# (A) The network N(C) of the counting section: its contraction equals the number of
# satisfying inputs, for random circuits with every gate kind, big gates split in blocks.
include(joinpath(@__DIR__, "common.jl"))

struct Net
    ports::Vector{Vector{Int}}      # edge ids of each vertex
    tensors::Vector{Vector{Int}}    # entry at index sum bit_k 2^k (k = port position, 0-based)
    tags::Vector{Symbol}
    nedges::Int
end

function tensor_from(fn, n::Int)
    t = Vector{Int}(undef, 1 << n)
    for idx in 0:(1<<n)-1
        t[idx+1] = fn(idx)
    end
    return t
end
bit(idx, k) = (idx >> k) & 1
bits(idx, from, len) = (idx >> from) & ((1 << len) - 1)

"""Network of the counting section with block size K and weight bound 2^beta, after
subdivision.  Returns (net, stats)."""
function build_network(m::Int, gates::Vector{Gate}, out::Int, K::Int, beta::Int)
    b = beta + ceillog2(K) + 2
    shift = K * 2^beta
    occ = [Tuple{Int,Int}[] for _ in 1:m+length(gates)]   # (vertex, port position)
    vports = Vector{Vector{Int}}()
    vtens = Vector{Vector{Int}}()
    vtags = Symbol[]
    edges = Tuple{Int,Int,Int,Int}[]                       # (vertex, port, vertex, port)
    big_edges = 0
    function new_vertex(nports, tensor, tag)
        @assert length(tensor) == 1 << nports
        push!(vports, zeros(Int, nports)); push!(vtens, tensor); push!(vtags, tag)
        return length(vports)
    end
    for (j, g) in enumerate(gates)
        f = length(g.preds)
        sig = m + j
        if g.kind == :table || f <= K
            T = tensor_from(idx -> Int(bit(idx, f) == gate_value(g, [bit(idx, i) for i in 0:f-1])), f + 1)
            v = new_vertex(f + 1, T, :gate)
            for (pos, p) in enumerate(g.preds)
                push!(occ[p], (v, pos))
            end
            push!(occ[sig], (v, f + 1))
        else
            w = g.kind == :sym ? ones(Int, f) : g.w
            k = cdiv(f, K)
            root = tensor_from(k * b + 1) do idx
                v = 0
                for jj in 0:k-1
                    v += bits(idx, jj * b, b) - shift
                end
                Int(bit(idx, k * b) == phi_of(g, v))
            end
            r = new_vertex(k * b + 1, root, :root)
            for jj in 0:k-1
                I = (jj*K+1):min(f, (jj + 1) * K)
                nI = length(I)
                Tb = tensor_from(nI + b) do idx
                    P = 0
                    for (q, i) in enumerate(I)
                        P += w[i] * bit(idx, q - 1)
                    end
                    Int(bits(idx, nI, b) == P + shift)
                end
                bv = new_vertex(nI + b, Tb, :block)
                for (q, i) in enumerate(I)
                    push!(occ[g.preds[i]], (bv, q))
                end
                for t in 1:b
                    push!(edges, (bv, nI + t, r, jj * b + t))
                    big_edges += 1
                end
            end
            push!(occ[sig], (r, k * b + 1))
        end
    end
    pin = new_vertex(1, [0, 1], :pin)                      # pin on the output
    push!(occ[out], (pin, 1))
    E2 = [1, 0, 0, 1]
    E3 = tensor_from(idx -> Int(idx == 0 || idx == 7), 3)
    for ports in occ                                       # equality trees
        d = length(ports)
        if d == 0
            continue
        elseif d == 1
            u = new_vertex(1, [1, 1], :eq)
            push!(edges, (u, 1, ports[1]...))
        elseif d == 2
            u = new_vertex(2, E2, :eq)
            push!(edges, (u, 1, ports[1]...))
            push!(edges, (u, 2, ports[2]...))
        else
            cs = [new_vertex(3, E3, :eq) for _ in 1:d-2]   # caterpillar c_1..c_{d-2}
            push!(edges, (cs[1], 1, ports[1]...))
            push!(edges, (cs[1], 2, ports[2]...))
            for i in 2:d-2
                push!(edges, (cs[i], 1, cs[i-1], 3))
                push!(edges, (cs[i], 2, ports[i+1]...))
            end
            push!(edges, (cs[end], 3, ports[end]...))
        end
    end
    edges_before = length(edges)
    ne = 0
    for (a, pa, c, pc) in edges                            # subdivision
        @assert vports[a][pa] == 0 && vports[c][pc] == 0
        vports[a][pa] = ne + 1
        vports[c][pc] = ne + 2
        push!(vports, [ne + 1, ne + 2]); push!(vtens, E2); push!(vtags, :sub)
        ne += 2
    end
    @assert all(all(>(0), p) for p in vports)
    net = Net(vports, vtens, vtags, ne)
    stats = (edges_before=edges_before, edges=ne, big_edges=big_edges,
             maxdeg=maximum(length.(vports)), b=b, nvert=length(vports))
    return net, stats
end

function contract_pair(pi, Ti, pj, Tj)
    shared = [e for e in pi if e in pj]
    po = vcat([e for e in pi if !(e in shared)], [e for e in pj if !(e in shared)])
    no, ns = length(po), length(shared)
    no + ns <= 30 || error("intermediate tensor too large")
    pos = Dict{Int,Int}()
    for (k, e) in enumerate(po); pos[e] = k - 1; end
    for (k, e) in enumerate(shared); pos[e] = no + k - 1; end
    mi = [pos[e] for e in pi]
    mj = [pos[e] for e in pj]
    T = zeros(Int, 1 << no)
    mask = (1 << no) - 1
    for c in 0:(1<<(no+ns))-1
        ii = 0
        for (k, q) in enumerate(mi); ii |= ((c >> q) & 1) << (k - 1); end
        a = Ti[ii+1]
        a == 0 && continue
        jj = 0
        for (k, q) in enumerate(mj); jj |= ((c >> q) & 1) << (k - 1); end
        T[(c&mask)+1] += a * Tj[jj+1]
    end
    return po, T
end

"Exact contraction by greedy pairwise elimination (Int entries; values are at most 2^m)."
function contract(net::Net)
    ts = [(copy(net.ports[i]), net.tensors[i]) for i in eachindex(net.ports)]
    while length(ts) > 1
        where = Dict{Int,Vector{Int}}()
        for (i, (p, _)) in enumerate(ts), e in p
            push!(get!(where, e, Int[]), i)
        end
        best = nothing
        for (e, l) in where
            (length(l) == 2 && l[1] != l[2]) || continue
            i, j = l
            sh = count(in(ts[j][1]), ts[i][1])
            size = length(ts[i][1]) + length(ts[j][1]) - 2 * sh
            if best === nothing || (size, i, j) < best
                best = (size, i, j)
            end
        end
        i, j = best === nothing ? (1, 2) : (best[2], best[3])   # components: multiply scalars
        po, T = contract_pair(ts[i][1], ts[i][2], ts[j][1], ts[j][2])
        deleteat!(ts, sort([i, j]))
        push!(ts, (po, T))
    end
    @assert isempty(ts[1][1])
    return ts[1][2][1]
end

function part_A(rng=Xoshiro(SEED))
    println("(A) contraction of N(C) against exhaustive counting")
    trials = 0
    kinds_big = Set{Symbol}()
    for trial in 1:120
        m = rand(rng, 1:6)
        gates, out = random_circuit(rng, m, rand(rng, 1:5), 3, 1, 7)
        m2, g2, out2, u = normalise(m, gates, out)
        K, beta = 2, 1
        net, st = build_network(m2, g2, out2, K, beta)
        st.maxdeg > 20 && continue
        for g in g2
            g.kind != :table && length(g.preds) > K && push!(kinds_big, g.kind)
        end
        Z = contract(net) * 2^u
        cnt = brute_count(m, gates, out)
        trials += 1
        if Z != cnt
            check("contraction trial $trial", false, "Z=$Z count=$cnt")
            return
        end
    end
    check("contraction equals #C on $trials random circuits", true,
          "(big gates of kinds $(join(sort(string.(collect(kinds_big))), ",")) split into blocks)")
    check("all four weighted kinds occurred as big gates", issubset([:thr, :exact, :mod, :sym], kinds_big))
end

standalone(part_A, @__FILE__)
