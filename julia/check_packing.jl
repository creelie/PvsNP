# (G) the Packing lemma: properties (1) to (3) on random bipartite graphs.
include(joinpath(@__DIR__, "common.jl"))

"Random bipartite multigraph with M edges and maximum degree <= Delta."
function random_bipartite(rng, M, Delta)
    nr = nc = cdiv(M, Delta) + 2
    rows = [i for i in 1:nr for _ in 1:Delta]
    cols = [j for j in 1:nc for _ in 1:Delta]
    shuffle!(rng, rows); shuffle!(rng, cols)
    return collect(zip(rows[1:M], cols[1:M])), nr, nc
end

function part_G(rng=Xoshiro(SEED + 4))
    println("(G) Packing lemma")
    for (r, a, Delta, M) in ((2, 1, 4, 160), (3, 1, 4, 700), (2, 2, 8, 4200))
        N = r^a
        Darr = N * N
        L = 2^a
        @assert M >= 2 * Darr^2 * Delta && M >= L * Darr && 2L <= Delta
        edges, nr, nc = random_bipartite(rng, M, Delta)
        # label with code c (0 <= c < N) has coordinate k (1..a) equal to digit k of c in base r
        coord(c, k) = (c ÷ r^(k - 1)) % r
        ER = first.(edges); EC = last.(edges)
        incR = [Int[] for _ in 1:nr]; incC = [Int[] for _ in 1:nc]
        for (k, (x, y)) in enumerate(edges)
            push!(incR[x], k); push!(incC[y], k)
        end
        codeR = fill(-1, nr); codeC = fill(-1, nc)
        # Method of conditional expectations on E sum_gamma X_gamma^2, in units of 1/N^2:
        # a pair of endpoints contributes N if equal or equally labelled (0 if differently
        # labelled), and 1 if one of them is unlabelled.
        function factor(code, w, arr, e)
            arr[e] == w && return N
            (code[w] < 0 || code[arr[e]] < 0) && return 1
            return code[arr[e]] == code[w] ? N : 0
        end
        function cost(k)
            ex, ey = edges[k]
            c = 0
            for e in 1:M
                c += factor(codeR, ex, ER, e) * factor(codeC, ey, EC, e)
            end
            return c
        end
        for (code, inc, n) in ((codeR, incR, nr), (codeC, incC, nc)), idx in 1:n
            if isempty(inc[idx])
                code[idx] = 0
                continue
            end
            best = nothing
            for cand in 0:N-1
                code[idx] = cand
                cst = sum(cost(k) for k in inc[idx])
                if best === nothing || cst < best[1]
                    best = (cst, cand)
                end
            end
            code[idx] = best[2]
        end
        X = Dict{Tuple{Int,Int},Vector{Tuple{Int,Int}}}()
        for (x, y) in edges
            push!(get!(X, (codeR[x], codeC[y]), Tuple{Int,Int}[]), (x, y))
        end
        load = maximum(length, values(X))
        # load <= M/Darr + sqrt(2 M Delta), exactly
        excess = load * Darr - M
        check("r=$r a=$a: largest load $load <= M/Darr + sqrt(2 M Delta) (exact comparison)",
              excess <= 0 || excess^2 <= 2 * M * Delta * Darr^2)
        Hpad = cdiv(load, L) * L
        check("r=$r a=$a: H_pad = $Hpad <= 3M/Darr = $(3M // Darr)", Hpad * Darr <= 3M)
        # slots of each pair label: real edges then padding
        slots = Dict{Tuple{Int,Int},Vector{Union{Nothing,Tuple{Int,Int}}}}()
        for rl in 0:N-1, cl in 0:N-1
            lst = get(X, (rl, cl), Tuple{Int,Int}[])
            slots[(rl, cl)] = vcat(lst, fill(nothing, Hpad - length(lst)))
        end
        # groups by unordered pairs per coordinate
        keyof(rl, cl) = [minmax(coord(rl, k), coord(cl, k)) for k in 1:a]
        groups = Dict{Vector{Tuple{Int,Int}},Vector{Tuple{Int,Int}}}()
        for rl in 0:N-1, cl in 0:N-1
            push!(get!(groups, keyof(rl, cl), Tuple{Int,Int}[]), (rl, cl))
        end
        packets = []
        for (key, members) in groups
            unequal = [k for k in 1:a if key[k][1] != key[k][2]]
            ap = length(unequal)
            @assert length(members) == 2^ap
            per = 2^(a - ap)
            copy_bits = [k for k in 1:a if !(k in unequal)]
            for p in 0:(Hpad÷per)-1
                packet = Vector{Any}(nothing, L)
                for (rl, cl) in members, cpy in 0:per-1
                    pos = 0
                    for k in unequal
                        pos |= Int(coord(rl, k) > coord(cl, k)) << (k - 1)
                    end
                    for (kk, k) in enumerate(copy_bits)
                        pos |= ((cpy >> (kk - 1)) & 1) << (k - 1)
                    end
                    @assert packet[pos+1] === nothing
                    packet[pos+1] = ((rl, cl), slots[(rl, cl)][p*per+cpy+1])
                end
                @assert all(!isnothing, packet)
                push!(packets, (key, packet))
            end
        end
        ok1 = length(packets) * L <= 3M
        placed = [e for (_, pk) in packets for (_, e) in pk if e !== nothing]
        ok1 &= sort(placed) == sort(edges)
        ok2 = true
        for (key, pk) in packets, (pos1, (g, _)) in enumerate(pk)
            rl, cl = g
            for k in 1:a
                ok2 &= minmax(coord(rl, k), coord(cl, k)) == key[k]
                if coord(rl, k) != coord(cl, k)
                    ok2 &= (((pos1 - 1) >> (k - 1)) & 1) == Int(coord(rl, k) > coord(cl, k))
                end
            end
        end
        ok3 = true
        for k in 1:a, sym in 0:r-1
            nrow = count(e -> coord(codeR[e[1]], k) == sym, edges)
            ncol = count(e -> coord(codeC[e[2]], k) == sym, edges)
            ok3 &= nrow * r <= 3M && ncol * r <= 3M
        end
        check("r=$r a=$a: (1) $(length(packets)) packets <= 3M/L, every edge placed once", ok1)
        check("r=$r a=$a: (2) unordered pairs fixed, orientation in bit c", ok2)
        check("r=$r a=$a: (3) at most 3M/r ports per symbol and coordinate", ok3)
    end
end

standalone(part_G, @__FILE__)
