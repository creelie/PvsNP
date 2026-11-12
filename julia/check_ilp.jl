# (C) Theorem C: the circuit of a zero-one program counts its feasible points, and
# binary search with self-reduction finds the optimum.
include(joinpath(@__DIR__, "common.jl"))

"Circuit of Theorem C: rows as thresholds, conjunction as an exact gate."
function ilp_circuit(A::Vector{Vector{Int}}, b::Vector{Int}, n::Int, extra=nothing)
    gates = Gate[]
    for (row, bj) in zip(A, b)
        supp = [k for k in 1:n if row[k] != 0]
        push!(gates, thr_gate(supp, [-row[k] for k in supp], -bj))      # row.x <= b_j
    end
    if extra !== nothing
        c, t = extra
        push!(gates, thr_gate(collect(1:n), copy(c), t))               # c.x >= t
    end
    r = length(gates)
    push!(gates, exact_gate([n + j for j in 1:r], ones(Int, r), r))
    return n, gates, n + r + 1
end

function part_C(rng=Xoshiro(SEED + 2))
    println("(C) Theorem C: zero-one programs")
    good = true
    for trial in 1:60
        n, r = rand(rng, 1:8), rand(rng, 1:5)
        A = [[rand(rng, (0, 0, rand(rng, -6:6))) for _ in 1:n] for _ in 1:r]
        A = [row for row in A if any(!=(0), row)]
        isempty(A) && (A = [ones(Int, n)])
        b = [rand(rng, -4:8) for _ in A]
        c = [rand(rng, -5:5) for _ in 1:n]
        xs = [[(x >> (i - 1)) & 1 for i in 1:n] for x in 0:(1<<n)-1]
        pts = [x for x in xs if all(sum(row .* x) <= bj for (row, bj) in zip(A, b))]
        good &= brute_count(ilp_circuit(A, b, n)...) == length(pts)
        isempty(pts) && continue
        bound = n * max(1, maximum(abs, c))
        lo, hi = -bound, bound                         # max c.x lies in [lo, hi]
        while lo < hi
            mid = fld(lo + hi + 1, 2)
            if brute_count(ilp_circuit(A, b, n, (c, mid))...) > 0
                lo = mid
            else
                hi = mid - 1
            end
        end
        tmax = lo
        good &= tmax == maximum(sum(c .* x) for x in pts)
        # self-reduction: fix x_1, x_2, ... keeping the count positive
        xfix = Int[]
        Acur, bcur, ccur, off = deepcopy(A), copy(b), copy(c), 0
        for k in 1:n
            for val in (0, 1)
                A2 = [row[2:end] for row in Acur]
                b2 = [bj - row[1] * val for (row, bj) in zip(Acur, bcur)]
                c2 = ccur[2:end]
                off2 = off + ccur[1] * val
                nrem = n - k
                feasible = nrem == 0 ? (all(>=(0), b2) && off2 >= tmax) :
                           brute_count(ilp_circuit(A2, b2, nrem, (c2, tmax - off2))...) > 0
                if feasible
                    push!(xfix, val)
                    Acur, bcur, ccur, off = A2, b2, c2, off2
                    break
                end
            end
        end
        good &= length(xfix) == n && (xfix in pts) && sum(c .* xfix) == tmax
    end
    check("feasible counts, binary search and self-reduction on 60 random programs", good)
end

standalone(part_C, @__FILE__)
