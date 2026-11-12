# (I) Theorem on tree encodings: the gate I_G, the rank lemma, the cube.

# Gate I_G for a graph with vertices 1..nv and edge list E; inputs (x_1..x_nv, y_1..y_k)
function IG_constraints(nv, E, bits)
    all(bits[a] + bits[b] + bits[nv+j] == 1 for (j,(a,b)) in enumerate(E))
end
function IG_weighted(nv, E, bits)
    k = length(E)
    w = zeros(BigInt, nv + k)
    for (j,(a,b)) in enumerate(E)
        w[a] += big(4)^(j-1); w[b] += big(4)^(j-1); w[nv+j] = big(4)^(j-1)
    end
    θ = sum(big(4)^(j-1) for j in 1:k)
    sum(w[i]*bits[i] for i in eachindex(bits)) == θ
end
function cube(k)
    E = Tuple{Int,Int}[]
    for v in 0:2^k-1, i in 0:k-1
        u = v ⊻ (1 << i)
        v < u && push!(E, (v+1, u+1))
    end
    E
end
# rank over Q of the matrix of I_G for the partition (A, complement)
function rankA(nv, E, A)
    f = nv + length(E); B = setdiff(1:f, A)
    Mx = zeros(Rational{BigInt}, 2^length(A), 2^length(B))
    bits = zeros(Int, f)
    for r in 0:2^length(A)-1, c in 0:2^length(B)-1
        for (t,i) in enumerate(A); bits[i] = (r >> (t-1)) & 1; end
        for (t,i) in enumerate(B); bits[i] = (c >> (t-1)) & 1; end
        Mx[r+1,c+1] = IG_constraints(nv, E, bits) ? 1 : 0
    end
    rank_rational(Mx)
end
function rank_rational(M)
    M = copy(M); m, n = size(M); r = 0
    for c in 1:n
        p = findfirst(i -> M[i,c] != 0, r+1:m)
        p === nothing && continue
        p += r; r += 1
        M[[r,p],:] = M[[p,r],:]
        for i in 1:m
            i != r && M[i,c] != 0 && (M[i,:] -= (M[i,c]/M[r,c]) * M[r,:])
        end
        r == m && break
    end
    r
end
# split edges and a greedy induced matching of split edges
function greedy_induced_split(nv, E, A)
    inA = falses(nv + length(E)); inA[A] .= true
    split = [j for (j,(a,b)) in enumerate(E) if !(inA[a] == inA[b] == inA[nv+j])]
    nbr = [Int[] for _ in 1:nv]
    for (a,b) in E; push!(nbr[a], b); push!(nbr[b], a); end
    blocked = falses(nv); M = Int[]
    for j in split
        a, b = E[j]
        (blocked[a] || blocked[b]) && continue
        push!(M, j)
        for v in (a, b, nbr[a]..., nbr[b]...); blocked[v] = true; end
    end
    length(split), M
end

function part_I()
    println("(I) tree encodings of weighted gates")
    # I1 base-four identity, exhaustive for Q2 (f = 8) and Q3 (f = 20)
    ok = true
    for k in (2, 3)
        E = cube(k); nv = 2^k; f = nv + length(E)
        bits = zeros(Int, f)
        for z in 0:2^f-1
            for i in 1:f; bits[i] = (z >> (i-1)) & 1; end
            ok &= IG_constraints(nv, E, bits) == IG_weighted(nv, E, bits)
        end
    end
    check("I1 I_G equals its exact-gate form on all inputs, G = Q2, Q3", ok)
    # I2 rank lemma: rank >= 2^|M| for every A of Q2 (2^8 partitions) and 400 random A of Q3 with |A| <= 10
    ok = true; cnt = 0
    E2 = cube(2)
    for z in 1:2^8-2
        A = [i for i in 1:8 if (z >> (i-1)) & 1 == 1]
        _, M = greedy_induced_split(4, E2, A)
        ok &= rankA(4, E2, A) >= 2^length(M); cnt += 1
    end
    E3 = cube(3); rng = MersenneTwister(7)
    for t in 1:400
        A = sort(randperm(rng, 20)[1:rand(rng, 1:10)])
        _, M = greedy_induced_split(8, E3, A)
        ok &= rankA(8, E3, A) >= 2^length(M); cnt += 1
    end
    check("I2 rank_A(I_G) >= 2^|M| on $cnt partitions of Q2, Q3", ok)
    # I3 split-edge and matching counts of the lemma, every A with |A| <= f/2 for Q3 (sampled 20000) and Q4 (sampled 5000)
    ok = true
    for (k, trials) in ((3, 20000), (4, 5000))
        E = cube(k); nv = 2^k; f = nv + length(E); d = k; c1 = min(1//4, 1//(d+1))
        for t in 1:trials
            A = randperm(rng, f)[1:rand(rng, 1:f÷2)]
            ns, M = greedy_induced_split(nv, E, A)
            ok &= ns >= c1*length(A) && length(M) >= c1*length(A)/(2d^2)
        end
    end
    check("I3 split edges >= c1|A| and induced matching >= c1|A|/(2d^2), Q3 and Q4 (25000 sets)", ok)
    # I4 edge-isoperimetric inequality e(S) <= |S| log2|S| / 2, all S in Q4
    E = cube(4); ok = true
    for z in 1:2^16-1
        inS(v) = (z >> (v-1)) & 1 == 1
        s = count_ones(z); e = count(((a,b),) -> inS(a) && inS(b), E)
        ok &= 2e <= s*log2(s) + 1e-9
    end
    check("I4 e(S) <= |S| log|S| / 2 for all 65535 nonempty S in Q4", ok)
    # I5 arithmetic of the theorem: 2k^2(k+1) <= 4k^3, k <= log2 f_k, 2|E| < 2 f_k, f_k <= 3 f_(k-1)
    ok = all(2k^2*(k+1) <= 4k^3 && 2^k <= big(2)^(k-1)*(k+2) && k*big(2)^k < 2*big(2)^(k-1)*(k+2) &&
             big(2)^(k-1)*(k+2) <= 3*big(2)^(k-2)*(k+1) for k in 2:2000)
    check("I5 constants of the tree theorem, 2 <= k <= 2000", ok)
end
