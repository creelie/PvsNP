# (B) The Size lemma: occurrence count, equality-tree and block edges, and the bound 22s
# on random circuits with big weighted gates split into blocks.
include(joinpath(@__DIR__, "common.jl"))

function part_B(rng=Xoshiro(SEED + 1))
    println("(B) the Size lemma: edges and degrees")
    worst = 0 // 1
    nets = withbig = 0
    for trial in 0:199
        m = rand(rng, 2:40)
        G = rand(rng, 1:60)
        if isodd(trial)
            gates, out = random_circuit(rng, m, G, 2, 1, 60)
        else   # many small gates and a few big weighted gates of large fan-in
            gates, _ = random_circuit(rng, m, rand(rng, 100:400), 2, 1, 2)
            for _ in 1:rand(rng, 1:3)
                f = rand(rng, 200:700)
                nsig = m + length(gates)
                kind = rand(rng, (:thr, :exact, :mod))
                preds = [rand(rng, 1:nsig) for _ in 1:f]
                push!(gates, kind == :mod ? mod_gate(preds, ones(Int, f), f ÷ 3, 3) :
                             Gate(kind, preds, Int[], ones(Int, f), f ÷ 3, 0))
            end
            nsig = m + length(gates)
            push!(gates, exact_gate(collect(nsig-2:nsig), [1, 1, 1], 3))
            out = m + length(gates)
        end
        m2, g2, out2, u = normalise(m, gates, out)
        W = sum(length(g.preds) for g in g2; init=0)
        s = m2 + W
        s < 2 && continue
        K, beta = ifloorpow(s, 4, 5), ifloorpow(s, 2, 3)
        b = beta + ceillog2(K) + 2
        dsig = zeros(Int, m2 + length(g2))
        big_edges = 0
        for (j, g) in enumerate(g2)          # count edges without building tensors
            f = length(g.preds)
            dsig[m2+j] += 1
            for p in g.preds
                dsig[p] += 1
            end
            if !(g.kind == :table || f <= K)
                big_edges += cdiv(f, K) * b
            end
        end
        dsig[out2] += 1
        tree = sum(d <= 2 ? d : 2d - 3 for d in dsig)
        before = tree + big_edges
        G2 = length(g2)
        ok = sum(dsig) == G2 + W + 1 && tree <= 2 * (G2 + W + 1) && G2 <= W + 2
        if b <= K
            ok = ok && big_edges <= 2W && before <= 6W + 6 && 2 * before <= 22s
            withbig += big_edges > 0
            worst = max(worst, 2 * before // s)
        end
        nets += 1
        if !ok
            check("size trial $trial", false)
            return
        end
    end
    check("occurrences sum to G+W+1, trees <= 2 sum d, edges <= 22s on $nets circuits", true,
          "($withbig with b <= K and a big gate; largest edges/s = $(round(Float64(worst), digits=2)))")
    check("at least 50 circuits with b <= K have a big gate", withbig >= 50)

end

standalone(part_B, @__FILE__)
