# (F) the Hermite formula (eq:hermite) on random rational polynomials.
include(joinpath(@__DIR__, "common.jl"))

function part_F(rng=Xoshiro(SEED + 3))
    println("(F) the Hermite formula (eq:hermite)")
    good = true
    cases = 0
    for a in 1:3
        L = 2^a
        S = -L:L-1
        alpha = 2^(a + 1)
        for u in 1:a, h in (1, 2)
            q = [(t, qmult(v2(t), u, h)) for t in S if t != 0]
            total = sum(last, q)
            for _ in 1:3
                F = Q[big(rand(rng, -50:50)) // rand(rng, 1:9) for _ in 1:total]   # degree total-1
                rhs = Q(0)
                for (t, qt) in q
                    qt == 0 && continue
                    Et = Q[1]
                    for (qq, mult) in q
                        if qq != t && mult > 0
                            Et = pmul(Et, ppow(Q[big(-qq) // (t - qq), big(1) // (t - qq)], mult))
                        end
                    end
                    Ft = pcompose_lin(F, t, alpha)
                    Ett = pcompose_lin(Et, t, alpha)
                    quot = pmul(Ft[1:qt], series_inv(Ett, qt))[1:qt]
                    rhs += peval(Et, 0) * peval(quot, big(-t) // alpha)
                end
                good &= rhs == F[1]
                cases += 1
            end
        end
    end
    check("F(0) recovered exactly from truncated expansions ($cases random F, a <= 3)", good)
end

standalone(part_F, @__FILE__)
