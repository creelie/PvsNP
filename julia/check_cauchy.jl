# (E) Integrality lemma of the Cauchy deformation W(t + alpha z).
include(joinpath(@__DIR__, "common.jl"))

function part_E()
    println("(E) Integrality lemma of W(t + alpha z)")
    good = good0 = true
    cases = 0
    for a in 1:4
        L = 2^a
        S = -L:L-1
        alpha = 2^(a + 1)
        Cp0 = prod(big(-q) for q in S if q != 0)
        for d in -(L - 1):(L-1)                    # d = y - x for slots x, y in [0, L)
            Wp = Q[1]                              # W(T) = prod_{q != d} (T - q) / C'(0)
            for q in S
                q != d && (Wp = pmul(Wp, Q[-q, 1]))
            end
            Wp = Wp .// Cp0
            good0 &= peval(Wp, 0) == (d == 0 ? 1 : 0)
            for t in S
                comp = pcompose_lin(Wp, t, alpha)
                good &= all(c == 0 || v2(c) >= 0 for c in comp)
                cases += 1
            end
        end
    end
    check("W(0) is the identity for a <= 4", good0)
    check("every coefficient of W_xy(t + alpha z) is 2-integral ($cases cases, a <= 4)", good)
end

standalone(part_E, @__FILE__)
