# (D) identity (eq:vEt), the bound v2(E_t(0)) >= -6Dh, and v2(C'(t)) = v2(C'(0)).
include(joinpath(@__DIR__, "common.jl"))

function part_D()
    println("(D) identity (eq:vEt) and v2(E_t(0)) >= -6Dh")
    good_id = good_bd = good_c = true
    cases = 0
    for a in 1:7
        L = 2^a
        S = -L:L-1
        Cp(t) = prod(big(t - q) for q in S if q != t)
        v0 = v2(Cp(0))
        good_c &= all(v2(Cp(t)) == v0 for t in S)
        for u in 1:a, h in (1, 2, 3, 5), t in S
            t == 0 && continue
            i = v2(t)
            qmult(i, u, h) == 0 && continue
            D = L ÷ 2^i
            direct = sum(qmult(v2(q), u, h) * (v2(q) - v2(t - q)) for q in S if q != 0 && q != t)
            formula = D * sum((j // big(2)^j) * (qmult(i + j, u, h) - qmult(i, u, h)) for j in 1:a-i; init=0 // big(1))
            good_id &= direct == formula
            good_bd &= direct >= -6 * D * h
            cases += 1
        end
    end
    check("v2(C'(t)) = v2(C'(0)) for all t in S, a <= 7", good_c)
    check("(eq:vEt) holds in $cases cases (a <= 7, all u, h in {1,2,3,5})", good_id)
    check("v2(E_t(0)) >= -6Dh in the same cases", good_bd)
end

standalone(part_D, @__FILE__)
