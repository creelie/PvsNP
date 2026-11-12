# Part H: constants of the parametrised contraction theorem (Theorem G),
# Corollaries D.1(delta) and G', the size lemma for general delta, and the
# transfer condition delta_1 < delta_2.  Exact integer/rational arithmetic,
# except where pi, sqrt or ln occur; those use 512-bit BigFloat with a margin.
include(joinpath(@__DIR__, "common.jl"))

setprecision(BigFloat, 512)

"Smallest integer U0 with U0 >= (C^(1/3) (17 + 2 log2 C))^(6/5)."
U0(C) = ceil(Int, (BigFloat(C)^(1//3) * (17 + 2*log2(BigFloat(C))))^(6//5))

function part_H()
    # H1  U0(1) = 30, U0(22) = 172
    check("H1 U0(1)=30 and U0(22)=172", U0(1) == 30 && U0(22) == 172)
    # H2  2 sqrt(U) <= 2^(4U) for U >= 1   (4 U >= 1 + log2(U)/2; squared: 4U <= 2^(8U))
    check("H2 2*sqrt(U) <= 2^(4U), 1<=U<=10^4", all(4*big(U) <= big(2)^(8U) for U in 1:10_000))
    # H3  4a(a+1) <= 2^(a/2+1) for even a >= 20 (a_d is even)
    check("H3 4a(a+1) <= 2^(a/2+1), even 20<=a<=10^4", all(4*big(a)*(a+1) <= big(2)^(a÷2+1) for a in 20:2:10_000))
    # H4  47 C^(6/5) (u+1)^(8/5) <= 2^(u+1) for u >= 16 + 2 log2 C, C = 2^(k/4)
    ok = true
    for k in 0:4000, j in 0:3
        C = BigFloat(2)^(k//4); u = ceil(Int, 16 + 2*log2(C)) + j
        ok &= log2(BigFloat(47)) + (6//5)*log2(C) + (8//5)*log2(BigFloat(u+1)) <= u + 1
    end
    ok &= all(log2(BigFloat(47)) + (8//5)*log2(BigFloat(u+1)) <= u + 1 for u in 16:20_000)
    check("H4 47 C^(6/5)(u+1)^(8/5) <= 2^(u+1), u >= 16+2log2C", ok)
    # H5  (1+pi^2) sqrt(34) < 64
    check("H5 (1+pi^2)*sqrt(34) < 64", (1 + BigFloat(pi)^2)*sqrt(BigFloat(34)) < 64 - big"0.1")
    # H6  64 sqrt(17/16)/(1 - sqrt2/8) < 81
    check("H6 64*sqrt(17/16)/(1-sqrt(2)/8) < 81", 64*sqrt(BigFloat(17)/16)/(1 - sqrt(BigFloat(2))/8) < 81 - big"0.5")
    # H7  81/ln 2 < 117
    check("H7 81/ln(2) < 117", 81/log(BigFloat(2)) < 117 - big"0.1")
    # H8  1 + 40*8/7 <= 47 and 6/64 < 1/8 and sum j^2/2^j = 6 (exact, finite tail bound)
    tail = sum(big(j)^2 // big(2)^j for j in 1:400)
    check("H8 1+320/7<=47, 6/64<1/8, sum j^2/2^j = 6", 1 + 320//7 <= 47 && 6//64 < 1//8 && 6 - tail < big(1)//big(10)^100)
    # H9  16(117C+4) = 1872C+64 and (117C+4) sqrt(104) < 1194C+41 for C >= 1
    ok = all(16*(117*C + 4) == 1872*C + 64 for C in 1:1000)
    ok &= all((117*C + 4)^2*104 < (1194*C + 41)^2 for C in 1:100_000)   # both sides positive
    check("H9 16(117C+4)=1872C+64, (117C+4)sqrt(104)<1194C+41", ok)
    # H10 (1872*22+65) sqrt(3) < 71500 and 71500 sqrt(2) < 101200 and 4/(5e6) < 1/(12*101200)
    ok = (1872*22 + 65)^2*3 < 71500^2 && 71500^2*2 < 101200^2 && 4*12*101200 < 5_000_000
    check("H10 counting and lower-bound constants", ok)
    # H11 Corollary D.1(delta): (G1)-(G3) for eps = delta/128, log s >= 128(U0(C)+1)/delta,
    #     delta in {1/100,...,50/100}, C in {1, 22}; logs computed exactly with lambda = ceil(log s)
    ok = true
    for C in (1, 22), p in 1:50
        δ = p//100
        for mult in (1, 2, 5, 40)
            ls = ceil(Int, 128*(U0(C) + 1)/δ)*mult          # log2 s (s a power of two)
            λ = ls; U = floor(Int, δ*λ/128)
            logΔ_up = (1 - δ)*ls + 1                        # Delta <= 2 s^(1-delta)
            ok &= U >= U0(C)                                  # (G1)
            ok &= 100U + logΔ_up <= ls                        # (G2)
            ok &= 4U + 1 <= (1 - δ)*ls                        # (G3), Delta >= s^(1-delta)
            ok &= U >= δ*ls/256                               # used for the exponent
        end
    end
    check("H11 (G1)-(G3) for Corollary D.1(delta)", ok)
    # H12 Size lemma, general delta: for s = 2^x, x a multiple of 6q, x >= 40/delta:
    #     beta' <= K and every degree <= 3 s^(1-delta/2) <= s^(1-delta/3)  (exact)
    ok = true
    for δ in (1//20, 1//10, 1//5, 1//4, 1//3, 1//2)
        q = denominator(δ); step = 6q
        x0 = step*cld(ceil(Int, 40/δ), step)
        for x in x0:step:x0 + 40step
            s = big(2)^x
            K = big(2)^Int(x*(1 - δ/2)); β = big(2)^Int(x*(1 - δ))
            βp = β + ndigits(K - 1, base=2) + 2               # ceil(log2 K) + 2 for K a power of two
            k = cld(s, K)
            degs = (β + 1, K + 1, K + βp, k*βp + 1)
            ok &= βp <= K
            ok &= all(3*big(2)^Int(x*(1 - δ/2)) >= d for d in degs)
            ok &= 3*big(2)^Int(x*(1 - δ/2)) <= big(2)^Int(x*(1 - δ/3))
        end
    end
    check("H12 size lemma degrees for general delta", ok)
    # H13 transfer membership: (dn)^(1-delta2) <= n^(1-delta1) for delta1 = delta/2, delta2 = delta,
    #     d = 2, i.e. d^(2(q-p)) <= n^p with delta = p/q; check the threshold n0 = d^(2(1-delta)/delta)
    ok = true
    for δ in (1//20, 1//10, 1//5, 1//4, 1//2)
        p, q = numerator(δ), denominator(δ)
        n0 = ceil(BigInt, BigFloat(2)^(2*(1 - δ)/δ))
        ok &= all(big(2)^(2*(q - p)) <= big(n)^p for n in n0:n0 + 2000)
        ok &= big(2)^(2*(q - p)) > big(n0 - 1)^p
    end
    check("H13 transfer membership threshold, delta1 = delta/2", ok)
end

standalone(part_H, @__FILE__)
