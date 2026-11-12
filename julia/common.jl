# Shared helpers for the checks of the finite statements of
# "Superlinear Wire Lower Bounds for Gates of Fan-In N^(1-delta)".
# Standard library only; all arithmetic is exact (Int, Int128, BigInt, Rational{BigInt}).
if !isdefined(Main, :PVSNP_COMMON)
const PVSNP_COMMON = true

using Random

const SEED = 20261104
const COUNTS = Dict(:pass => 0, :fail => 0)

function check(name::AbstractString, ok::Bool, info::AbstractString="")
    COUNTS[ok ? :pass : :fail] += 1
    println((ok ? "PASS " : "FAIL ") * name * (isempty(info) ? "" : " " * info))
    flush(stdout)
    return ok
end

summary_line() = println("$(COUNTS[:pass]) checks passed, $(COUNTS[:fail]) failed")

"Run `f` as a stand-alone program when `file` is the script being executed."
function standalone(f, file)
    if abspath(PROGRAM_FILE) == abspath(file)
        t = @elapsed f()
        summary_line()
        println("runtime: ", round(t, digits=2), " s")
        exit(COUNTS[:fail] == 0 ? 0 : 1)
    end
end

# ---------------------------------------------------------------- exact arithmetic
"Two-adic valuation of a nonzero integer or rational."
function v2(x::Integer)
    @assert x != 0
    return trailing_zeros(x)
end
v2(x::Rational) = v2(numerator(x)) - v2(denominator(x))

"floor(s^(p/q)) for integers s >= 0, p >= 0, q >= 1: the largest r with r^q <= s^p."
function ifloorpow(s::Integer, p::Integer, q::Integer)
    t = big(s)^p
    r = BigInt(floor(BigInt, big(float(s))^(p / q)))      # guess, then corrected exactly
    while r^q > t
        r -= 1
    end
    while (r + 1)^q <= t
        r += 1
    end
    return Int(r)
end

"ceil(s^(p/q)): the least r with r^q >= s^p."
function iceilpow(s::Integer, p::Integer, q::Integer)
    r = ifloorpow(s, p, q)
    return big(r)^q == big(s)^p ? r : r + 1
end

"ceil(log2 K) for K >= 1."
ceillog2(K::Integer) = K <= 1 ? 0 : ndigits(K - 1, base=2)

cdiv(a::Integer, b::Integer) = -fld(-a, b)

# ---------------------------------------------------------------- circuits of K(F, beta)
# kinds: :table (table = 2^f bits, index sum y_i 2^(i-1)), :thr [v >= theta],
# :exact [v == theta], :mod [v == theta mod mu], :sym (table = f+1 bits, phi(sum y_i)).
# Signals: inputs 1..m, gate j is signal m+j.
struct Gate
    kind::Symbol
    preds::Vector{Int}
    table::Vector{Int}
    w::Vector{Int}
    theta::Int
    mu::Int
end
table_gate(preds, table) = Gate(:table, preds, table, Int[], 0, 0)
sym_gate(preds, table) = Gate(:sym, preds, table, Int[], 0, 0)
thr_gate(preds, w, theta) = Gate(:thr, preds, Int[], w, theta, 0)
exact_gate(preds, w, theta) = Gate(:exact, preds, Int[], w, theta, 0)
mod_gate(preds, w, theta, mu) = Gate(:mod, preds, Int[], w, theta, mu)

"phi applied to the weighted sum v (for :sym, out-of-range sums give 0)."
function phi_of(g::Gate, v::Int)
    f = length(g.preds)
    g.kind == :sym && return (0 <= v <= f) ? g.table[v+1] : 0
    g.kind == :thr && return Int(v >= g.theta)
    g.kind == :exact && return Int(v == g.theta)
    g.kind == :mod && return Int(mod(v - g.theta, g.mu) == 0)
    error("kind")
end

function gate_value(g::Gate, y::AbstractVector{Int})
    if g.kind == :table
        idx = 0
        for (i, b) in enumerate(y)
            idx |= b << (i - 1)
        end
        return g.table[idx+1]
    elseif g.kind == :sym
        return g.table[sum(y)+1]
    end
    v = 0
    for i in eachindex(y)
        v += g.w[i] * y[i]
    end
    return phi_of(g, v)
end

function evaluate(m::Int, gates::Vector{Gate}, out::Int, x::Int)
    val = Vector{Int}(undef, m + length(gates))
    for i in 1:m
        val[i] = (x >> (i - 1)) & 1
    end
    for (j, g) in enumerate(gates)
        val[m+j] = gate_value(g, val[g.preds])
    end
    return val[out]
end

brute_count(m, gates, out) = sum(evaluate(m, gates, out, x) for x in 0:(1<<m)-1)

function random_circuit(rng, m, G, F, beta, maxfan)
    gates = Gate[]
    for j in 0:G-1
        nsig = m + j
        kind = rand(rng, (:table, :thr, :exact, :mod, :sym))
        f = kind == :table ? rand(rng, 0:min(F, nsig)) : rand(rng, 1:min(maxfan, nsig + 3))
        preds = [rand(rng, 1:nsig) for _ in 1:f]            # repetitions allowed
        if kind == :table
            push!(gates, table_gate(preds, [rand(rng, 0:1) for _ in 1:2^f]))
        elseif kind == :sym
            push!(gates, sym_gate(preds, [rand(rng, 0:1) for _ in 1:f+1]))
        else
            w = [rand(rng, -2^beta:2^beta) for _ in 1:f]
            h = fld(f * 2^beta, 2)
            theta = rand(rng, -h:h)
            if kind == :mod
                push!(gates, mod_gate(preds, w, theta, rand(rng, 1:2^beta)))
            elseif kind == :thr
                push!(gates, thr_gate(preds, w, theta))
            else
                push!(gates, exact_gate(preds, w, theta))
            end
        end
    end
    return gates, m + G
end

"""Delete gates that do not reach the output; drop unused inputs.
Returns (m', gates', out', u) with #C = 2^u #C'."""
function normalise(m::Int, gates::Vector{Gate}, out::Int)
    n = m + length(gates)
    reach = falses(n)
    reach[out] = true
    for j in length(gates):-1:1
        if reach[m+j]
            for p in gates[j].preds
                reach[p] = true
            end
        end
    end
    used = [i for i in 1:m if reach[i]]
    u = m - length(used)
    newid = Dict{Int,Int}(i => k for (k, i) in enumerate(used))
    ng = Gate[]
    for (j, g) in enumerate(gates)
        if reach[m+j]
            newid[m+j] = length(used) + length(ng) + 1
            push!(ng, Gate(g.kind, [newid[p] for p in g.preds], g.table, g.w, g.theta, g.mu))
        end
    end
    return length(used), ng, newid[out], u
end

# ---------------------------------------------------------------- polynomials over Q
const Q = Rational{BigInt}
const Poly = Vector{Q}                      # low degree first

function pmul(p::Poly, q::Poly)
    r = zeros(Q, length(p) + length(q) - 1)
    for (i, a) in enumerate(p)
        a == 0 && continue
        for (j, b) in enumerate(q)
            r[i+j-1] += a * b
        end
    end
    return r
end

function ppow(p::Poly, k::Int)
    r = Q[1]
    for _ in 1:k
        r = pmul(r, p)
    end
    return r
end

function peval(p::Poly, x)
    r = Q(0)
    for c in Iterators.reverse(p)
        r = r * x + c
    end
    return r
end

"p(t + alpha z) as a polynomial in z."
function pcompose_lin(p::Poly, t, alpha)
    r = Q[0]
    for c in Iterators.reverse(p)
        r = pmul(r, Q[t, alpha])
        r[1] += c
    end
    return r
end

"Inverse of a power series with p[1] != 0, modulo z^n."
function series_inv(p::Poly, n::Int)
    inv = zeros(Q, n)
    inv[1] = 1 // p[1]
    for k in 1:n-1
        s = Q(0)
        for j in 1:min(k, length(p) - 1)
            s += p[j+1] * inv[k-j+1]
        end
        inv[k+1] = -s / p[1]
    end
    return inv
end

"Multiplicity q_t = h max(0, u - v2(t)) of the tapered Hermite scheme."
qmult(i, u, h) = h * max(0, u - i)

end # PVSNP_COMMON
