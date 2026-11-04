"""Checks of the finite statements of the paper
"Superlinear Wire Lower Bounds toward P versus NP".

Run:  python3 check_encoding.py            (about a minute)

Each part prints one line per check and the script ends with
"N checks passed, 0 failed".  All arithmetic is exact (Python integers and
fractions); numpy is used only to contract tensors with integer entries.

  (A) network N(C) of the counting section: contraction equals the number of satisfying
      inputs, for random circuits with every gate kind, big gates in blocks;
  (B) the Size lemma: edge count against the formula and the bound 22s, and the
      degree bound ceil(s^(9/10)) as a function of s;
  (C) Theorem C: the circuit of a zero-one program counts its feasible
      points, and binary search with self-reduction finds the optimum;
  (D) identity (eq:vEt), the bound v2(E_t(0)) >= -6Dh, and v2(C'(t)) = v2(C'(0));
  (E) the Integrality lemma of the Cauchy deformation W;
  (F) the Hermite formula (eq:hermite) on random rational polynomials;
  (G) the Packing lemma: properties (1) to (3) on random bipartite graphs.
"""
import itertools
import math
import random
import sys
from fractions import Fraction

import numpy as np

PASS = FAIL = 0


def check(name, ok, info=''):
    global PASS, FAIL
    if ok:
        PASS += 1
    else:
        FAIL += 1
    print(('PASS ' if ok else 'FAIL ') + name + ((' ' + info) if info else ''))


def v2(x):
    """Two-adic valuation of a nonzero rational."""
    x = Fraction(x)
    assert x != 0
    n, d, k = x.numerator, x.denominator, 0
    while n % 2 == 0:
        n //= 2; k += 1
    while d % 2 == 0:
        d //= 2; k -= 1
    return k


# ======================================================================
# Circuits of K(F, beta)
# ======================================================================
# gate = (kind, preds, data); kinds:
#   'table'  data = tuple of 2^f bits, index sum y_i 2^i
#   'thr'    data = (w, theta)           [v >= theta]
#   'exact'  data = (w, theta)           [v == theta]
#   'mod'    data = (w, theta, mu)       [v == theta mod mu]
#   'sym'    data = tuple of f+1 bits    phi(sum y_i), unit weights
# signals: inputs 0..m-1, gate j is signal m+j.

def gate_value(g, y):
    kind, preds, data = g
    if kind == 'table':
        return data[sum(b << i for i, b in enumerate(y))]
    if kind == 'sym':
        return data[sum(y)]
    w = data[0]
    v = sum(wi * yi for wi, yi in zip(w, y))
    if kind == 'thr':
        return int(v >= data[1])
    if kind == 'exact':
        return int(v == data[1])
    if kind == 'mod':
        return int((v - data[1]) % data[2] == 0)
    raise ValueError(kind)


def evaluate(m, gates, out, x):
    val = list(x)
    for g in gates:
        val.append(gate_value(g, [val[p] for p in g[1]]))
    return val[out]


def brute_count(m, gates, out):
    return sum(evaluate(m, gates, out, x) for x in itertools.product((0, 1), repeat=m))


def random_circuit(rng, m, G, F, beta, maxfan):
    gates = []
    for j in range(G):
        nsig = m + j
        kind = rng.choice(['table', 'thr', 'exact', 'mod', 'sym'])
        if kind == 'table':
            f = rng.randint(0, min(F, nsig))
        else:
            f = rng.randint(1, min(maxfan, nsig + 3))
        preds = [rng.randrange(nsig) for _ in range(f)]      # repetitions allowed
        if kind == 'table':
            data = tuple(rng.randint(0, 1) for _ in range(2 ** f))
        elif kind == 'sym':
            data = tuple(rng.randint(0, 1) for _ in range(f + 1))
        else:
            w = [rng.randint(-2 ** beta, 2 ** beta) for _ in range(f)]
            theta = rng.randint(-f * 2 ** beta // 2, f * 2 ** beta // 2)
            if kind == 'mod':
                data = (w, theta, rng.randint(1, 2 ** beta))
            else:
                data = (w, theta)
        gates.append((kind, preds, data))
    return gates, m + G - 1


def normalise(m, gates, out):
    """Delete gates that do not reach the output; drop unused inputs.
    Returns (m', gates', out', u) with #C = 2^u #C'."""
    n = m + len(gates)
    reach = [False] * n
    reach[out] = True
    for j in range(len(gates) - 1, -1, -1):
        if reach[m + j]:
            for p in gates[j][1]:
                reach[p] = True
    used_inputs = [i for i in range(m) if reach[i]]
    u = m - len(used_inputs)
    newid = {}
    for k, i in enumerate(used_inputs):
        newid[i] = k
    ng = []
    for j, g in enumerate(gates):
        if reach[m + j]:
            newid[m + j] = len(used_inputs) + len(ng)
            ng.append((g[0], [newid[p] for p in g[1]], g[2]))
    return len(used_inputs), ng, newid[out], u


# ======================================================================
# The network N(C)
# ======================================================================
class Network:
    def __init__(self):
        self.nedges = 0
        self.vertices = []          # (ports list of edge ids, tensor ndarray, side tag)

    def edge(self):
        self.nedges += 1
        return self.nedges - 1

    def vertex(self, ports, tensor, tag):
        tensor = np.asarray(tensor, dtype=np.int64)
        assert tensor.shape == (2,) * len(ports)
        self.vertices.append([list(ports), tensor, tag])


def tensor_from(fn, n):
    t = np.zeros((2,) * n, dtype=np.int64)
    for idx in itertools.product((0, 1), repeat=n):
        t[idx] = fn(idx)
    return t


def build_network(m, gates, out, K, beta):
    """Network of Section 4.2 with block size K and weight bound 2^beta,
    before and after subdivision.  Returns (network, stats)."""
    b = beta + math.ceil(math.log2(K)) + 2 if K > 1 else beta + 2
    occ = {s: [] for s in range(m + len(gates))}   # occurrences: (vertex index, port position)
    net = Network()
    pending = []          # vertices as lists of port placeholders, resolved after equality trees
    big_edges = 0

    def new_vertex(nports, tensor, tag):
        pending.append([[None] * nports, tensor, tag])
        return len(pending) - 1

    for j, g in enumerate(gates):
        kind, preds, data = g
        f = len(preds)
        sig = m + j
        small = kind == 'table' or f <= K
        if small:
            T = tensor_from(lambda idx: int(idx[f] == gate_value(g, idx[:f])), f + 1)
            v = new_vertex(f + 1, T, 'gate')
            for pos, p in enumerate(preds):
                occ[p].append((v, pos))
            occ[sig].append((v, f))
        else:
            w = data[0] if kind != 'sym' else [1] * f
            k = -(-f // K)
            blocks = [list(range(i * K, min(f, (i + 1) * K))) for i in range(k)]
            root_tensor = tensor_from(
                lambda idx: int(idx[k * b] == phi_of(kind, data, f, sum(
                    sum(idx[jj * b + t] << t for t in range(b)) - K * 2 ** beta for jj in range(k)))),
                k * b + 1)
            r = new_vertex(k * b + 1, root_tensor, 'root')
            for jj, I in enumerate(blocks):
                nI = len(I)
                Tb = tensor_from(lambda idx, I=I: int(sum(idx[nI + t] << t for t in range(b)) ==
                                                      sum(w[i] * idx[q] for q, i in enumerate(I)) + K * 2 ** beta),
                                 nI + b)
                bv = new_vertex(nI + b, Tb, 'block')
                for q, i in enumerate(I):
                    occ[preds[i]].append((bv, q))
                for t in range(b):
                    e = ('blk', bv, nI + t, r, jj * b + t)
                    pending_edges.append(e)
                    big_edges += 1
            occ[sig].append((r, k * b))
    # pin on the output
    pin = new_vertex(1, [0, 1], 'pin')
    occ[out].append((pin, 0))
    # equality trees
    for sgn, ports in occ.items():
        d = len(ports)
        if d == 0:
            continue
        if d == 1:
            u = new_vertex(1, [1, 1], 'eq')
            pending_edges.append(('eq', u, 0, ports[0][0], ports[0][1]))
        elif d == 2:
            u = new_vertex(2, np.eye(2, dtype=np.int64), 'eq')
            pending_edges.append(('eq', u, 0, ports[0][0], ports[0][1]))
            pending_edges.append(('eq', u, 1, ports[1][0], ports[1][1]))
        else:
            E3 = tensor_from(lambda idx: int(idx[0] == idx[1] == idx[2]), 3)
            # caterpillar: internal vertices c_1..c_{d-2}
            cs = [new_vertex(3, E3, 'eq') for _ in range(d - 2)]
            pending_edges.append(('eq', cs[0], 0, ports[0][0], ports[0][1]))
            pending_edges.append(('eq', cs[0], 1, ports[1][0], ports[1][1]))
            for i in range(1, d - 2):
                pending_edges.append(('eq', cs[i], 0, cs[i - 1], 2))
                pending_edges.append(('eq', cs[i], 1, ports[i + 1][0], ports[i + 1][1]))
            pending_edges.append(('eq', cs[-1], 2, ports[-1][0], ports[-1][1]))
    edges_before = len(pending_edges)
    # subdivision: every edge (a,pa)-(c,pc) becomes (a,pa)-s-(c,pc)
    ids = []
    for _ in pending:
        pass
    for (_, a, pa, c, pc) in pending_edges:
        e1, e2 = net.edge(), net.edge()
        pending[a][0][pa] = e1
        pending[c][0][pc] = e2
        net.vertex([e1, e2], np.eye(2, dtype=np.int64), 'sub')
    for ports, T, tag in pending:
        assert None not in ports
        net.vertex(ports, T, tag)
    degs = [len(p) for p, _, _ in net.vertices]
    return net, dict(edges_before=edges_before, edges=net.nedges, big_edges=big_edges,
                     maxdeg=max(degs), b=b, nvert=len(net.vertices))


def phi_of(kind, data, f, v):
    if kind == 'sym':
        return data[v] if 0 <= v <= f else 0
    if kind == 'thr':
        return int(v >= data[1])
    if kind == 'exact':
        return int(v == data[1])
    if kind == 'mod':
        return int((v - data[1]) % data[2] == 0)
    raise ValueError(kind)


pending_edges = []


def contract(net):
    """Exact contraction by greedy pairwise elimination (int64 entries)."""
    tensors = [(list(p), T.copy()) for p, T, _ in net.vertices]
    # each edge appears in exactly two tensors
    while len(tensors) > 1:
        # choose the pair sharing an edge with the smallest result
        where = {}
        for i, (p, _) in enumerate(tensors):
            for e in p:
                where.setdefault(e, []).append(i)
        best = None
        for e, (i, j) in ((e, l) for e, l in where.items() if len(l) == 2 and l[0] != l[1]):
            sh = set(tensors[i][0]) & set(tensors[j][0])
            size = len(set(tensors[i][0]) | set(tensors[j][0])) - 2 * len(sh)
            if best is None or size < best[0]:
                best = (size, i, j)
        if best is None:      # disconnected components: multiply scalars
            i, j = 0, 1
        else:
            _, i, j = best
        pi, Ti = tensors[i]
        pj, Tj = tensors[j]
        shared = [e for e in pi if e in pj]
        letters = {}
        for e in pi + pj:
            if e not in letters:
                letters[e] = len(letters)
        assert len(letters) <= 52, 'intermediate tensor too large'
        L = 'abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ'
        si = ''.join(L[letters[e]] for e in pi)
        sj = ''.join(L[letters[e]] for e in pj)
        po = [e for e in pi if e not in shared] + [e for e in pj if e not in shared]
        so = ''.join(L[letters[e]] for e in po)
        T = np.einsum(si + ',' + sj + '->' + so, Ti, Tj)
        tensors = [t for k, t in enumerate(tensors) if k not in (i, j)] + [(po, T)]
    p, T = tensors[0]
    assert p == []
    return int(T)


def part_A(rng):
    global pending_edges
    print('(A) contraction of N(C) against exhaustive counting')
    trials, kinds_big = 0, set()
    for trial in range(120):
        m = rng.randint(1, 6)
        gates, out = random_circuit(rng, m, rng.randint(1, 5), F=3, beta=1, maxfan=7)
        m2, g2, out2, u = normalise(m, gates, out)
        K, beta = 2, 1
        pending_edges = []
        net, st = build_network(m2, g2, out2, K, beta)
        if max(len(p) for p, _, _ in net.vertices) > 20:
            continue
        for g in g2:
            if g[0] != 'table' and len(g[1]) > K:
                kinds_big.add(g[0])
        Z = contract(net) * 2 ** u
        ok = Z == brute_count(m, gates, out)
        trials += 1
        if not ok:
            check('contraction trial %d' % trial, False, 'Z=%d count=%d' % (Z, brute_count(m, gates, out)))
            return
    check('contraction equals #C on %d random circuits' % trials, True,
          '(big gates of kinds %s split into blocks)' % ','.join(sorted(kinds_big)))
    check('all four weighted kinds occurred as big gates', kinds_big >= {'thr', 'exact', 'mod', 'sym'})


# ======================================================================
# (B) sizes
# ======================================================================
def part_B(rng):
    global pending_edges
    print('(B) the Size lemma: edges and degrees')
    worst = 0.0
    nets = withbig = 0
    for trial in range(200):
        m = rng.randint(2, 40)
        G = rng.randint(1, 60)
        if trial % 2:
            gates, out = random_circuit(rng, m, G, F=2, beta=1, maxfan=60)
        else:
            # many small gates and a few big weighted gates of large fan-in
            gates, _ = random_circuit(rng, m, rng.randint(100, 400), F=2, beta=1, maxfan=2)
            for _ in range(rng.randint(1, 3)):
                f = rng.randint(200, 700)
                nsig = m + len(gates)
                kind = rng.choice(['thr', 'exact', 'mod'])
                data = ([1] * f, f // 3, 3) if kind == 'mod' else ([1] * f, f // 3)
                gates.append((kind, [rng.randrange(nsig) for _ in range(f)], data))
            nsig = m + len(gates)
            gates.append(('exact', list(range(nsig - 3, nsig)), ([1, 1, 1], 3)))
            out = m + len(gates) - 1
        m2, g2, out2, u = normalise(m, gates, out)
        W = sum(len(g[1]) for g in g2)
        s = m2 + W
        if s < 2:
            continue
        K, beta = int(s ** 0.8), int(s ** (2 / 3))
        # count edges and degrees without building tensors
        b = beta + math.ceil(math.log2(K)) + 2
        dsig = {sg: 0 for sg in range(m2 + len(g2))}
        big = 0
        maxdeg = 3
        for j, g in enumerate(g2):
            f = len(g[1])
            dsig[m2 + j] += 1
            for p in g[1]:
                dsig[p] += 1
            if g[0] == 'table' or f <= K:
                maxdeg = max(maxdeg, f + 1)
            else:
                k = -(-f // K)
                big += k * b
                maxdeg = max(maxdeg, k * b + 1, K + b)
        dsig[out2] += 1
        tree = sum({0: 0, 1: 1, 2: 2}.get(d, 2 * d - 3) for d in dsig.values())
        before = tree + big
        G2 = len(g2)
        ok = sum(dsig.values()) == G2 + W + 1 and tree <= 2 * (G2 + W + 1)
        if b <= K:
            ok = ok and big <= 2 * W and 2 * before <= 22 * s
            withbig += big > 0
            worst = max(worst, 2 * before / s)
        nets += 1
        if not ok:
            check('size trial %d' % trial, False)
            return
    check('occurrences sum to G+W+1, trees <= 2 sum d, edges <= 22s on %d circuits' % nets, True,
          '(%d with b <= K and a big gate; largest edges/s = %.2f)' % (withbig, worst))
    check('at least 50 circuits with b <= K have a big gate', withbig >= 50)
    # degree bound: worst case over f <= s of max(K+1, K+b, ceil(f/K) b + 1)
    first_ok = None
    bad_after = []
    for s in range(2, 3 * 10 ** 6):
        K, beta = int(s ** 0.8), int(s ** (2 / 3))
        if K < 1:
            continue
        b = beta + math.ceil(math.log2(K)) + 2 if K > 1 else beta + 2
        deg = max(K + b, (-(-s // K)) * b + 1)
        ok = deg <= math.ceil(s ** 0.9) and b <= K
        if ok and first_ok is None:
            first_ok = s
        if not ok and first_ok is not None:
            first_ok = None
            bad_after.append(s)
    check('degree <= ceil(s^(9/10)) and b <= K for all s from %d to 3*10^6' % first_ok, first_ok is not None)


# ======================================================================
# (C) zero-one programs
# ======================================================================
def ilp_circuit(A, b, extra=None):
    """Circuit of Theorem C: rows as thresholds, conjunction as an exact gate."""
    n = len(A[0])
    gates = []
    for row, bj in zip(A, b):
        supp = [k for k in range(n) if row[k] != 0]
        gates.append(('thr', supp, ([-row[k] for k in supp], -bj)))
    if extra is not None:
        c, t = extra
        gates.append(('thr', list(range(n)), (list(c), t)))
    r = len(gates)
    gates.append(('exact', [n + j for j in range(r)], ([1] * r, r)))
    return n, gates, n + r


def part_C(rng):
    print('(C) Theorem C: zero-one programs')
    good = True
    for trial in range(60):
        n, r = rng.randint(1, 8), rng.randint(1, 5)
        A = [[rng.choice([0, 0, rng.randint(-6, 6)]) for _ in range(n)] for _ in range(r)]
        A = [row for row in A if any(row)] or [[1] * n]
        b = [rng.randint(-4, 8) for _ in A]
        c = [rng.randint(-5, 5) for _ in range(n)]
        pts = [x for x in itertools.product((0, 1), repeat=n)
               if all(sum(a * xi for a, xi in zip(row, x)) <= bj for row, bj in zip(A, b))]
        m, gates, out = ilp_circuit(A, b)
        good &= brute_count(m, gates, out) == len(pts)

        def count_with(Ap, bp, t):
            m, gates, out = ilp_circuit(Ap, bp, (c_cur, t))
            return brute_count(m, gates, out)
        if pts:
            c_cur = c
            bound = len(c) * max(1, max(abs(v) for v in c))
            lo, hi = -bound, bound                    # max c.x in [lo, hi]
            while lo < hi:
                mid = (lo + hi + 1) // 2
                if count_with(A, b, mid) > 0:
                    lo = mid
                else:
                    hi = mid - 1
            tmax = lo
            good &= tmax == max(sum(ci * xi for ci, xi in zip(c, x)) for x in pts)
            # self-reduction: fix x_1, x_2, ... keeping the count positive
            x_fixed = []
            Acur, bcur, ccur, off = [row[:] for row in A], b[:], c[:], 0
            for k in range(n):
                for val in (0, 1):
                    # program on remaining variables with x_k = val
                    A2 = [row[1:] for row in Acur]
                    b2 = [bj - row[0] * val for row, bj in zip(Acur, bcur)]
                    c2 = ccur[1:]
                    off2 = off + ccur[0] * val
                    if not A2[0] if A2 else True:
                        feasible = all(bj >= 0 for bj in b2) and off2 >= tmax
                    else:
                        c_cur = c2
                        mm, gg, oo = ilp_circuit(A2, b2, (c2, tmax - off2))
                        feasible = brute_count(mm, gg, oo) > 0
                    if feasible:
                        x_fixed.append(val)
                        Acur, bcur, ccur, off = A2, b2, c2, off2
                        break
            good &= len(x_fixed) == n and tuple(x_fixed) in pts and \
                sum(ci * xi for ci, xi in zip(c, x_fixed)) == tmax
        else:
            good &= True
    check('feasible counts, binary search and self-reduction on 60 random programs', good)


# ======================================================================
# (D) the identity (eq:vEt) and the bound -6Dh
# ======================================================================
def qmult(i, u, h):
    return h * max(0, u - i)


def part_D():
    print('(D) identity (eq:vEt) and v2(E_t(0)) >= -6Dh')
    good_id = good_bd = good_c = True
    cases = 0
    for a in range(1, 8):
        L = 2 ** a
        S = list(range(-L, L))
        Cp = lambda t: math.prod(t - q for q in S if q != t)
        good_c &= all(v2(Cp(t)) == v2(Cp(0)) for t in S)
        for u in range(1, a + 1):
            for h in (1, 2, 3, 5):
                for t in S:
                    if t == 0:
                        continue
                    i = v2(t)
                    if qmult(i, u, h) == 0:
                        continue
                    D = L // 2 ** i
                    direct = sum(qmult(v2(q), u, h) * (v2(q) - v2(t - q)) for q in S if q not in (0, t))
                    formula = Fraction(D) * sum(Fraction(j, 2 ** j) * (qmult(i + j, u, h) - qmult(i, u, h))
                                                for j in range(1, a - i + 1))
                    good_id &= direct == formula
                    good_bd &= direct >= -6 * D * h
                    cases += 1
    check('v2(C\'(t)) = v2(C\'(0)) for all t in S, a <= 7', good_c)
    check('(eq:vEt) holds in %d cases (a <= 7, all u, h in {1,2,3,5})' % cases, good_id)
    check('v2(E_t(0)) >= -6Dh in the same cases', good_bd)


# ======================================================================
# polynomial helpers over Q (lists of Fractions, low degree first)
# ======================================================================
def pmul(p, q):
    r = [Fraction(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        if a:
            for j, b in enumerate(q):
                r[i + j] += a * b
    return r


def ppow(p, k):
    r = [Fraction(1)]
    for _ in range(k):
        r = pmul(r, p)
    return r


def peval(p, x):
    r = Fraction(0)
    for c in reversed(p):
        r = r * x + c
    return r


def pcompose_lin(p, t, alpha):
    """p(t + alpha z) as a polynomial in z."""
    r = [Fraction(0)]
    for c in reversed(p):
        r = pmul(r, [Fraction(t), Fraction(alpha)])
        r[0] += c
    return r


def series_inv(p, n):
    """Inverse of a power series with p[0] != 0, modulo z^n."""
    inv = [Fraction(0)] * n
    inv[0] = 1 / p[0]
    for k in range(1, n):
        s = sum(p[j] * inv[k - j] for j in range(1, min(k, len(p) - 1) + 1))
        inv[k] = -s / p[0]
    return inv


# ======================================================================
# (E) integrality of the Cauchy deformation
# ======================================================================
def part_E():
    print('(E) Integrality lemma of W(t + alpha z)')
    good = good0 = True
    cases = 0
    for a in range(1, 5):
        L = 2 ** a
        S = list(range(-L, L))
        alpha = 2 ** (a + 1)
        Cpoly = [Fraction(1)]
        for q in S:
            Cpoly = pmul(Cpoly, [Fraction(-q), Fraction(1)])
        Cp0 = math.prod(-q for q in S if q != 0)
        for d in range(-(L - 1), L):           # d = y - x for slots x, y in [0, L)
            # W(T) = prod_{q != d} (T - q) / C'(0)
            Wp = [Fraction(1)]
            for q in S:
                if q != d:
                    Wp = pmul(Wp, [Fraction(-q), Fraction(1)])
            Wp = [c / Cp0 for c in Wp]
            good0 &= peval(Wp, 0) == (1 if d == 0 else 0)
            for t in S:
                comp = pcompose_lin(Wp, t, alpha)
                good &= all(c == 0 or v2(c) >= 0 for c in comp)
                cases += 1
    check('W(0) is the identity for a <= 4', good0)
    check('every coefficient of W_xy(t + alpha z) is 2-integral (%d cases, a <= 4)' % cases, good)


# ======================================================================
# (F) Hermite formula
# ======================================================================
def part_F(rng):
    print('(F) the Hermite formula (eq:hermite)')
    good = True
    cases = 0
    for a in (1, 2, 3):
        L = 2 ** a
        S = list(range(-L, L))
        alpha = 2 ** (a + 1)
        for u in range(1, a + 1):
            for h in (1, 2):
                q = {t: qmult(v2(t), u, h) for t in S if t != 0}
                total = sum(q.values())
                for _ in range(3):
                    deg = total - 1
                    F = [Fraction(rng.randint(-50, 50), rng.randint(1, 9)) for _ in range(deg + 1)]
                    rhs = Fraction(0)
                    for t, qt in q.items():
                        if qt == 0:
                            continue
                        Et = [Fraction(1)]
                        for qq, mult in q.items():
                            if qq != t and mult:
                                Et = pmul(Et, ppow([Fraction(-qq, t - qq), Fraction(1, t - qq)], mult))
                        Ft = pcompose_lin(F, t, alpha)
                        Ett = pcompose_lin(Et, t, alpha)
                        quot = pmul(Ft[:qt], series_inv(Ett, qt))[:qt]
                        rhs += peval(Et, 0) * peval(quot, Fraction(-t, alpha))
                    good &= rhs == F[0]
                    cases += 1
    check('F(0) recovered exactly from truncated expansions (%d random F, a <= 3)' % cases, good)


# ======================================================================
# (G) packing
# ======================================================================
def random_bipartite(rng, M, Delta):
    """Random bipartite multigraph with M edges and maximum degree <= Delta."""
    nr = nc = -(-M // Delta) + 2
    rows = [i for i in range(nr) for _ in range(Delta)]
    cols = [j for j in range(nc) for _ in range(Delta)]
    rng.shuffle(rows); rng.shuffle(cols)
    return list(zip(rows[:M], cols[:M])), nr, nc


def part_G(rng):
    print('(G) Packing lemma')
    for (r, a, Delta, M) in ((2, 1, 4, 160), (3, 1, 4, 700), (2, 2, 8, 4200)):
        N = r ** a
        Darr = N * N
        L = 2 ** a
        assert M >= 2 * Darr ** 2 * Delta and M >= L * Darr and 2 * L <= Delta
        edges, nr, nc = random_bipartite(rng, M, Delta)
        labels = list(itertools.product(range(r), repeat=a))
        lab = {}
        inc = {}
        for k, (x, y) in enumerate(edges):
            inc.setdefault(('R', x), []).append(k)
            inc.setdefault(('C', y), []).append(k)
        # method of conditional expectations on E sum_gamma X_gamma^2, in units of
        # 1/N^2: a pair of endpoints contributes N if equal or equally labelled
        # (0 if differently labelled), and 1 if one of them is unlabelled.
        verts = [('R', x) for x in range(nr)] + [('C', y) for y in range(nc)]
        ER = np.array([x for x, _ in edges]); EC = np.array([y for _, y in edges])
        code = {'R': -np.ones(nr, dtype=np.int64), 'C': -np.ones(nc, dtype=np.int64)}

        def factor(side, w, arr_other):
            other = code[side][arr_other]
            f = np.where(other < 0, 1, np.where(other == code[side][w], N, 0))
            f = np.where(code[side][w] < 0, 1, f)
            return np.where(arr_other == w, N, f)
        for v in verts:
            side, idx = v
            if v not in inc:
                code[side][idx] = 0
                continue
            best = None
            for cand in range(N):
                code[side][idx] = cand
                cost = 0
                for k in inc[v]:
                    ex, ey = edges[k]
                    cost += int(np.dot(factor('R', ex, ER), factor('C', ey, EC)))
                if best is None or cost < best[0]:
                    best = (cost, cand)
            code[side][idx] = best[1]
        lab = {}
        for x in range(nr):
            lab[('R', x)] = labels[code['R'][x]]
        for y in range(nc):
            lab[('C', y)] = labels[code['C'][y]]
        X = {}
        for (x, y) in edges:
            g = (lab[('R', x)], lab[('C', y)])
            X.setdefault(g, []).append((x, y))
        load = max(len(v) for v in X.values())
        bound = M / Darr + math.sqrt(2 * M * Delta)
        check('r=%d a=%d: largest load %d <= M/Darr + sqrt(2 M Delta) = %.1f' % (r, a, load, bound), load <= bound)
        Hpad = -(-load // L) * L
        check('r=%d a=%d: H_pad = %d <= 3M/Darr = %.1f' % (r, a, Hpad, 3 * M / Darr), Hpad <= 3 * M / Darr)
        # slots of each pair label: real edges then padding
        slots = {}
        for rl in labels:
            for cl in labels:
                lst = X.get((rl, cl), [])
                slots[(rl, cl)] = lst + [None] * (Hpad - len(lst))
        # groups by unordered pairs per coordinate
        groups = {}
        for (rl, cl) in slots:
            key = tuple(tuple(sorted((rl[c], cl[c]))) for c in range(a))
            groups.setdefault(key, []).append((rl, cl))
        packets = []
        for key, members in groups.items():
            unequal = [c for c in range(a) if key[c][0] != key[c][1]]
            ap = len(unequal)
            assert len(members) == 2 ** ap
            per = 2 ** (a - ap)
            copy_bits = [c for c in range(a) if c not in unequal]
            for p in range(Hpad // per):
                packet = [None] * L
                for (rl, cl) in members:
                    orient = [int(rl[c] > cl[c]) for c in unequal]
                    for cpy in range(per):
                        pos = 0
                        for bit, c in zip(orient, unequal):
                            pos |= bit << c
                        for kk, c in enumerate(copy_bits):
                            pos |= ((cpy >> kk) & 1) << c
                        assert packet[pos] is None
                        packet[pos] = ((rl, cl), slots[(rl, cl)][p * per + cpy])
                packets.append((key, packet))
        ok1 = len(packets) <= 3 * M / L
        placed = [e for _, pk in packets for (_, e) in pk if e is not None]
        ok1 &= sorted(placed) == sorted(edges)
        ok2 = True
        for key, pk in packets:
            for pos, (g, e) in enumerate(pk):
                rl, cl = g
                for c in range(a):
                    ok2 &= tuple(sorted((rl[c], cl[c]))) == key[c]
                    if rl[c] != cl[c]:
                        ok2 &= ((pos >> c) & 1) == int(rl[c] > cl[c])
        ok3 = True
        for c in range(a):
            for sym in range(r):
                nrow = sum(1 for (x, y) in edges if lab[('R', x)][c] == sym)
                ncol = sum(1 for (x, y) in edges if lab[('C', y)][c] == sym)
                ok3 &= nrow <= 3 * M / r and ncol <= 3 * M / r
        check('r=%d a=%d: (1) %d packets <= 3M/L, every edge placed once' % (r, a, len(packets)), ok1)
        check('r=%d a=%d: (2) unordered pairs fixed, orientation in bit c' % (r, a), ok2)
        check('r=%d a=%d: (3) at most 3M/r ports per symbol and coordinate' % (r, a), ok3)


if __name__ == '__main__':
    rng = random.Random(20261104)
    part_A(rng)
    part_B(rng)
    part_C(rng)
    part_D()
    part_E()
    part_F(rng)
    part_G(rng)
    print('%d checks passed, %d failed' % (PASS, FAIL))
    sys.exit(1 if FAIL else 0)
