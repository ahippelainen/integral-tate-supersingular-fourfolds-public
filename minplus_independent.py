"""Independent recomputation of Propositions 4.3, 5.1 and 8.4 with separately written min-plus code that shares nothing with minplus.py.

Basis e_i of M, i = 4 s1 + 2 s2 + s3, F e_i = (sign) p^{w_i} e_{perm(i)}. The Künneth (2,2)-component of the square is computed inside wedge^4 of the 16-dimensional module M + M rather than from Künneth components.
"""
from itertools import combinations, permutations

INF = 10 ** 9


def inert_pi():
    """The model (1.2): F(x1 (x) x2 (x) x3) = x3 (x) A x1 (x) x2."""
    perm, w = {}, {}
    for a in (0, 1):
        for b in (0, 1):
            for c in (0, 1):
                perm[4 * a + 2 * b + c] = 4 * c + 2 * (1 - a) + b
                w[4 * a + 2 * b + c] = a
    return perm, w


def split_pi():
    """(W^2, A sigma) (x) (W^4, sigma)."""
    perm, w = {}, {}
    for a in (0, 1):
        for b in (0, 1):
            for c in (0, 1):
                perm[4 * a + 2 * b + c] = 4 * (1 - a) + 2 * b + c
                w[4 * a + 2 * b + c] = a
    return perm, w


def degree2_pi():
    """(W^2, sigma) (x) (W^2 (x) W^2, (A (x) 1) sigma'): slot 1 unit root, slots 2 and 3 exchanged, A in slot 2."""
    perm, w = {}, {}
    for a in (0, 1):
        for b in (0, 1):
            for c in (0, 1):
                perm[4 * a + 2 * b + c] = 4 * a + 2 * c + (1 - b)
                w[4 * a + 2 * b + c] = b
    return perm, w


def direct_sum(*mods):
    perm, w, off = {}, {}, 0
    for pm, ww in mods:
        for i in range(len(pm)):
            perm[off + i] = off + pm[i]
            w[off + i] = ww[i]
        off += len(pm)
    return perm, w


def order(perm):
    k, cur = 1, dict(perm)
    while any(cur[i] != i for i in cur):
        cur = {i: perm[cur[i]] for i in cur}
        k += 1
    return k


def tate_exponents(perm, w, k):
    """n_K for all k-sets K: the exponents of cap_j phi^j(wedge^k M), phi = p^{-k/2} wedge^k F, walking backwards along the orbit of K."""
    n = len(perm)
    inv = {perm[i]: i for i in range(n)}
    period = order(perm)
    out = {}
    for K in combinations(range(n), k):
        K = frozenset(K)
        cur, acc, best = K, 0, 0
        for _ in range(period):
            cur = frozenset(inv[i] for i in cur)
            acc += sum(w[i] for i in cur) - k // 2
            best = max(best, acc)
        assert cur == K and acc == 0
        out[K] = best
    return out


def product_exponents(nI, nJ, k1, k2, n):
    """Span of x ^ y, x in the k1-form lattice nI, y in the k2-form lattice nJ."""
    out = {}
    for K in combinations(range(n), k1 + k2):
        out[frozenset(K)] = min(nI[frozenset(I)] + nJ[frozenset(K) - frozenset(I)] for I in combinations(K, k1))
    return out


def end_exponents(perm, w):
    """m[(a, b)]: exponent of End(M, F) (x) W at the matrix unit e_b -> e_a."""
    n = len(perm)
    inv = {perm[i]: i for i in range(n)}
    m = {}
    for a0 in range(n):
        for b0 in range(n):
            a, b, acc, best = a0, b0, 0, 0
            while True:
                a, b = inv[a], inv[b]
                acc += w[a] - w[b]
                best = max(best, acc)
                if (a, b) == (a0, b0):
                    break
            assert acc == 0
            m[a0, b0] = best
    return m


def lab(K):
    return "{" + ",".join(format(i, "03b") for i in sorted(K)) + "}"


def fs(*bits):
    return frozenset(int(b, 2) for b in bits)


def end_span(src, m, n4):
    """Span over U in End of wedge^4 U (x), x in the monomial lattice src: target t_i = image of the i-th element of K (injective, else wedge^4 vanishes)."""
    out = {K: INF for K in n4}
    for K, e in src.items():
        Ks = sorted(K)
        for tgt in permutations(range(8), 4):
            v = e + sum(m[tgt[i], Ks[i]] for i in range(4))
            T = frozenset(tgt)
            if v < out[T]:
                out[T] = v
    return out


def block(perm, w, src=None):
    """[T_22 : S_22] and [T_22 : S_22 + PB(src)] inside wedge^4 of M + M (indices < 8 first summand)."""
    m = end_exponents(perm, w)
    permY, wY = direct_sum((perm, w), (perm, w))
    n2Y, n4Y = tate_exponents(permY, wY, 2), tate_exponents(permY, wY, 4)
    s4Y = product_exponents(n2Y, n2Y, 2, 2, 16)
    blk = [K for K in n4Y if sum(1 for i in K if i < 8) == 2]
    out = [sum(s4Y[K] - n4Y[K] for K in blk)]
    assert all(s4Y[K] >= n4Y[K] for K in blk)
    if src is not None:
        pb = {}
        for K, e in src.items():
            Ks = sorted(K)
            for c1 in combinations(range(4), 2):
                c2 = [i for i in range(4) if i not in c1]
                for t1 in permutations(range(8), 2):
                    for t2 in permutations(range(8), 2):
                        v = e + m[t1[0], Ks[c1[0]]] + m[t1[1], Ks[c1[1]]] + m[t2[0], Ks[c2[0]]] + m[t2[1], Ks[c2[1]]]
                        T = frozenset([t1[0], t1[1], 8 + t2[0], 8 + t2[1]])
                        if v < pb.get(T, INF):
                            pb[T] = v
        assert all(pb.get(K, INF) >= n4Y[K] for K in blk)
        out.append(sum(min(s4Y[K], pb.get(K, INF)) - n4Y[K] for K in blk))
    return out


# Proposition 4.3
perm, w = inert_pi()
n2, n4, n6 = (tate_exponents(perm, w, k) for k in (2, 4, 6))
s4 = product_exponents(n2, n2, 2, 2, 8)
s6 = product_exponents(n2, s4, 2, 4, 8)
assert all(s4[K] >= n4[K] for K in n4) and all(s6[K] >= n6[K] for K in n6)
defects = {K: (n4[K], s4[K]) for K in n4 if s4[K] != n4[K]}
Tp, Tm = fs("000", "011", "101", "110"), fs("001", "010", "100", "111")
Mp, Mm = fs("000", "001", "011", "101"), fs("010", "100", "110", "111")
i4, i6 = sum(s4[K] - n4[K] for K in n4), sum(s6[K] - n6[K] for K in n6)
print(f"Proposition 4.3: [T^4 : S] = p^{i4};", " ".join(f"{lab(K)} {v}" for K, v in sorted(defects.items(), key=lambda kv: lab(kv[0]))))
print(f"  [T^6 : triple products] = p^{i6}")
assert defects == {Tp: (0, 1), Tm: (0, 1), Mm: (0, 1), Mp: (1, 2)} and i4 == 4 and i6 == 0

# Lemma 4.4(i), (ii): the 4-sets J with perm(J) = complement of J, and |J cap {s1 = 1}|
eig = {K for K in n4 if frozenset(perm[i] for i in K) == frozenset(range(8)) - K}
cnt = {lab(K): sum(1 for i in K if w[i] == 1) for K in (Tp, Tm, Mp, Mm)}
print("Lemma 4.4: F-compatible eigensets", " ".join(lab(K) for K in sorted(eig, key=lab)), "; |J cap {s1=1}| for T+, T-, M+, M-:", list(cnt.values()))
assert eig == {Tp, Tm, Mp, Mm} and list(cnt.values()) == [2, 2, 1, 3]

# Proposition 5.1
m = end_exponents(perm, w)
idx = lambda *lats: sum(min(l.get(K, INF) for l in lats) - n4[K] for K in n4)
L = {Tp: n4[Tp], Tm: n4[Tm]}
N = {Mp: n4[Mp], Mm: n4[Mm]}
cS, cL, cN = end_span(s4, m, n4), end_span(L, m, n4), end_span(N, m, n4)
i_ok = all(cS[K] >= s4[K] for K in n4)
iii_ok = all(cN[K] >= min(s4[K], N.get(K, INF)) for K in n4)
r = (idx(s4, L), idx(s4, cL), idx(s4, N))
print(f"Proposition 5.1: (i) End^* S inside S: {i_ok}; (ii) [T^4 : S + L] = p^{r[0]}, [T^4 : S + End^* L] = p^{r[1]}; (iii) End^* N inside S + N: {iii_ok}, [T^4 : S + N] = p^{r[2]}")
assert i_ok and iii_ok and r == (2, 0, 2)
b = block(perm, w, L)
print(f"  (iv) [T_22 : S_22] = p^{b[0]}, [T_22 : S_22 + PB(L)] = p^{b[1]}")
assert b[1] == 0

# Proposition 8.4
for nm, (perm, w) in (("(W^2, A sigma) (x) (W^4, sigma)", split_pi()), ("Hodge slot at the place of degree 2", degree2_pi())):
    n2, n4 = tate_exponents(perm, w, 2), tate_exponents(perm, w, 4)
    s4 = product_exponents(n2, n2, 2, 2, 8)
    e = sum(s4[K] - n4[K] for K in n4)
    bb, = block(perm, w)
    print(f"Proposition 8.4, {nm}: [T^4 : S] = p^{e}, [T_22 : S_22] = p^{bb}")
    assert all(s4[K] >= n4[K] for K in n4) and e == 0 and bb == 0
print("all assertions passed")
