"""Independent check of Proposition 5.1(i)-(iii) at p = 5, 13, 17 without the min-plus formula.

Explicit Z_p-bases of T^2, T^4 and End(M, F) of the model (1.2) are built as vectors over the Galois ring W(F_{p^12}) modulo p^7, each checked to be Tate (respectively to commute with F), saturated and of full rank. S is spanned by all products of two basis vectors of T^2, squares included. wedge^4 U is applied to random endomorphisms U, and lattice colengths are computed by exact elimination over the chain ring W(F_{p^12})/p^7. Inclusions (i) and (iii) are tested on the sampled U only; the equality S + End^* w = T^4 in (ii) holds for the true span because it already holds for the sampled one.
"""
import itertools as it
import numpy as np
from sympy.polys.galoistools import gf_irreducible_p
from sympy.polys.domains import ZZ

R = 12  # W(F_{p^12}) contains the coefficients of all Frobenius orbits of the model


def run(p, N, NS, seed):
    q = p ** N
    rng = np.random.default_rng(seed)

    # F_{p^12} = F_p[x]/(f) for the first monic irreducible f of degree R in lexicographic order of its coefficients from the top; f is stored from low to high degree
    f = next([1] + list(c) for c in it.product(range(p), repeat=R) if gf_irreducible_p([1] + list(c), p, ZZ))[::-1]
    red = np.zeros((2 * R - 1, R), dtype=np.int64)  # x^k mod f
    for k in range(2 * R - 1):
        v = [0] * (2 * R - 1)
        v[k] = 1
        for d in range(2 * R - 2, R - 1, -1):
            c = v[d]
            if c:
                for i in range(R + 1):
                    v[d - R + i] -= c * f[i]
        red[k] = np.array(v[:R]) % q

    def mul(a, b):
        """Product in W(F_{p^R})/p^N, broadcasting over leading axes."""
        a, b = np.broadcast_arrays(a, b)
        c = np.zeros(a.shape[:-1] + (2 * R - 1,), dtype=np.int64)
        for i in range(R):
            c[..., i:i + R] += a[..., i:i + 1] * b
            c[..., i:i + R] %= q
        return (c @ red) % q

    def one():
        e = np.zeros(R, dtype=np.int64)
        e[0] = 1
        return e

    def power(a, e):
        r = one()
        b = a.copy()
        while e:
            if e & 1:
                r = mul(r, b)
            b = mul(b, b)
            e >>= 1
        return r

    def inv(u):
        z = power(u, p ** R - 2)  # inverse modulo p, then Newton
        for _ in range(N.bit_length() + 1):
            z = (mul(z, (2 * one() - mul(u, z)) % q)) % q
        return z

    def poly_eval(coeffs, y):
        r = np.zeros(R, dtype=np.int64)
        for c in reversed(coeffs):
            r = (mul(r, y) + c * one()) % q
        return r

    # sigma: the Hensel lift of x -> x^p to the root of f
    xg = np.zeros(R, dtype=np.int64)
    xg[1] = 1
    y = power(xg, p)
    fp = [i * f[i] for i in range(1, R + 1)]
    for _ in range(N + 2):
        y = (y - mul(poly_eval(f, y), inv(poly_eval(fp, y)))) % q
    assert not poly_eval(f, y).any()
    Sig = np.zeros((R, R), dtype=np.int64)
    cur = one()
    for i in range(R):
        Sig[i] = cur
        cur = mul(cur, y)

    def sig(a, k=1):
        for _ in range(k % R):
            a = (a @ Sig) % q
        return a

    def val(a):
        """Valuation (N for zero), vectorised over leading axes."""
        v = np.full(a.shape, N, dtype=np.int64)
        t = a.copy()
        for j in range(N - 1, -1, -1):
            m = (t % (p ** j) == 0) & (t != 0)
            v = np.where(m & (v == N), j, v)
        return v.min(axis=-1)

    assert (sig(xg, R) == xg).all()
    assert (sig(mul(xg, xg)) == mul(sig(xg), sig(xg))).all()

    labels = ["".join(s) for s in it.product("01", repeat=3)]
    idx = {s: i for i, s in enumerate(labels)}
    pi = {s: s[2] + str(1 - int(s[0])) + s[1] for s in labels}
    a = {s: int(s[0]) for s in labels}

    def perm_sign(seq):
        seq = list(seq)
        s = 1
        for i in range(len(seq)):
            for j in range(i + 1, len(seq)):
                if seq[i] > seq[j]:
                    s = -s
        return s

    subs = {k: [tuple(c) for c in it.combinations(labels, k)] for k in (2, 4)}
    sidx = {k: {K: i for i, K in enumerate(subs[k])} for k in (2, 4)}

    def Fwedge(K):
        img = [pi[x] for x in K]
        return perm_sign([idx[x] for x in img]), sum(a[x] for x in K), tuple(sorted(img, key=lambda s: idx[s]))

    def apply_F(vec, k):
        out = np.zeros_like(vec)
        for K in subs[k]:
            sg, e, J = Fwedge(K)
            out[sidx[k][J]] = (out[sidx[k][J]] + sg * (p ** e) * sig(vec[sidx[k][K]])) % q
        return out

    def rank_mod_p(A):
        A = A.copy() % p
        r = 0
        rows, cols = A.shape
        for c in range(cols):
            piv = [i for i in range(r, rows) if A[i, c]]
            if not piv:
                continue
            A[[r, piv[0]]] = A[[piv[0], r]]
            A[r] = (A[r] * pow(int(A[r, c]), -1, p)) % p
            for i in range(rows):
                if i != r and A[i, c]:
                    A[i] = (A[i] - A[i, c] * A[r]) % p
            r += 1
        return r

    def eigen_basis(r, E):
        """Z_p-basis of {z : sigma^r z = E z}, by twisted traces and independence modulo p."""
        gens = []
        for i in range(R):
            z = np.zeros(R, dtype=np.int64)
            z[i] = 1
            acc = np.zeros(R, dtype=np.int64)
            t = z
            for j in range(R // r):
                acc = (acc + (E ** j) * t) % q
                t = sig(t, r)
            gens.append(acc)
        basis, M = [], np.zeros((0, R), dtype=np.int64)
        for g in gens:
            T = np.vstack([M, g[None] % p])
            if rank_mod_p(T) > M.shape[0]:
                basis.append(g)
                M = T
            if len(basis) == r:
                break
        assert len(basis) == r
        for g in basis:
            assert ((sig(g, r) - E * g) % q == 0).all()
        return basis

    def tate_basis(k):
        dim = len(subs[k])
        seen = set()
        basis = []
        for K0 in subs[k]:
            if K0 in seen:
                continue
            orb, signs, exps, K = [], [], [], K0
            while True:
                orb.append(K)
                seen.add(K)
                sg, e, J = Fwedge(K)
                signs.append(sg)
                exps.append(e - k // 2)
                K = J
                if K == K0:
                    break
            r = len(orb)
            E = int(np.prod(signs))
            assert sum(exps) == 0
            cs = np.concatenate([[0], np.cumsum(exps)[:-1]])
            base = int(max(-cs))
            for z in eigen_basis(r, E):
                v = np.zeros((dim, R), dtype=np.int64)
                cur = z.copy()
                sgn = 1
                for j, K in enumerate(orb):
                    v[sidx[k][K]] = (sgn * (p ** (base + int(cs[j]))) * cur) % q
                    cur = sig(cur)
                    sgn *= signs[j]
                assert ((apply_F(v, k) - (p ** (k // 2)) * v) % q == 0).all(), "not Tate"
                basis.append(v)
        B = np.array(basis)
        assert B.shape[0] == dim
        assert rank_mod_p(B.reshape(dim, -1)) == dim, "not saturated"
        return B

    def end_basis():
        seen, basis = set(), []
        for s0 in labels:
            for t0 in labels:
                if (s0, t0) in seen:
                    continue
                orb, exps, st = [], [], (s0, t0)
                while True:
                    orb.append(st)
                    seen.add(st)
                    exps.append(a[st[0]] - a[st[1]])
                    st = (pi[st[0]], pi[st[1]])
                    if st == (s0, t0):
                        break
                cs = np.concatenate([[0], np.cumsum(exps)[:-1]])
                base = int(max(-cs))
                for z in eigen_basis(len(orb), 1):
                    U = np.zeros((8, 8, R), dtype=np.int64)
                    cur = z.copy()
                    for j, (s, t) in enumerate(orb):
                        U[idx[s], idx[t]] = ((p ** (base + int(cs[j]))) * cur) % q
                        cur = sig(cur)
                    basis.append(U)
        B = np.array(basis)
        assert B.shape[0] == 64 and rank_mod_p(B.reshape(64, -1)) == 64
        for U in B:  # F U = U F on the basis
            for b in labels:
                lhs = np.zeros((8, R), dtype=np.int64)
                for s in labels:
                    lhs[idx[pi[s]]] = (lhs[idx[pi[s]]] + (p ** a[s]) * sig(U[idx[s], idx[b]])) % q
                rhs = ((p ** a[b]) * U[:, idx[pi[b]]]) % q
                assert ((lhs - rhs) % q == 0).all(), "not an endomorphism"
        return B

    def wedge22(u, v):
        out = np.zeros((70, R), dtype=np.int64)
        for I in subs[2]:
            for J in subs[2]:
                if set(I) & set(J):
                    continue
                K = tuple(sorted(I + J, key=lambda s: idx[s]))
                sg = perm_sign([idx[x] for x in I + J])
                out[sidx[4][K]] = (out[sidx[4][K]] + sg * mul(u[sidx[2][I]], v[sidx[2][J]])) % q
        return out

    def wedge4U(U, x):
        """(wedge^4 U)(x), x in wedge^4 M, U[s, t] = coefficient of e_s in U e_t."""
        out = np.zeros((70, R), dtype=np.int64)
        rows = [[idx[s] for s in J] for J in subs[4]]
        for K in subs[4]:
            xk = x[sidx[4][K]]
            if not xk.any():
                continue
            cols = [idx[s] for s in K]
            sub = U[np.ix_(range(8), cols)]
            Ms = np.moveaxis(np.stack([sub[r] for r in rows], axis=0), 0, 2)  # 4 x 4 x 70 x R
            d = np.zeros((70, R), dtype=np.int64)
            for perm in it.permutations(range(4)):
                term = Ms[0, perm[0]]
                for i in range(1, 4):
                    term = mul(term, Ms[i, perm[i]])
                d = (d + perm_sign(perm) * term) % q
            out = (out + mul(d, xk[None])) % q
        return out

    def colength(gens):
        """W-colength of the span of gens in W^70 modulo p^N; asserts full rank."""
        A = np.array(gens) % q
        total = 0
        for c in range(A.shape[1]):
            v = val(A[:, c])
            r = int(np.argmin(v))
            vr = int(v[r])
            assert vr < N, "rank deficiency or precision loss at column %d" % c
            total += vr
            piv = A[r].copy()
            u = (piv[c] // (p ** vr)) % q
            piv = mul(piv, inv(u)[None]) % q
            others = np.delete(A, r, axis=0)
            e = others[:, c] // (p ** vr)
            others = (others - mul(e[:, None, :], piv[None])) % q
            assert not (others[:, c] % q).any()
            # over W/p^N the multiples of the pivot row with zero entry in column c are p^(N - vr) piv, and they stay generators
            if vr:
                others = np.vstack([others, ((p ** (N - vr)) * piv)[None] % q])
            A = others
        return total

    T2 = tate_basis(2)
    T4 = tate_basis(4)
    End = end_basis()
    # x ^ x is not zero for 2-forms, so the squares are needed
    S = [wedge22(T2[i], T2[j]) for i in range(28) for j in range(i, 28)]
    sets = {"T+": ("000", "011", "101", "110"), "T-": ("001", "010", "100", "111"), "M+": ("000", "001", "011", "101"), "M-": ("010", "100", "110", "111")}

    def supported(B, names):
        ids = [sidx[4][tuple(sorted(sets[nm], key=lambda s: idx[s]))] for nm in names]
        return [v for v in B if all(not v[i].any() for i in range(70) if i not in ids) and any(v[i].any() for i in ids)]

    L = supported(T4, ["T+", "T-"])
    Nl = supported(T4, ["M+", "M-"])
    assert len(L) == 2 and len(Nl) == 2
    c_T = colength(list(T4))

    def rand_end():
        U = np.zeros_like(End[0])
        for c, B in zip(rng.integers(0, q, size=64), End):
            U = (U + int(c) * B) % q
        return U

    # a random element of L outside pL, which Theorem 5.2 needs
    c = rng.integers(0, q, size=2)
    while not (c % p).any():
        c = rng.integers(0, q, size=2)
    w = (int(c[0]) * L[0] + int(c[1]) * L[1]) % q
    imgs_w, imgs_N = [], []
    for _ in range(NS):
        U = rand_end()
        imgs_w.append(wedge4U(U, w))
        imgs_N.append(wedge4U(U, Nl[0]))
        imgs_N.append(wedge4U(U, Nl[1]))
    imgs_S = []
    for _ in range(max(NS // 4, 5)):
        U = rand_end()
        i, j = rng.integers(0, len(S), size=2)
        imgs_S.append(wedge4U(U, S[i]))
        imgs_S.append(wedge4U(U, (S[i] + 3 * S[j]) % q))
    res = {
        "[T^4 : S]": colength(S) - c_T,
        "[T^4 : S + End^* S] (sampled U)": colength(S + imgs_S) - c_T,
        "[T^4 : S + L]": colength(S + L) - c_T,
        "[T^4 : S + End^* w] (w in L outside pL, sampled U)": colength(S + [w] + imgs_w) - c_T,
        "[T^4 : S + N]": colength(S + Nl) - c_T,
        "[T^4 : S + N + End^* N] (sampled U)": colength(S + Nl + imgs_N) - c_T,
    }
    print("p = %d, modulo p^%d, %d random endomorphisms: bases of T^2, T^4, End(M, F) built and checked;" % (p, N, NS), "; ".join("%s = p^%d" % kv for kv in res.items()))
    assert list(res.values()) == [4, 4, 2, 0, 2, 2]


for p in (5, 13, 17):
    run(p, 7, 12, 0)
print("all assertions passed")
