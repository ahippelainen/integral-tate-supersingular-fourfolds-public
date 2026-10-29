"""Independent recomputation of Proposition 4.3 at p = 5 and p = 7 with integer matrices, without the min-plus formula.

F = Pi sigma with Pi the integer matrix of the model (1.2) built from Kronecker products. On wedge^k M the lattice T^k (x) W is the intersection of the phi^j(wedge^k M), phi = p^{-k/2} wedge^k Pi, j = 0, ..., 5 (proof of Lemma 2.1); it is computed through its dual lattice by Hermite normal form in PARI. S is spanned by all products x ^ y of basis vectors x, y of T^2, squares included, and T^4/S is read off from the Smith normal form.
"""
from itertools import combinations
import cypari2

pari = cypari2.Pari()
pari.allocatemem(2 * 10 ** 8, silent=True)


def kron(X, Y):
    r1, c1, r2, c2 = X.nrows(), X.ncols(), Y.nrows(), Y.ncols()
    Z = pari.matrix(r1 * r2, c1 * c2, [0] * (r1 * r2 * c1 * c2))
    for i in range(r1):
        for j in range(c1):
            for k in range(r2):
                for l in range(c2):
                    Z[i * r2 + k, j * c2 + l] = X[i, j] * Y[k, l]
    return Z


def run(p):
    A = pari.matrix(2, 2, [0, p, 1, 0])
    I2 = pari.matid(2)
    P = pari.matrix(8, 8, [0] * 64)  # x1 (x) x2 (x) x3 -> x3 (x) x1 (x) x2 on the basis e_{abc}, index 4a + 2b + c
    for a in range(2):
        for b in range(2):
            for c in range(2):
                P[4 * c + 2 * a + b, 4 * a + 2 * b + c] = 1
    Pi = P * kron(kron(A, I2), I2)
    assert Pi ** 6 == p ** 3 * pari.matid(8)

    def wedge(M, k):
        subs = list(combinations(range(8), k))
        W = pari.matrix(len(subs), len(subs), [0] * len(subs) ** 2)
        for j, J in enumerate(subs):
            for i, I in enumerate(subs):
                W[i, j] = pari.matdet(pari.matrix(k, k, [M[r, c] for r in I for c in J]))
        return W, subs

    def tate_lattice(k):
        Wk, subs = wedge(Pi, k)
        n = len(subs)
        phi_inv = p ** (k // 2) * Wk ** -1
        gens, X = [], pari.matid(n)
        for _ in range(6):
            gens.append(X.mattranspose())
            X = phi_inv * X
        assert X == pari.matid(n)
        G = pari.matconcat(gens)
        den = pari.denominator(G)
        Ldual = pari.mathnf(den * G) / den
        return (Ldual ** -1).mattranspose(), subs

    L2, s2 = tate_lattice(2)
    L4, s4 = tate_lattice(4)
    idx4 = {S: i for i, S in enumerate(s4)}

    def wedge_vec(x, y):
        v = [0] * 70
        for i, I in enumerate(s2):
            if x[i] == 0:
                continue
            for j, J in enumerate(s2):
                if y[j] == 0 or set(I) & set(J):
                    continue
                seq = list(I + J)
                sgn = (-1) ** sum(1 for a in range(4) for b in range(a + 1, 4) if seq[a] > seq[b])
                v[idx4[tuple(sorted(seq))]] += sgn * x[i] * y[j]
        return v

    cols = []
    for a in range(28):
        for b in range(a, 28):
            cols.append(wedge_vec([L2[r, a] for r in range(28)], [L2[r, b] for r in range(28)]))
    G = pari.matrix(70, len(cols), [cols[j][i] for i in range(70) for j in range(len(cols))])
    den = pari.denominator(G)
    Sb = pari.mathnf(den * G) / den
    coords = L4 ** -1 * Sb
    assert pari.denominator(coords) == 1
    ed = [int(x) for x in pari.matsnf(coords) if int(x) != 1]
    print(f"p = {p}: rank S = {pari.matrank(Sb)}, elementary divisors of T^4/S: {ed}")
    assert pari.matrank(Sb) == 70 and ed == [p] * 4


for p in (5, 7):
    run(p)
print("all assertions passed")
