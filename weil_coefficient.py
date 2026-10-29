"""Check of Lemma 7.4 through the cohomological Fourier-Mukai transform of Orlov's equivalence, for d = 4, 6, 8, 10, 12, 28.

X_3 is a principally polarized abelian threefold with symplectic basis alpha_i, beta_i of H^1(X_3, Z) (generators 0..5, int alpha_0 beta_0 alpha_1 beta_1 alpha_2 beta_2 = 1). The image of ch(I_1) x ch(I_1), ch(I_1) = 1 + Theta - (d/2) Theta^2 - d [pt], under the transform is computed exactly in the exterior algebra over Q(sqrt(-d)) on integral bases of H^1(X_3) and H^1(X_3^dual) (generators 0..5 and 6..11 of the output), normalized by exp(-c_1/rk), and its degree-6 part kappa_3 is decomposed by K_d-types. Gamma_1 is found as the annihilator of the decomposable degree-6 part of the image of rho_1 x rho_2, eta is the operator that is sqrt(-d) on Gamma_1 and -sqrt(-d) on its conjugate, and the type (i, j) of a class is read off from the derivation induced by eta, which acts by sqrt(-d)(i - j). The same decomposition of the degree-6 part of ch itself, before the normalization, shows the claim at the end of the first paragraph of the proof of Lemma 7.4 that it has components of every type.
"""
from fractions import Fraction as Fr
from math import gcd

D = None  # Markman's d; s^2 = -d


class K:
    """Element a + b s of Q(s), s^2 = -D."""
    __slots__ = ("a", "b")

    def __init__(self, a=0, b=0):
        self.a, self.b = Fr(a), Fr(b)

    def __add__(self, o):
        o = kk(o)
        return K(self.a + o.a, self.b + o.b)
    __radd__ = __add__

    def __neg__(self):
        return K(-self.a, -self.b)

    def __sub__(self, o):
        return self + (-kk(o))

    def __rsub__(self, o):
        return kk(o) - self

    def __mul__(self, o):
        o = kk(o)
        return K(self.a * o.a - D * self.b * o.b, self.a * o.b + self.b * o.a)
    __rmul__ = __mul__

    def conj(self):
        return K(self.a, -self.b)

    def inv(self):
        n = self.a * self.a + D * self.b * self.b
        return K(self.a / n, -self.b / n)

    def __truediv__(self, o):
        return self * kk(o).inv()

    def iszero(self):
        return self.a == 0 and self.b == 0


def kk(x):
    return x if isinstance(x, K) else K(x)


S = K(0, 1)


def nz(c):
    return not (c.iszero() if isinstance(c, K) else c == 0)


def msign(m1, m2):
    """Sign of e_{m1} ^ e_{m2} = sign e_{m1 | m2} for bit masks of generators, 0 if they overlap."""
    if m1 & m2:
        return 0
    c, m = 0, m2
    while m:
        j = (m & -m).bit_length() - 1
        c += bin(m1 >> (j + 1)).count("1")
        m &= m - 1
    return -1 if c & 1 else 1


def mul(x, y):
    r = {}
    for m1, c1 in x.items():
        for m2, c2 in y.items():
            sg = msign(m1, m2)
            if sg:
                r[m1 | m2] = r.get(m1 | m2, 0) + sg * c1 * c2
    return {m: c for m, c in r.items() if nz(c)}


def add(x, y, cy=1):
    r = dict(x)
    for m, c in y.items():
        r[m] = r.get(m, 0) + cy * c
    return {m: c for m, c in r.items() if nz(c)}


def deg(x, k):
    return {m: c for m, c in x.items() if bin(m).count("1") == k}


def gen(i, c=1):
    return {1 << i: c}


def scal(c):
    return {0: c}


def linsub(x, img):
    """Ring endomorphism of the exterior algebra sending generator j to the 1-form img[j]."""
    r = {}
    for m, c in x.items():
        t, mm = scal(c), m
        while mm:
            j = (mm & -mm).bit_length() - 1
            t = mul(t, img[j])
            mm &= mm - 1
        r = add(r, t)
    return r


def expo(x, top=6):
    r, t = scal(1), scal(1)
    for k in range(1, top + 1):
        t = {m: c / k for m, c in mul(t, x).items()}
        r = add(r, t)
    return r


def shift(x, off):
    return {m << off: c for m, c in x.items()}


def orlov(c1, c2):
    """ch Phi(F_1 x F_2) from ch F_1 = c1, ch F_2 = c2 on X_3 (generators 0..5); output on X_3 x X_3^dual (generators 0..5 and 6..11)."""
    x = mul(c1, shift(c2, 6))
    x = linsub(x, {**{j: add(gen(j), gen(6 + j), -1) for j in range(6)}, **{6 + j: gen(6 + j) for j in range(6)}})  # mu_* = (mu^{-1})^*, mu^{-1}(x, y) = (x - y, y)
    x = linsub(x, {**{j: gen(j) for j in range(6)}, **{6 + j: gen(6 + j, -1) for j in range(6)}})  # (-1)^* on the second factor
    P = scal(1)
    for j in range(6):
        P = mul(P, add(scal(1), mul(gen(6 + j), gen(12 + j))))  # exp c_1(P) on X_3 x X_3^dual, c_1(P) = sum e_j ^ ehat_j
    x = mul(x, P)
    fib = 0b111111 << 6
    r = {}
    for m, c in x.items():
        if m & fib == fib:
            mm = (m & 0b111111) | ((m >> 12) << 6)
            r[mm] = r.get(mm, 0) - c  # integrate over the middle factor; the shift [3] gives the sign
    return {m: c for m, c in r.items() if nz(c)}


def nullspace(rows, n):
    piv, R = [], []
    for rw in rows:
        rw = [kk(v) for v in rw]
        for pc, prow in zip(piv, R):
            if not rw[pc].iszero():
                f = rw[pc]
                rw = [a - f * b for a, b in zip(rw, prow)]
        nzs = [i for i in range(n) if not rw[i].iszero()]
        if not nzs:
            continue
        pc = nzs[0]
        f = rw[pc].inv()
        rw = [a * f for a in rw]
        for i, prow in enumerate(R):
            if not prow[pc].iszero():
                g = prow[pc]
                R[i] = [a - g * b for a, b in zip(prow, rw)]
        piv.append(pc)
        R.append(rw)
    basis = []
    for fcol in (i for i in range(n) if i not in piv):
        v = [K(0)] * n
        v[fcol] = K(1)
        for pc, prow in zip(piv, R):
            v[pc] = -prow[fcol]
        basis.append(v)
    return basis


def annihilator(om):
    """{v in H^1 (x) K_d : v ^ om = 0}."""
    eqs = {}
    for j in range(12):
        for m, c in mul(gen(j, K(1)), om).items():
            eqs.setdefault(m, [K(0)] * 12)[j] += c
    return nullspace(list(eqs.values()), 12)


def matinv(M):
    n = len(M)
    A = [row[:] + [K(1) if i == j else K(0) for j in range(n)] for i, row in enumerate(M)]
    for c in range(n):
        p = next(i for i in range(c, n) if not A[i][c].iszero())
        A[c], A[p] = A[p], A[c]
        f = A[c][c].inv()
        A[c] = [x * f for x in A[c]]
        for i in range(n):
            if i != c and not A[i][c].iszero():
                g = A[i][c]
                A[i] = [x - g * y for x, y in zip(A[i], A[c])]
    return [row[n:] for row in A]


def derive(x, A):
    """The derivation of the exterior algebra extending the linear map A (column j = image of generator j)."""
    img = {j: {1 << i: A[i][j] for i in range(12) if A[i][j] != 0} for j in range(12)}
    r = {}
    for m, c in x.items():
        bits = [j for j in range(12) if m >> j & 1]
        for t, j in enumerate(bits):
            left = sum(1 << q for q in bits[:t])
            right = sum(1 << q for q in bits[t + 1:])
            r = add(r, mul(mul({left: c}, img[j]), {right: 1}))
    return r


def egcd(a, b):
    if b == 0:
        return (abs(a), 1 if a >= 0 else -1, 0)
    g, x, y = egcd(b, a % b)
    return g, y, x - (a // b) * y


def rgcd(xs):
    """gcd of rationals."""
    den = 1
    for x in xs:
        den = den * x.denominator // gcd(den, x.denominator)
    num = 0
    for x in xs:
        num = gcd(num, int(x * den))
    return Fr(num, den)


def content_in_weil_lattice(w, w2):
    """Content of w in B = (Q w + Q w2) cap H^6(Z), by Hermite normal form: B is dual to the Z-span L' of the coefficient pairs (w_m, w2_m)."""
    keys = sorted(set(w) | set(w2))
    vs = [(w.get(m, Fr(0)), w2.get(m, Fr(0))) for m in keys]
    L = 1
    for a, b in vs:
        for x in (a, b):
            L = L * x.denominator // gcd(L, x.denominator)
    g, y, h = 0, 0, 0
    for a, b in ((int(a * L), int(b * L)) for a, b in vs):
        if a == 0:
            h = gcd(h, b)
            continue
        G, u, v = egcd(g, a)
        h = gcd(h, (a // G) * y - (g // G) * b)
        g, y = G, u * y + v * b
    y = y % h if h else y
    a11, a12, a22 = Fr(g, L), Fr(y, L), Fr(h, L)  # L' has basis (a11, a12), (0, a22)
    det = a11 * a22
    (p, q), (r, t) = (a22 / det, -a12 / det), (Fr(0), a11 / det)  # dual basis of B
    dd = p * t - q * r
    c1, c2 = t / dd, -q / dd  # w = (1, 0) = c1 (p, q) + c2 (r, t)
    return rgcd([c1, c2])


def types(x, eta, d):
    """The K_d-types (i, 6 - i) at which the degree-6 class x has a non-zero component. The derivation D of eta acts on type (i, 6 - i) by k sqrt(-d), k = 2i - 6, so a polynomial in D^2 projects onto k^2, and (y + D y / (k sqrt(-d)))/2 separates k from -k."""
    out = set()
    for k in range(-6, 7, 2):
        y = dict(x)
        for k2 in {0, 4, 16, 36} - {k * k}:
            y = {m: c / (d * (k2 - k * k)) for m, c in add(derive(derive(y, eta), eta), y, d * k2).items()}
        if k:
            sk = (S * k).inv()
            y = {m: c / 2 for m, c in add(y, {m: c * sk for m, c in derive(y, eta).items()}).items()}
        if y:
            out.add(((k + 6) // 2, (6 - k) // 2))
    return out


def top(x):
    return x.get((1 << 12) - 1, 0)


def run(d):
    global D
    D = d
    TH = add(add(mul(gen(0), gen(1)), mul(gen(2), gen(3))), mul(gen(4), gen(5)))
    assert mul(mul(TH, TH), TH) == {0b111111: Fr(6)}
    chI = add(add(add(scal(Fr(1)), TH), mul(TH, TH), Fr(-d, 2)), {0b111111: Fr(1)}, -d)
    ch = orlov(chI, chI)
    r = ch.get(0, 0)
    kap = mul(expo({m: -c / r for m, c in deg(ch, 2).items()}), ch)
    k3 = deg(kap, 6)
    assert r == 8 * d

    rho1 = expo({m: c * S for m, c in TH.items()}, 3)
    rho2 = expo({m: c * (-S) for m, c in TH.items()}, 3)
    assert len(annihilator(deg(orlov(rho1, rho1), 6))) == 0
    om = orlov(rho1, rho2)
    assert all(not deg(om, k) for k in range(6))
    G1 = annihilator(deg(om, 6))
    assert len(G1) == 6
    cols = G1 + [[c.conj() for c in v] for v in G1]
    Pm = [[cols[j][i] for j in range(12)] for i in range(12)]
    Pi = matinv(Pm)
    eta = [[S * sum((Pm[i][k] * (1 if k < 6 else -1) * Pi[k][j] for k in range(12)), K(0)) for j in range(12)] for i in range(12)]
    assert all(e.b == 0 and e.a.denominator == 1 for row in eta for e in row)  # eta is defined over Z
    eta = [[e.a for e in row] for row in eta]
    assert all(sum(eta[i][k] * eta[k][j] for k in range(12)) == (-d if i == j else 0) for i in range(12) for j in range(12))
    pairV = lambda u, v: sum((u[j] * v[6 + j] + u[6 + j] * v[j] for j in range(6)), K(0))
    assert all(pairV(u, v).iszero() for u in G1 for v in G1)  # Gamma_1 is isotropic

    dk = derive(k3, eta)
    d2k = derive(dk, eta)
    d3k = derive(d2k, eta)
    only = add(d3k, dk, 36 * d) == {}  # the derivation satisfies D^3 = -36 d D only if i - j is 0 or +-6
    w = {m: -c / (36 * d) for m, c in d2k.items()}  # the component of types (6,0) + (0,6)
    k33 = add(k3, w, -1)
    hform = {}
    for j in range(12):
        hform = add(hform, mul({1 << i: eta[i][j] / 2 for i in range(12) if eta[i][j] != 0}, gen(6 + j if j < 6 else j - 6)))
    h3 = mul(mul(hform, hform), hform)
    m0 = next(iter(h3))
    lam = k33.get(m0, 0) / h3[m0]
    assert add(k33, h3, -lam) == {}  # the (3,3)-component is a multiple of h^3
    cont = content_in_weil_lattice(w, derive(w, eta))
    assert cont == rgcd(list(w.values()))
    assert all(c.denominator == 1 for c in hform.values()) and rgcd(list(hform.values())) == 1
    pf = top(mul(mul(mul(hform, hform), mul(hform, hform)), mul(hform, hform))) / 720
    print(f"d = {d}: rank {r}; only types (6,0), (0,6), (3,3): {only}; (3,3)-component = {lam} h^3; content of the Weil component {cont}, (d+1)/(2d) = {Fr(d + 1, 2 * d)}; Pfaffian of h {pf}")
    assert only and cont == Fr(d + 1, 2 * d) and abs(pf) == d ** 3
    tch, tk = types(deg(ch, 6), eta, d), types(k3, eta, d)
    print(f"d = {d}: K_d-types of the degree-6 part of ch: {sorted(tch, reverse=True)}; of kappa_3: {sorted(tk, reverse=True)}")
    assert tch == {(i, 6 - i) for i in range(7)} and tk == {(6, 0), (3, 3), (0, 6)}


for d in (4, 6, 8, 10, 12, 28):
    run(d)
print("all assertions passed")
