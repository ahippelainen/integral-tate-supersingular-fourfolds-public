"""Independent recomputation of Lemma 7.4 for d = 4, 6, 8, 10, 12, 28 through the spinor formulas of Markman's preprint arXiv:2502.03415 that the proof of Lemma 7.4 uses, sharing no code with weil_coefficient.py.

ch Phi(I_2 x I_1) = phi'(ch I_1 (x) tau ch I_1) with phi' = (phi_P (x) psi_{P^-1}[n]) o phi-tilde and phi-tilde(s (x) t) = psi(s [pt_X^dual] tau(t)), where the Clifford action is psi'(e_i) = L_{e_i} + delta_{e_i}, psi'(f_i) = L_{f_i}. Then kappa = exp(-c_1/r) ch, and kappa_3 is written in the basis w_i = f_i - sqrt(-d) Theta^sharp(f_i) of Gamma_1 and its conjugate. e_0..e_5 is a basis of H^1(X_3, Z) with Theta = sum e_i ^ e_{i+3}, f_0..f_5 the dual basis of H^1(X_3^dual, Z). Coefficients in Q(sqrt(-d)) are pairs (a, b) = a + b sqrt(-d).
"""
from math import gcd
from fractions import Fraction as Fr

N = 3
NE = 2 * N            # e_0..e_5 basis of H^1(X), f_0..f_5 dual basis of H^1(X^) at bit positions 6..11
DIM = 2 * NE
D = None              # sqrt(-d)^2 = -D


def kmul(x, y):
    return (x[0] * y[0] - D * x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def kadd(x, y):
    return (x[0] + y[0], x[1] + y[1])


ZERO, ONE, SQ = (Fr(0), Fr(0)), (Fr(1), Fr(0)), (Fr(0), Fr(1))


def kscal(c, x):
    return (c * x[0], c * x[1])


def kinv(x):
    n = x[0] * x[0] + D * x[1] * x[1]
    return (x[0] / n, -x[1] / n)


def acc(out, m, c):
    v = kadd(out.get(m, ZERO), c)
    if v == ZERO:
        out.pop(m, None)
    else:
        out[m] = v


def sign_insert(i, m):
    """Sign of moving basis vector i to its sorted place in monomial m (vector i placed in front)."""
    return -1 if bin(m & ((1 << i) - 1)).count("1") % 2 else 1


def wedge_vec(i, x):
    """L_{v_i}(x) = v_i ^ x."""
    out = {}
    for m, c in x.items():
        if not m >> i & 1:
            acc(out, m | 1 << i, kscal(sign_insert(i, m), c))
    return out


def contract(i, x):
    """Anti-derivation removing v_i: delta(v_i ^ rest) = rest."""
    out = {}
    for m, c in x.items():
        if m >> i & 1:
            acc(out, m & ~(1 << i), kscal(sign_insert(i, m), c))
    return out


def wedge(x, y):
    out = {}
    for m1, c1 in x.items():
        for m2, c2 in y.items():
            if m1 & m2:
                continue
            s, mm = 1, m1
            for i in range(DIM):          # insert bits of m2 in increasing order: v_{m1} ^ v_{m2}
                if m2 >> i & 1:
                    # moving v_i past the bits of mm that are > i (they sit to its right in sorted order)
                    if bin(mm >> (i + 1)).count("1") % 2:
                        s = -s
                    mm |= 1 << i
            acc(out, mm, kscal(s, kmul(c1, c2)))
    return out


def deg(m):
    return bin(m).count("1")


def part(x, k):
    return {m: c for m, c in x.items() if deg(m) == k}


def eps(K, Kc):
    """e_K ^ e_Kc = eps e_{all}, K, Kc sorted index tuples."""
    seq = list(K) + list(Kc)
    s = 1
    for a in range(len(seq)):
        for b in range(a + 1, len(seq)):
            if seq[a] > seq[b]:
                s = -s
    return s


def tau(x):
    return {m: kscal(-1 if (deg(m) * (deg(m) - 1) // 2) % 2 else 1, c) for m, c in x.items()}


def phi_tilde(s, t):
    """psi(s [pt_X^] tau(t)), s, t in Lambda H^1(X) (bits 0..5)."""
    out = {}
    pt_hat = (1 << DIM) - (1 << NE)
    for ms, cs in s.items():
        for mt, ct in tau(t).items():
            if pt_hat & mt:
                continue
            # psi'(f_0..f_5) psi'(tau t).1 = f_0^..^f_5 ^ e_{mt}
            y = wedge({sum(1 << (NE + i) for i in range(NE)): ONE}, {mt: ONE})
            for i in sorted((i for i in range(NE) if ms >> i & 1), reverse=True):   # s = e_{i1}...e_{ik}: rightmost acts first
                a = wedge_vec(i, y)
                b = contract(NE + i, y)      # delta_{e_i} = contraction with B0(e_i, .) = f_i-coefficient
                y = dict(a)
                for m, c in b.items():
                    acc(y, m, c)
            for m, c in y.items():
                acc(out, m, kmul(kmul(cs, ct), c))
    return out


def pd_map(x):
    """(phi_P (x) psi_{P^-1}[n]) on monomials f_L ^ e_K."""
    out = {}
    full = tuple(range(NE))
    for m, c in x.items():
        K = tuple(i for i in range(NE) if m >> i & 1)
        L = tuple(i for i in range(NE) if m >> (NE + i) & 1)
        k, l = len(K), len(L)
        Kc = tuple(i for i in full if i not in K)
        Lc = tuple(i for i in full if i not in L)
        sgn_order = -1 if (k * l) % 2 else 1          # our monomial is e_K ^ f_L = (-1)^{kl} f_L ^ e_K
        s = sgn_order * (-1 if ((k * (k + 1) + l * (l + 1)) // 2) % 2 else 1) * eps(L, Lc) * eps(K, Kc)
        mo = sum(1 << i for i in Lc) | sum(1 << (NE + i) for i in Kc)   # e_{Lc} ^ f_{Kc}, already sorted e before f
        acc(out, mo, kscal(s, c))
    return out


def expo(x, kmax=6):
    out, term = {0: ONE}, {0: ONE}
    for j in range(1, kmax + 1):
        term = {m: kscal(Fr(1, j), c) for m, c in wedge(term, x).items()}
        for m, c in term.items():
            acc(out, m, c)
    return out


def kappa3(d):
    global D
    D = Fr(d)
    theta = {}
    for i in range(N):
        acc(theta, (1 << i) | (1 << (i + N)), ONE)
    th2 = wedge(theta, theta)
    pt = {m: kscal(Fr(1, 6), c) for m, c in wedge(th2, theta).items()}
    assert pt in ({(1 << NE) - 1: ONE}, {(1 << NE) - 1: (Fr(-1), Fr(0))})  # [pt] = Theta^3/6
    chF = {0: ONE}
    for x, cf in ((theta, Fr(1)), (th2, -D / 2), (pt, -D)):
        for m, c in x.items():
            acc(chF, m, kscal(cf, c))
    ch = pd_map(phi_tilde(chF, tau(chF)))
    r = ch.get(0, ZERO)
    c1 = part(ch, 2)
    kappa = wedge(expo({m: kscal(-1, kmul(c, kinv(r))) for m, c in c1.items()}), ch)
    return r, part(kappa, 6)


def run(d):
    r, k3 = kappa3(d)
    # w_j = f_j - sqrt(-d) theta(f_j), with theta(f_j) = s e_i the contraction of Theta with f_j
    th_f = {j: ((j + N, 1) if j < N else (j - N, -1)) for j in range(NE)}
    w, wb = {}, {}
    for j in range(NE):
        i, s = th_f[j]
        w[j] = {1 << (NE + j): ONE, 1 << i: kscal(-s, SQ)}
        wb[j] = {1 << (NE + j): ONE, 1 << i: kscal(s, SQ)}
    # kappa_3 in the basis w_0..w_5 (bits 0..5), wbar_0..wbar_5 (bits 6..11): f_j = (w_j + wbar_j)/2, e_i = s (wbar_j - w_j)/(2 sqrt(-d))
    inv2sq = kinv(kscal(2, SQ))
    img = {}
    for j in range(NE):
        img[NE + j] = {1 << j: (Fr(1, 2), Fr(0)), 1 << (NE + j): (Fr(1, 2), Fr(0))}
        i, s = th_f[j]
        img[i] = {1 << (NE + j): kscal(s, inv2sq), 1 << j: kscal(-s, inv2sq)}
    k3u = {}
    for m, c in k3.items():
        y = {0: ONE}
        for i in range(DIM):
            if m >> i & 1:
                y = wedge(y, img[i])
        for mm, cc in y.items():
            acc(k3u, mm, kmul(c, cc))
    types = sorted({(deg(m & ((1 << NE) - 1)), 6 - deg(m & ((1 << NE) - 1))) for m in k3u})
    c1, c2 = k3u.get((1 << NE) - 1, ZERO), k3u.get(((1 << NE) - 1) << NE, ZERO)

    # omega_1 = w_0 ^ ... ^ w_5, omega_2 its conjugate, Tr(omega_1) = omega_1 + omega_2 in H^6(Z)
    om1, om2 = {0: ONE}, {0: ONE}
    for j in range(NE):
        om1, om2 = wedge(om1, w[j]), wedge(om2, wb[j])
    tr1 = dict(om1)
    for m, c in om2.items():
        acc(tr1, m, c)
    assert all(c[1] == 0 and c[0].denominator == 1 for c in tr1.values())
    cont = 0
    for c in tr1.values():
        cont = gcd(cont, int(c[0]))

    # the (3,3)-part is a multiple of xi^3, xi the GL(Gamma_1)-invariant 2-form sum_i w_i ^ w*_i, w*_i the dual basis of Gamma_2 under the pairing (e_i, f_j) = delta_ij
    def pair(x, y):
        tot = ZERO
        for m1, a in x.items():
            for m2, b in y.items():
                i1, i2 = m1.bit_length() - 1, m2.bit_length() - 1
                if (i1 < NE and i2 == NE + i1) or (i2 < NE and i1 == NE + i2):
                    tot = kadd(tot, kmul(a, b))
        return tot
    xi = {}
    for i in range(NE):
        for j in range(NE):
            g = pair(w[i], wb[j])
            if g != ZERO:
                for m, c in wedge(w[i], {mm: kmul(cc, kinv(g)) for mm, cc in wb[j].items()}).items():
                    acc(xi, m, c)
    xi3 = wedge(wedge(xi, xi), xi)
    rest = dict(k3)
    for m, c in tr1.items():
        acc(rest, m, kscal(-1, kmul(c1, c)))
    m0 = next(iter(xi3))
    lam = kmul(rest.get(m0, ZERO), kinv(xi3[m0]))
    for m, c in xi3.items():
        acc(rest, m, kscal(-1, kmul(lam, c)))
    weil = abs(c1[0]) * cont
    print(f"d = {d}: rank {r[0]}; K_d-types of kappa_3 {types}; coefficients of omega_1, omega_2: {c1[0]}, {c2[0]}; kappa_3 - ({c1[0]}) Tr(omega_1) is a multiple of xi^3: {not rest}; content of Tr(omega_1) in H^6(Z): {cont}; content of the Weil component {weil}")
    assert r == (8 * d, 0) and types == [(0, 6), (3, 3), (6, 0)]
    assert c1 == c2 and c1[1] == 0 and abs(c1[0]) == Fr(d + 1, 4 * d)
    assert not rest and cont == 2 and weil == Fr(d + 1, 2 * d)


for d in (4, 6, 8, 10, 12, 28):
    run(d)
print("all assertions passed")
