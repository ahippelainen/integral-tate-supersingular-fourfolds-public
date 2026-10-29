"""Min-plus calculus for monomial Dieudonné modules (Section 2.2 of the note).

A monomial module has a basis (e_b) indexed by labels b and F e_b = ±p^{a(b)} e_{pi(b)}. Every lattice the note uses is monomial over W, so it is stored as a dict mapping a basis element of the relevant exterior power (a frozenset of labels, or a pair of them for the Künneth (2,2)-component of a square) to the exponent of p at that element. Exponents come from the orbit rule (2.2) and from minima over products and over values of polarized forms; signs never change an exponent and are not tracked.
"""
import itertools as it

BIG = 10 ** 9


def orbit_exponents(items, step, weight, target):
    """Smallest exponents n with n(step K) = n(K) + weight(K) - target along every orbit of step, normalized to minimum 0 on each orbit. This is the orbit rule (2.2) for the F-fixed lattice of p^{-target} F."""
    n, seen = {}, set()
    for K0 in items:
        if K0 in seen:
            continue
        orb, K = [], K0
        while True:
            orb.append(K)
            seen.add(K)
            K = step(K)
            if K == K0:
                break
        c, cs = 0, []
        for K in orb:
            cs.append(c)
            c += weight(K) - target
        assert c == 0, ("orbit not of slope zero", orb)
        base = -min(cs)
        for K, x in zip(orb, cs):
            n[K] = base + x
    return n


class Module:
    def __init__(self, labels, pi, a, name):
        self.L, self.pi, self.a, self.name = list(labels), pi, a, name
        self.all = frozenset(self.L)
        self.sub = {k: [frozenset(c) for c in it.combinations(self.L, k)] for k in (2, 4, 6)}
        self.n = {k: orbit_exponents(self.sub[k], self.step, self.weight, k // 2) for k in (2, 4, 6)}
        self.S = {}
        for I, J in it.combinations(self.sub[2], 2):
            if not I & J:
                K = I | J
                self.S[K] = min(self.S.get(K, BIG), self.n[2][I] + self.n[2][J])
        self._Shat = None

    @classmethod
    def from_words(cls, words):
        """Direct sum of the modules of the binary words: basis e_(c,i), F e_(c,i) = p^{w_c[i]} e_(c,i+1)."""
        labels, pi, a = [], {}, {}
        for c, w in enumerate(words):
            for i, x in enumerate(w):
                labels.append((c, i))
                pi[(c, i)] = (c, (i + 1) % len(w))
                a[(c, i)] = int(x)
        return cls(labels, pi, a, "+".join(words))

    def step(self, K):
        return frozenset(self.pi[x] for x in K)

    def weight(self, K):
        return sum(self.a[x] for x in K)

    def orbits(self):
        out, seen = [], set()
        for b in self.L:
            if b not in seen:
                o, x = [], b
                while x not in o:
                    o.append(x)
                    seen.add(x)
                    x = self.pi[x]
                out.append(o)
        return out

    def S6(self):
        """Exponents of the span of products of three classes in T^2."""
        out = {}
        for I in self.sub[2]:
            for K, v in self.S.items():
                if not I & K:
                    out[I | K] = min(out.get(I | K, BIG), self.n[2][I] + v)
        return out

    @property
    def Shat(self):
        """Exponents of S-hat (9.1): minimum of n6(J') + n6(J'') over 6-sets with J' cap J'' = J and J' cup J'' = everything."""
        if self._Shat is None:
            out = {}
            for K in self.sub[4]:
                rest = sorted(self.all - K)
                out[K] = min(self.n[6][K | frozenset(I)] + self.n[6][self.all - frozenset(I)] for I in it.combinations(rest, 2))
            self._Shat = out
        return self._Shat

    def anumber(self):
        """dim M/(FM + VM): e_b lies outside FM + VM modulo p exactly when a(pi^{-1} b) = 1 and a(b) = 0."""
        inv = {v: k for k, v in self.pi.items()}
        return sum(1 for b in self.L if self.a[inv[b]] == 1 and self.a[b] == 0)

    def kerF(self):
        """Labels b with e_b in ker(F mod p)."""
        return frozenset(b for b in self.L if self.a[b] == 1)

    def index(self, *lattices):
        """log_p [T^4 : sum of the lattices]; asserts that every lattice lies in T^4 and that the sum has full rank."""
        tot = 0
        for K, nk in self.n[4].items():
            g = min(lat.get(K, BIG) for lat in lattices)
            assert nk <= g < BIG, (self.name, sorted(K), g, nk)
            tot += g - nk
        return tot


def hom_exponents(X, Y):
    """Exponents of Hom_F(M_X, M_Y) (x) W on the matrix units E_{y,x}: e_x -> e_y."""
    pairs = [(y, x) for y in Y.L for x in X.L]
    return orbit_exponents(pairs, lambda yx: (Y.pi[yx[0]], X.pi[yx[1]]), lambda yx: Y.a[yx[0]] - X.a[yx[1]], 0)


_minors = {}


def minor_exponents(X, Y):
    """For u in Hom_F(M_X, M_Y), the exponent of the monomial span of the 4x4 minors with rows R (4-set of Y) and columns C (4-set of X): the minimum over bijections C -> R of the sum of the exponents of u. By polarization (4! a unit) this is the exponent of the span over all u."""
    key = (id(X), id(Y))
    if key not in _minors:
        m = hom_exponents(X, Y)
        tab = {}
        for R in Y.sub[4]:
            rs = tuple(R)
            for C in X.sub[4]:
                tab[R, C] = min(sum(m[r, c] for r, c in zip(rs, perm)) for perm in it.permutations(tuple(C)))
        _minors[key] = (tab, X, Y)
    return _minors[key][0]


def merge(*lattices):
    out = {}
    for lat in lattices:
        for K, v in lat.items():
            if v < out.get(K, BIG):
                out[K] = v
    return out


def pullback(X, Z, src):
    """Span on H^4 of X of g^*(src) over all homomorphisms g: X -> Z; g^* on H^1 is u in Hom_F(M_Z, M_X) and acts on H^4 by the 4x4 minors of u."""
    tab = minor_exponents(Z, X)
    return {J: min(e + tab[J, K] for K, e in src.items()) for J in X.sub[4]}


def pushforward(X, Y, src):
    """Span on H^4 of X of f_*(src) over all homomorphisms f: Y -> X. By Poincaré duality the entry of f_* from e_J to e_I is the minor of f^* with rows Y - J and columns X - I."""
    tab = minor_exponents(X, Y)
    return {I: min(e + tab[Y.all - J, X.all - I] for J, e in src.items()) for I in X.sub[4]}


def end_closure(X, start, push=True):
    """Close a monomial lattice under End(X)^* and, if push, End(X)_*, iterating to the fixed point."""
    cur = dict(start)
    while True:
        new = merge(cur, pullback(X, X, cur), pushforward(X, X, cur) if push else {})
        if new == cur:
            return cur
        cur = new


def kunneth22(X, src=None):
    """Künneth (2,2)-component of H^4 of X x X. Returns (log_p [T_22 : S_22], log_p [T_22 : S_22 + PB(src)]), where S_22 is the (2,2)-component of S(X x X) and PB(src) the span of the (2,2)-components of (U_1, U_2)^* x, x in src, U_i in End(X)."""
    P2 = X.sub[2]
    blk = [(I, J) for I in P2 for J in P2]
    nb = orbit_exponents(blk, lambda IJ: (X.step(IJ[0]), X.step(IJ[1])), lambda IJ: X.weight(IJ[0]) + X.weight(IJ[1]), 2)
    pairs = [(i, j) for i in X.L for j in X.L]
    n11 = orbit_exponents(pairs, lambda ij: (X.pi[ij[0]], X.pi[ij[1]]), lambda ij: X.a[ij[0]] + X.a[ij[1]], 1)
    s22 = {(I, J): X.n[2][I] + X.n[2][J] for I, J in blk}
    for (i, j), (k, l) in it.combinations(pairs, 2):
        if i != k and j != l:
            key = (frozenset((i, k)), frozenset((j, l)))
            s22[key] = min(s22[key], n11[i, j] + n11[k, l])

    def idx(*lats):
        tot = 0
        for key, nk in nb.items():
            g = min(lat.get(key, BIG) for lat in lats)
            assert nk <= g < BIG
            tot += g - nk
        return tot

    out = [idx(s22)]
    if src is not None:
        m = hom_exponents(X, X)
        cost = {}
        for I in P2:
            for A in P2:
                cost[I, A] = min(m[t1, a0] + m[t2, a1] for (a0, a1) in [tuple(A)] for t1, t2 in it.permutations(tuple(I)))
        pb = {}
        for K, e in src.items():
            for A in it.combinations(tuple(K), 2):
                A = frozenset(A)
                B = K - A
                for I in P2:
                    for J in P2:
                        v = e + cost[I, A] + cost[J, B]
                        if v < pb.get((I, J), BIG):
                            pb[I, J] = v
        out.append(idx(s22, pb))
    return out
