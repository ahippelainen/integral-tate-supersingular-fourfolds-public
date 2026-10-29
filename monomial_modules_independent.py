"""Independent recomputation of Table 1, Proposition 9.3 and Remark 9.4 with separately written min-plus code that shares nothing with minplus.py and monomial_modules.py.

Basis e_0, ..., e_7 split into F-cycles, one per word, F e_i = p^{w_i} e_{pi(i)}. Exponents are computed with doubled values so that they stay integral before the final halving.
"""
import itertools as it

INF = 10 ** 9

# Table 1 of the note: module -> (a-number, self-dual, log_p [T^4 : S], log_p [T^4 : S + S-hat])
TABLE = {
    "01+01+01+01": (4, True, 0, 0), "01+01+0101": (4, True, 0, 0), "0101+0101": (4, True, 0, 0), "01+010101": (4, True, 0, 0), "01010101": (4, True, 0, 0),
    "01+01+0011": (3, True, 0, 0), "0011+0101": (3, True, 0, 0), "00101101": (3, True, 0, 0),
    "0011+0011": (2, True, 0, 0), "00110011": (2, True, 0, 0),
    "00001111": (1, True, 0, 0),
    "00110101": (3, False, 0, 0), "00101011": (3, False, 2, 0),
    "00011101": (2, False, 2, 0), "00010111": (2, False, 16, 0),
    "01+000111": (2, True, 4, 4),
    "01+001101": (3, False, 2, 2), "01+001011": (3, False, 10, 2),
    "00100111": (2, False, 26, 26), "00011011": (2, False, 26, 26),
}


def necklaces(n):
    seen, out = set(), []
    for bits in it.product("01", repeat=n):
        s = "".join(bits)
        if s.count("1") * 2 != n:
            continue
        r = min(s[i:] + s[:i] for i in range(n))
        if r not in seen:
            seen.add(r)
            out.append(r)
    return out


def decompositions():
    out = []
    for pt in ([8], [6, 2], [4, 4], [4, 2, 2], [2, 2, 2, 2]):
        combos = {tuple(sorted(c, key=lambda s: (len(s), s))) for c in it.product(*[necklaces(k) for k in pt])}
        out += sorted(combos)
    return out


class Mod:
    def __init__(self, words):
        self.words = words
        self.w, self.pi = [], []
        base = 0
        for wd in words:
            for j in range(len(wd)):
                self.w.append(int(wd[j]))
                self.pi.append(base + (j + 1) % len(wd))
            base += len(wd)
        self.inv = [0] * 8
        for i, j in enumerate(self.pi):
            self.inv[j] = i
        self.subsets = {k: [frozenset(c) for c in it.combinations(range(8), k)] for k in (2, 4, 6)}
        self.nexp = {k: {K: self._n(K, k) for K in self.subsets[k]} for k in (2, 4, 6)}

    def _n(self, K, k):
        best, acc, cur = 0, 0, K
        while True:
            cur = frozenset(self.inv[x] for x in cur)
            acc += 2 * sum(self.w[x] for x in cur) - k
            best = max(best, acc)
            if cur == K:
                assert acc == 0
                break
        assert best % 2 == 0
        return best // 2

    def a_number(self):
        return sum(1 for j in range(8) if self.w[self.inv[j]] == 1 and self.w[j] == 0)

    def S(self):
        n2 = self.nexp[2]
        return {K: min(n2[frozenset(I)] + n2[K - frozenset(I)] for I in it.combinations(sorted(K), 2)) for K in self.subsets[4]}

    def P(self):
        """S-hat: products of two classes of T^6 under the Pontryagin product."""
        n6, allset = self.nexp[6], frozenset(range(8))
        out = {}
        for K in self.subsets[4]:
            C = sorted(allset - K)
            out[K] = min(n6[K | frozenset(A)] + n6[K | (frozenset(C) - frozenset(A))] for A in it.combinations(C, 2))
        return out

    def endexp(self):
        return homexp(self, self)

    def pull(self, lat, m):
        out = dict(lat)
        for K, x in lat.items():
            if x >= INF:
                continue
            Kl = sorted(K)
            for Kp in self.subsets[4]:
                Kpl = sorted(Kp)
                best = min(sum(m[(Kpl[perm[i]], Kl[i])] for i in range(4)) for perm in it.permutations(range(4)))
                out[Kp] = min(out[Kp], x + best)
        return out

    def push(self, lat, m):
        out = dict(lat)
        allset = frozenset(range(8))
        for K, x in lat.items():
            if x >= INF:
                continue
            Kc = sorted(allset - K)
            for Kp in self.subsets[4]:
                Kpc = sorted(allset - Kp)
                best = min(sum(m[(Kc[perm[i]], Kpc[i])] for i in range(4)) for perm in it.permutations(range(4)))
                out[Kp] = min(out[Kp], x + best)
        return out


def homexp(MX, MY):
    """Exponents of Hom_F(M_X, M_Y) (x) W on the matrix units E_{t k}, k in the X-basis, t in the Y-basis."""
    h = {}
    for t in range(8):
        for k in range(8):
            best, acc, ct, ck = 0, 0, t, k
            while True:
                ct, ck = MY.inv[ct], MX.inv[ck]
                acc += MY.w[ct] - MX.w[ck]
                best = max(best, acc)
                if (ct, ck) == (t, k):
                    assert acc == 0
                    break
            h[(t, k)] = best
    return h


allset = frozenset(range(8))


def push_from(MX, MY, latY):
    """f_* for f: Y -> X, the Poincaré adjoint of f^* = wedge^4 A, A in Hom_F(M_X, M_Y)."""
    h = homexp(MX, MY)
    out = {K: INF for K in MX.subsets[4]}
    for K, y in latY.items():
        Kc = sorted(allset - K)
        for Kp in MX.subsets[4]:
            Kpc = sorted(allset - Kp)
            out[Kp] = min(out[Kp], y + min(sum(h[(Kc[pp[i]], Kpc[i])] for i in range(4)) for pp in it.permutations(range(4))))
    return out


def pull_from(MX, MY, latY):
    """g^* for g: X -> Y, g^* = wedge^4 B, B in Hom_F(M_Y, M_X)."""
    h2 = homexp(MY, MX)
    out = {K: INF for K in MX.subsets[4]}
    for K, y in latY.items():
        Kl = sorted(K)
        for Kp in MX.subsets[4]:
            Kpl = sorted(Kp)
            out[Kp] = min(out[Kp], y + min(sum(h2[(Kpl[pp[i]], Kl[i])] for i in range(4)) for pp in it.permutations(range(4))))
    return out


def index(mod, lat):
    tot = 0
    for K in mod.subsets[4]:
        assert mod.nexp[4][K] <= lat[K] < INF, (K, lat[K])
        tot += lat[K] - mod.nexp[4][K]
    return tot


def comb(*lats):
    return {K: min(l[K] for l in lats) for K in lats[0]}


def closure(M, lat, push=True):
    m = M.endexp()
    while True:
        new = M.pull(lat, m)
        if push:
            new = M.push(new, m)
        if new == lat:
            return lat
        lat = new


def canon_words(words):
    canon = lambda s: min(s[i:] + s[:i] for i in range(len(s)))
    return tuple(sorted((canon(s) for s in words), key=lambda s: (len(s), s)))


def dual_words(words):
    return canon_words(["".join("1" if c == "0" else "0" for c in s) for s in words])


decs = decompositions()
assert len(decs) == 20
mods, rows = {}, {}
for d in decs:
    M = Mod(d)
    nm = "+".join(d)
    mods[nm] = M
    rows[nm] = (M.a_number(), canon_words(dual_words(d)) == canon_words(d), index(M, M.S()), index(M, comb(M.S(), M.P())))
    print(nm, "| a = %d | self-dual %s | log_p [T^4 : S] = %d | log_p [T^4 : S + S-hat] = %d" % rows[nm])
assert rows == TABLE
print("Table 1 agrees, row by row")


def primitive_multiset(words):
    """Each word v = u^k is replaced by k copies of its primitive root u; the smallest period of v is the first return of v inside vv."""
    out = []
    for v in words:
        per = (v + v).find(v, 1)
        out += [min(v[:per][i:] + v[:per][:i] for i in range(per))] * (len(v) // per)
    return tuple(sorted(out))


classes = {}
for nm, M in mods.items():
    classes.setdefault(primitive_multiset(M.words), []).append(nm)
nfilled = sum(1 for c in classes.values() if all(rows[nm][3] == 0 for nm in c))
print(f"isomorphism classes {len(classes)}, of which {nfilled} with S + S-hat = T^4")
assert len(classes) == 14 and nfilled == 9

filled = [mods[nm] for nm in mods if rows[nm][3] == 0]
Gp, E4 = mods["01+000111"], mods["01+01+01+01"]
assert len(filled) == 15
for nm in ("00011011", "00100111", "01+001011", "01+001101"):
    X = mods[nm]
    base = comb(X.S(), X.P())
    r = []
    for sources in (filled, [E4, Gp], filled + [Gp]):
        lat = base
        for Y in sources:
            lat = comb(lat, push_from(X, Y, Y.nexp[4]), pull_from(X, Y, Y.nexp[4]))
        r.append(index(X, closure(X, lat)))
    Ws = {frozenset((W, allset - W)) for W in X.subsets[4] if frozenset(X.pi[i] for i in W) == allset - W and sum(X.w[i] for i in W) == 2}
    assert len(Ws) == 1
    W, Wc = tuple(next(iter(Ws)))
    LW = {K: INF for K in X.subsets[4]}
    LW[W], LW[Wc] = X.nexp[4][W], X.nexp[4][Wc]
    iE = index(X, closure(X, comb(X.S(), LW), push=False))
    iP = index(X, comb(X.S(), X.P(), LW))
    print(f"{nm} | the fifteen, End closure: {r[0]} | E_0^4 and G_p, End closure: {r[1]} | the fifteen and G_p, End closure: {r[2]} | [T^4 : S + End^* L_W] = p^{iE} | [T^4 : S + S-hat + L_W] = p^{iP}")
    assert r == [rows[nm][3]] * 3 and iE == 0 and (iP == 0 or rows[nm][0] != 3) and not rows[nm][1]
print("all assertions passed")
