"""Section 9: Table 1, Proposition 9.3 and Remark 9.4, for the twenty cycle decompositions of monomial supersingular Dieudonné modules of height 8 and dimension 4."""
import itertools as it
from minplus import Module, merge, pullback, pushforward, end_closure

# Table 1 of the note, row by row: modules, a-number, self-dual, log_p [T^4 : S] (one value for the row or one per module), log_p [T^4 : S + S-hat]
TABLE = [
    (("01+01+01+01", "01+01+0101", "0101+0101", "01+010101", "01010101"), 4, True, (0,), 0),
    (("01+01+0011", "0011+0101", "00101101"), 3, True, (0,), 0),
    (("0011+0011", "00110011"), 2, True, (0,), 0),
    (("00001111",), 1, True, (0,), 0),
    (("00110101", "00101011"), 3, False, (0, 2), 0),
    (("00011101", "00010111"), 2, False, (2, 16), 0),
    (("01+000111",), 2, True, (4,), 4),
    (("01+001101", "01+001011"), 3, False, (2, 10), 2),
    (("00100111", "00011011"), 2, False, (26,), 26),
]
# isomorphism classes named in the caption of Table 1; every other decomposition is alone in its class
CLASSES = [{"01+01+01+01", "01+01+0101", "0101+0101", "01+010101", "01010101"}, {"01+01+0011", "0011+0101"}, {"0011+0011", "00110011"}]
OPEN = ["01+001101", "01+001011", "00100111", "00011011"]


def canon(w):
    return min(w[i:] + w[:i] for i in range(len(w)))


def name(words):
    return "+".join(sorted(words, key=lambda w: (len(w), w)))


def decompositions():
    necklaces = sorted({canon("".join("1" if i in ones else "0" for i in range(2 * k))) for k in (1, 2, 3, 4) for ones in it.combinations(range(2 * k), k)}, key=lambda w: (len(w), w))
    out = []

    def rec(start, rem, cur):
        if rem == 0:
            out.append(tuple(cur))
        for i in range(start, len(necklaces)):
            if len(necklaces[i]) <= rem:
                rec(i, rem - len(necklaces[i]), cur + [necklaces[i]])
    rec(0, 8, [])
    return out


def iso_key(words):
    """Multiset of primitive words: v = u^k contributes k copies of u (Section 9)."""
    out = []
    for v in words:
        d = next(d for d in range(1, len(v) + 1) if len(v) % d == 0 and v == v[:d] * (len(v) // d))
        out += [canon(v[:d])] * (len(v) // d)
    return tuple(sorted(out))


def dual(words):
    return tuple(canon(w.translate(str.maketrans("01", "10"))) for w in words)


decs = decompositions()
words = {name(w): w for w in decs}
order = [nm for names, *_ in TABLE for nm in names]
print("cycle decompositions:", len(words))
assert len(words) == 20 and sorted(order) == sorted(words)
mods = {nm: Module.from_words(sorted(words[nm], key=lambda x: (len(x), x))) for nm in order}

rows = {}
print("module | a-number | self-dual | log_p [T^4 : S] | log_p [T^4 : S + S-hat]")
for nm, X in mods.items():
    sd = iso_key(dual(words[nm])) == iso_key(words[nm])
    assert sd == (sorted(map(canon, dual(words[nm]))) == sorted(words[nm]))
    rows[nm] = (X.anumber(), sd, X.index(X.S), X.index(X.S, X.Shat))
    print(nm, "|", " | ".join(map(str, rows[nm])))

table = {}
for names, a, sd, es, eh in TABLE:
    for i, nm in enumerate(names):
        table[nm] = (a, sd, es[i] if len(es) > 1 else es[0], eh)
    if len(names) == 2 and not sd:
        assert iso_key(dual(words[names[0]])) == iso_key(words[names[1]]), names  # a module and its dual
assert rows == table
print("Table 1 agrees with the computation, row by row")

for nm in mods:
    dn = next(x for x in mods if iso_key(words[x]) == iso_key(dual(words[nm])))
    assert rows[nm][0] == rows[dn][0] and rows[nm][3] == rows[dn][3]
print("a-number and log_p [T^4 : S + S-hat] agree on every pair of mutually dual modules")

classes = {}
for nm in mods:
    classes.setdefault(iso_key(words[nm]), set()).add(nm)
classes = list(classes.values())
assert sorted(map(sorted, (c for c in classes if len(c) > 1))) == sorted(map(sorted, CLASSES))
filled = [nm for nm in mods if rows[nm][3] == 0]
nfilled = sum(1 for c in classes if c <= set(filled))
open_ = [nm for nm in mods if rows[nm][3] > 0 and nm != "01+000111"]
print(f"isomorphism classes: {len(classes)}; S + S-hat = T^4 for {len(filled)} decompositions in {nfilled} classes; open: {' '.join(open_)}")
assert (len(classes), len(filled), nfilled) == (14, 15, 9) and sorted(open_) == sorted(OPEN)
assert all(c <= set(filled) or not c & set(filled) for c in classes)

# Proposition 9.3: enlargements of S + S-hat; the statement concerns the four open modules, the other rows are printed for comparison
Gp = mods["01+000111"]


def transported(X, sources):
    return merge(*[f(X, Y, Y.n[4]) for Y in sources for f in (pushforward, pullback)])


print("module | log_p [T^4 : S + S-hat] after adding the push-forwards and pull-backs of T^4 of the given modules and closing under End^*, End_*:  the fifteen with S + S-hat = T^4 | E_0^4 and G_p | the fifteen and G_p")
for nm, X in mods.items():
    base = merge(X.S, X.Shat)
    r = [X.index(end_closure(X, merge(base, transported(X, src)))) for src in ([mods[y] for y in filled], [mods["01+01+01+01"], Gp], [mods[y] for y in filled] + [Gp])]
    print(nm, "|", " | ".join(map(str, r)))
    if nm in OPEN:
        assert r == [rows[nm][3]] * 3

# Remark 9.4: the diagonal inert imaginary quadratic actions of signature (2,2) on the four open modules
for nm in OPEN:
    X = mods[nm]
    Ws = {frozenset((W, X.all - W)) for W in X.sub[4] if X.step(W) == X.all - W and len(W & X.kerF()) == 2}
    assert len(Ws) == 1
    W, Wc = tuple(next(iter(Ws)))
    LW = {W: X.n[4][W], Wc: X.n[4][Wc]}
    iE, iP = X.index(X.S, pullback(X, X, LW)), X.index(X.S, X.Shat, LW)
    print(f"{nm} (a-number {rows[nm][0]}): one (2,2) Weil lattice L_W, exponents {X.n[4][W]}, {X.n[4][Wc]}; [T^4 : S + End^* L_W] = p^{iE}; [T^4 : S + S-hat + L_W] = p^{iP}")
    assert iE == 0 and not rows[nm][1] and (iP == 0 or rows[nm][0] != 3)
assert max(r[3] for r in rows.values()) == 26 and {nm for nm in mods if rows[nm][3] == 26} == {"00100111", "00011011"}
print("all assertions passed")
