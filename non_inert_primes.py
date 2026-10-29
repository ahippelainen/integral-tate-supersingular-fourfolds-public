"""Proposition 8.4: the two models at primes that are unramified and not inert in k have T^4 = S, and the Künneth (2,2)-component of T^4 of the square is spanned by that of S."""
import itertools as it
from minplus import Module, kunneth22

labels = ["".join(s) for s in it.product("01", repeat=3)]
models = [
    # Hodge slot at a place of residue degree 1: (W^2, A sigma) (x) (W^4, sigma), the Dieudonné module of E_0^4
    ("(W^2, A sigma) (x) (W^4, sigma)", {s: str(1 - int(s[0])) + s[1] + s[2] for s in labels}, {s: int(s[0]) for s in labels}, ["01"] * 4),
    # Hodge slot at the place of residue degree 2: (W^2, sigma) (x) (W^2 (x) W^2, (A (x) 1) sigma'), sigma'(x (x) y) = sigma y (x) sigma x
    ("(W^2, sigma) (x) (W^2 (x) W^2, (A (x) 1) sigma')", {s: s[0] + s[2] + str(1 - int(s[1])) for s in labels}, {s: int(s[1]) for s in labels}, ["0011"] * 2),
]
for nm, pi, a, words in models:
    X = Module(labels, pi, a, nm)
    w = sorted(min(x[i:] + x[:i] for i in range(len(x))) for x in ("".join(str(a[s]) for s in o) for o in X.orbits()))
    e = X.index(X.S)
    b0, = kunneth22(X)
    print(f"{nm}: cycle words {'+'.join(w)}  [T^4 : S] = p^{e}  [T_22 : S_22] = p^{b0}")
    assert w == words and e == 0 and b0 == 0
print("all assertions passed")
