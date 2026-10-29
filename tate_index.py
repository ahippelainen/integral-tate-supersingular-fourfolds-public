"""Proposition 4.3 and Lemma 4.4(i)-(iii): the Tate lattices T^2, T^4, T^6 of the model (1.2) and the index of S in T^4."""
import itertools as it
from minplus import Module

labels = ["".join(s) for s in it.product("01", repeat=3)]
pi = {s: s[2] + str(1 - int(s[0])) + s[1] for s in labels}  # (4.1)
a = {s: int(s[0]) for s in labels}
X = Module(labels, pi, a, "model (1.2)")


def name(K):
    return "{" + ",".join(sorted(K)) + "}"


def fs(*s):
    return frozenset(s)


Tp, Tm = fs("000", "011", "101", "110"), fs("001", "010", "100", "111")
Mp, Mm = fs("000", "001", "011", "101"), fs("010", "100", "110", "111")

# the pi-orbits and their exponent words, after (4.1)
orbits = X.orbits()
for o in orbits:
    print("pi-orbit", " ".join(o), " exponents a(s):", "".join(str(a[s]) for s in o))
assert orbits == [["000", "010", "011", "111", "101", "100"], ["001", "110"]]

# the four sets (4.2): tetrahedra are the parity classes; M+ and M- by majority after s -> (s1, s2, 1 - s3)
assert Tp == {s for s in labels if sum(map(int, s)) % 2 == 0} and Tm == frozenset(labels) - Tp
flip = lambda s: (int(s[0]), int(s[1]), 1 - int(s[2]))
assert Mp == {s for s in labels if sum(1 for x in flip(s) if x == 0) >= 2} and Mm == frozenset(labels) - Mp

n2, n4, S = X.n[2], X.n[4], X.S
print("2-sets:", len(n2), " 4-sets:", len(n4))
assert (len(n2), len(n4)) == (28, 70)
print("exponents nu_T(J) of T^2 for the 28 two-sets J:")
print("  " + "  ".join(f"{name(J)}:{n2[J]}" for J in X.sub[2]))
print("exponents nu_T(J), nu_S(J) of T^4 and S for the 70 four-sets J:")
for J in X.sub[4]:
    print(f"  {name(J)}  {n4[J]}  {S[J]}")

defects = {J: (n4[J], S[J]) for J in n4 if S[J] != n4[J]}
assert defects == {Tp: (0, 1), Tm: (0, 1), Mm: (0, 1), Mp: (1, 2)}
e = X.index(S)
print(f"[T^4 : S] = p^{e}; nu_S - nu_T is 1 at T+, T-, M+, M- and 0 elsewhere, so T^4/S = (Z/p)^4")
assert e == 4

s6 = X.S6()
i6 = sum(s6[K] - X.n[6][K] for K in X.n[6])
assert all(s6[K] >= X.n[6][K] for K in X.n[6])
print(f"[T^6 : products of three classes in T^2] = p^{i6}")
assert i6 == 0

# Lemma 4.4(i): the F-compatible eigensets (pi(J) = complement of J) are the four sets (4.2)
eig = [J for J in X.sub[4] if X.step(J) == X.all - J]
print("4-sets J with pi(J) = complement of J:", " ".join(name(J) for J in eig))
assert set(eig) == {Tp, Tm, Mp, Mm}
# Lemma 4.4(ii), (iii) and the text after Lemma 4.4
for nm, J, k in (("T+", Tp, 2), ("T-", Tm, 2), ("M+", Mp, 1), ("M-", Mm, 3)):
    print(f"  {nm} = {name(J)}  |J cap {{s1=1}}| = {len(J & X.kerF())}  a(J) = {X.weight(J)}  nu_T(J) = {n4[J]}")
    assert len(J & X.kerF()) == k
assert X.weight(Tp) == X.weight(Tm) == 2
assert (n4[Tp], n4[Tm], n4[Mp], n4[Mm]) == (0, 0, 1, 0)
assert X.step(Tp) == Tm and X.step(Mp) == Mm
print(f"a-number of the model: {X.anumber()}")  # Remark 8.5
assert X.anumber() == 2
print("all assertions passed")
