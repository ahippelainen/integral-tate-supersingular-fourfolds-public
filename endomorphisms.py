"""Proposition 5.1 and the exponents used in the proof of Theorem 5.2: the action of End(M, F) on T^4 of the model (1.2), and the Künneth (2,2)-component of T^4 of its square."""
import itertools as it
from minplus import Module, hom_exponents, merge, pullback, kunneth22

labels = ["".join(s) for s in it.product("01", repeat=3)]
X = Module(labels, {s: s[2] + str(1 - int(s[0])) + s[1] for s in labels}, {s: int(s[0]) for s in labels}, "model (1.2)")
n4, S = X.n[4], X.S
fs = lambda *s: frozenset(s)
Tp, Tm = fs("000", "011", "101", "110"), fs("001", "010", "100", "111")
Mp, Mm = fs("000", "001", "011", "101"), fs("010", "100", "110", "111")
L = {Tp: n4[Tp], Tm: n4[Tm]}  # Lemma 4.4(iii)
N = {Mp: n4[Mp], Mm: n4[Mm]}  # after Lemma 4.4

m = hom_exponents(X, X)
print("exponents of End(M, F) (x) W on the matrix units E_{t,s}: e_s -> e_t (row t, column s):")
print("       " + " ".join(labels))
for t in labels:
    print(f"  {t}  " + "   ".join(str(m[t, s]) for s in labels))

endS = pullback(X, X, S)
i_ok = all(endS[J] >= S[J] for J in n4)
iiL, iiEL = X.index(S, L), X.index(S, pullback(X, X, L))
SN = merge(S, N)
endN = pullback(X, X, N)
iii_ok = all(endN[J] >= SN[J] for J in n4)
iiiN = X.index(SN)
print(f"(i)   End^* S inside S: {i_ok}")
print(f"(ii)  [T^4 : S + L] = p^{iiL}   [T^4 : S + End^* L] = p^{iiEL}")
print(f"(iii) End^* N inside S + N: {iii_ok}   [T^4 : S + N] = p^{iiiN}")
assert i_ok and iii_ok and (iiL, iiEL, iiiN) == (2, 0, 2)

# proof of Theorem 5.2: S + N differs from S only at e_{M+}, e_{M-}, by one power of p each; S has exponent 1 at e_{T+}, e_{T-}
assert {J: S[J] - SN[J] for J in n4 if S[J] != SN[J]} == {Mp: 1, Mm: 1}
assert S[Tp] == S[Tm] == 1
print("S + N and S differ only at e_{M+}, e_{M-}, by p each; S has exponent 1 at e_{T+}, e_{T-}")

b0, b1 = kunneth22(X, L)
print(f"(iv)  [T_22 : S_22] = p^{b0}   [T_22 : S_22 + PB(L)] = p^{b1}")
assert b1 == 0
print("all assertions passed")
