# Integral crystalline Tate classes on Mumford's fourfolds: code

Code for the computations in the note *Integral crystalline Tate classes of codimension two at supersingular points of Mumford's fourfolds*. Each script reproduces the numbers of the statement listed next to it and asserts them, so a run stops with an error if a number differs from the note.

| Script | Reproduces |
|---|---|
| `tate_index.py` | Proposition 4.3: the two π-orbits of (4.1), the exponents of T², T⁴ and S for all 2-sets and 4-sets, the four sets (4.2), T⁴/S ≅ (Z/p)⁴, and T⁶ spanned by triple products; Lemma 4.4(i)–(iii) and the lattice N after it: the four F-compatible eigensets, their numbers of elements with s₁ = 1, and the exponents of L and N; Remark 8.5: the a-number 2 (Appendix A) |
| `endomorphisms.py` | Proposition 5.1(i)–(iv) and the exponents used in the proof of Theorem 5.2: the exponents of End(M, F), End\*S ⊆ S, [T⁴ : S + L] = p², S + End\*L = T⁴, End\*N ⊆ S + N, [T⁴ : S + N] = p², and the Künneth (2,2)-component of T⁴ of X × X (Appendix A) |
| `non_inert_primes.py` | Proposition 8.4: T⁴ = S and the Künneth (2,2)-component for the two models of the proof (Appendix A) |
| `monomial_modules.py` | Table 1 and Proposition 9.3: a-number, self-duality, [T⁴ : S] and [T⁴ : S + Ŝ] for the twenty cycle decompositions, the fourteen isomorphism classes, the fifteen decompositions in nine classes with S + Ŝ = T⁴, and the enlargements that leave the four open indices unchanged; Remark 9.4: the Weil lattices of signature (2,2) on the four open modules (Appendix A) |
| `weil_coefficient.py` | Lemma 7.4, through the cohomological Fourier–Mukai transform of Orlov's equivalence for d = 4, 6, 8, 10, 12, 28: only K_d-types (6,0), (0,6), (3,3), and Weil component of content (d+1)/(2d), while the degree-6 part of ch before the normalization by κ has components of every type (i, 6−i); the determinant d⁶ of ψ₆ (Section 7.1) (Appendix A) |
| `minplus.py` | the min-plus calculus of Section 2.2, used by the first four scripts |
| `minplus_independent.py` | Propositions 4.3, 5.1 and 8.4 and Lemma 4.4(i), (ii) again, with separately written min-plus code |
| `tate_index_independent.py` | Proposition 4.3 at p = 5 and 7 with integer matrices and Hermite normal forms, without the min-plus formula |
| `endomorphisms_independent.py` | Proposition 5.1(i)–(iii) at p = 5, 13 and 17 with explicit bases over W(F_{p¹²}) modulo p⁷ and randomly sampled endomorphisms (fixed seed), without the min-plus formula |
| `monomial_modules_independent.py` | Table 1, Proposition 9.3 and Remark 9.4 again, with separately written min-plus code |
| `weil_coefficient_independent.py` | Lemma 7.4 again, through Markman's spinor formulas, including that ½(ω + ω̄) is primitive in H⁶(X₆, Z) |

The scripts ending in `_independent.py` share no code with the others and recompute the statements listed next to them by other means: integer matrices with Hermite normal forms, explicit p-adic bases, separately written min-plus code, and Markman's spinor formulas.

The note and this code were written by large language models; the note's subsection on the use of large language models states how, and what has and has not been checked.

## Running

Python 3.12 with the versions in `requirements.txt`; the scripts without `_independent` in their names need only the standard library.

```
pip install -r requirements.txt
python tate_index.py
```

## License

MIT, see `LICENSE`.
