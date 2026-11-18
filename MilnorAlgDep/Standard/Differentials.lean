module

public import MilnorAlgDep.Standard.Differentials.Basis
public import MilnorAlgDep.Standard.Differentials.ChainRule
public import MilnorAlgDep.Standard.Differentials.Independence
public import MilnorAlgDep.Standard.Differentials.PDeriv

/-!
# Kähler differentials of field extensions

Standard facts about `Ω[E⁄l]` for fields `l ⊆ E`, blueprint Lemma 2.3 (`lem:standard`) and the
general form of Lemma 4.6 (`lem:lax`):

* `Differentials/Basis.lean`: (S2), `(d aᵢ)ᵢ` is a basis of `Ω[E⁄l]` if `E` is separable
  algebraic over `l(a)` with `a` algebraically independent (`MilnorAlgDep.kaehlerBasis`).
* `Differentials/ChainRule.lean`: (S2), chain rule; `d y ∈ span {d xᵢ}` for `y` separable over
  `l(x)`; `d (y ^ p) = 0` in characteristic `p`.
* `Differentials/PDeriv.lean`: (S1), polynomials with vanishing partial derivatives.
* `Differentials/Independence.lean`: Lemma 4.6 in general form (linearly independent
  differentials imply algebraic independence over a perfect field) and the characteristic `0`
  criterion `AlgebraicIndependent l y ↔ LinearIndependent E (d ∘ y)`.
-/
