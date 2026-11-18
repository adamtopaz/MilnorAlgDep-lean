module

public import MilnorAlgDep.Standard.Differentials.BaseChange
public import MilnorAlgDep.Standard.Differentials.Basis
public import MilnorAlgDep.Standard.Differentials.ChainRule
public import MilnorAlgDep.Standard.Differentials.Independence
public import MilnorAlgDep.Standard.Differentials.KernelD
public import MilnorAlgDep.Standard.Differentials.PDeriv
public import MilnorAlgDep.Standard.Differentials.PerfectCore
public import MilnorAlgDep.Standard.Differentials.Restrict

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
* `Differentials/KernelD.lean`: (S3), the kernel of `d` is `E ^ p` (`l` perfect of
  characteristic `p`).
* `Differentials/PerfectCore.lean`: (S3), `y ∉ l` is `z ^ p ^ j` with `d z ≠ 0`, for unique
  `j`, `z` (`l` moreover relatively algebraically closed in `E`).
* `Differentials/BaseChange.lean`: `E' ⊗ Ω[E⁄l] → Ω[E'⁄l]` is an isomorphism for `E'/E` separable
  algebraic, and injective when the `d aᵢ` stay independent.
* `Differentials/Restrict.lean`: applying all this to intermediate fields of a big field `L`
  (e.g. the elements of `L` separable algebraic over `l(a)`).
-/
