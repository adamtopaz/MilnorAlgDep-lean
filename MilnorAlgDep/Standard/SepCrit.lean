module

public import MilnorAlgDep.Standard.Differentials
public import Mathlib.FieldTheory.Separable

/-!
# A differential separability criterion

Blueprint Lemma 3.1 (`lem:sepcrit`) describes separability of `yᵢ` over `l(yⱼ : j ≠ i)` through the
partial derivatives of the irreducible relation `f` of `(y₁, …, y_m)`. In the blueprint it is used
in two ways: to read off separability from a linear relation `∑ f_{Yᵢ} d yᵢ = 0` (Lemmas 3.2, 3.5,
4.6 and 6.2), and to know that some `f_{Yᵢ}` is non-zero. We replace it by the following criterion,
which avoids multivariate polynomials altogether:

* `MilnorAlgDep.isSeparable_adjoin_of_linearIndependent_kaehler_D`: let `l` be perfect and
  `x : ι → E`; if the differentials `d xᵢ` are linearly independent in `Ω[E⁄l]` and `y ∈ E` is
  algebraic over `l(x)`, then `y` is separable over `l(x)`.

Proof sketch: otherwise the minimal polynomial `f = ∑ cᵢ Xⁱ` of `y` over `K = l(x)` has `f' = 0`,
so `0 = d (f(y)) = ∑ᵢ yⁱ d cᵢ = ∑ₖ (∑ᵢ ∂ₖ(cᵢ) yⁱ) d xₖ` in `Ω[E⁄l]`, where `∂ₖ` are the coordinate
derivations of `K` for the basis `(d xₖ)` of `Ω[K⁄l]` (Lemma 2.1 (S2)). Hence each polynomial
`∑ᵢ ∂ₖ(cᵢ) Xⁱ`, of degree `< deg f`, vanishes at `y`, so is zero; so `d cᵢ = 0` in `Ω[K⁄l]` and
`cᵢ ∈ K ^ p` (Lemma 2.1 (S3), `MilnorAlgDep.kaehler_D_eq_zero_iff_exists_pow_eq`). Then `f` is a
`p`-th power, contradicting irreducibility.

We also record (`MilnorAlgDep.exists_isSeparable_pow_pow`) that in characteristic `p` some
`p ^ n`-th power of an algebraic element is separable.
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential IntermediateField

variable {l E : Type*} [Field l] [Field E] [Algebra l E]

/-- **Separability criterion** (replacing blueprint Lemma 3.1(c)): over a perfect field `l`, if
the differentials `d xᵢ` are linearly independent in `Ω[E⁄l]` and `y` is algebraic over `l(x)`,
then `y` is separable over `l(x)`. -/
theorem isSeparable_adjoin_of_linearIndependent_kaehler_D [PerfectField l] {ι : Type*}
    {x : ι → E} (h : LinearIndependent E fun i ↦ D l E (x i)) {y : E}
    (hy : IsAlgebraic (adjoin l (Set.range x)) y) : IsSeparable (adjoin l (Set.range x)) y := by
  sorry

/-- In characteristic `p`, if `y` is algebraic over `K` then `y ^ p ^ n` is separable over `K`
for some `n`. -/
theorem exists_isSeparable_pow_pow {K : Type*} [Field K] [Algebra K E] (p : ℕ) [ExpChar K p]
    {y : E} (hy : IsAlgebraic K y) : ∃ n : ℕ, IsSeparable K (y ^ p ^ n) := by
  sorry

end MilnorAlgDep
