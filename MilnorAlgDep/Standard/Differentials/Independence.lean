module

public import MilnorAlgDep.Standard.Differentials.Basis
public import MilnorAlgDep.Standard.Differentials.ChainRule
public import MilnorAlgDep.Standard.Differentials.PDeriv
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Algebraic independence and Kähler differentials

This file formalizes the general form of blueprint Lemma 4.5 (`lem:lax`, "Lax property"): over a
perfect field `l`, elements of `E` whose differentials are linearly independent in `Ω[E⁄l]` are
algebraically independent (`MilnorAlgDep.algebraicIndependent_of_linearIndependent_kaehler_D`).

The proof is the blueprint's: take a non-zero relation `f` of minimal total degree. If all
partial derivatives of `f` vanish, then `f` is constant (characteristic `0`) or a `p`-th power
`g ^ p` (Lemma 2.1 (S1), characteristic `p`), and `g` is a relation of smaller degree. Otherwise a
non-zero partial derivative of `f` has smaller degree, so does not vanish at `y`, and the chain
rule gives a non-trivial linear relation between the `d yᵢ`.

In characteristic `0` the converse holds, by extending `y` to a transcendence basis and applying
Lemma 2.1 (S2) (`MilnorAlgDep.algebraicIndependent_iff_linearIndependent_kaehler_D`); in
particular `d y = 0 ↔ y` is algebraic over `l` (`MilnorAlgDep.kaehler_D_eq_zero_iff_isAlgebraic`).
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential MvPolynomial IntermediateField

variable {l E : Type*} [Field l] [Field E] [Algebra l E]

/-- **Blueprint Lemma 4.5 (Lax property)**, general form: over a perfect field `l`, if the
differentials `d yᵢ` are linearly independent in the `E`-vector space `Ω[E⁄l]`, then the `yᵢ` are
algebraically independent over `l`. Equivalently, algebraically dependent elements have linearly
dependent differentials. -/
theorem algebraicIndependent_of_linearIndependent_kaehler_D [PerfectField l] {ι : Type*}
    {y : ι → E} (h : LinearIndependent E fun i ↦ D l E (y i)) : AlgebraicIndependent l y := by
  rw [algebraicIndependent_iff]
  intro f
  induction hn : f.totalDegree using Nat.strong_induction_on generalizing f with
  | _ n ih =>
  intro hf
  by_contra hne
  -- A relation of total degree `0` is a non-zero constant: impossible.
  have hconst : ∀ c : l, aeval y (C c : MvPolynomial ι l) = 0 → (C c : MvPolynomial ι l) = 0 := by
    intro c hc
    rw [aeval_C, map_eq_zero_iff _ (algebraMap l E).injective] at hc
    rw [hc, C_0]
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [totalDegree_eq_zero_iff_eq_C] at hn
    rw [hn] at hf hne
    exact hne (hconst _ hf)
  by_cases hd : ∃ i, pderiv i f ≠ 0
  · -- Some partial derivative is non-zero: the chain rule gives a linear relation.
    obtain ⟨i, hi⟩ := hd
    have hlt : (pderiv i f).totalDegree < n := hn ▸ totalDegree_pderiv_lt hi
    have hne' : aeval y (pderiv i f) ≠ 0 := fun h0 ↦ hi (ih _ hlt _ rfl h0)
    have hiv : i ∈ f.vars := by
      by_contra hv
      exact hi (pderiv_eq_zero_of_notMem_vars hv)
    exact hne' (linearIndependent_iff'.mp h f.vars (fun j ↦ aeval y (pderiv j f))
      (sum_pderiv_smul_derivation_eq_zero (D l E) y hf) i hiv)
  · -- All partial derivatives vanish: use (S1).
    push Not at hd
    obtain ⟨p, hchar⟩ := ExpChar.exists l
    have hchar' := hchar
    rcases hchar' with _ | ⟨hp⟩
    · rw [eq_C_of_pderiv_eq_zero hd] at hf hne
      exact hne (hconst _ hf)
    · obtain ⟨g, rfl⟩ := exists_eq_pow_of_pderiv_eq_zero p hd
      have hg0 : g ≠ 0 := by
        rintro rfl
        exact hne (zero_pow hp.ne_zero)
      have hgy : aeval y g = 0 := by
        rw [map_pow] at hf
        exact pow_eq_zero_iff hp.ne_zero |>.mp hf
      rw [totalDegree_pow_of_isDomain hg0] at hn
      have hpos : 0 < g.totalDegree := Nat.pos_of_ne_zero fun h0 ↦ hn0 (by rw [← hn, h0, mul_zero])
      have hlt : g.totalDegree < n := by
        rw [← hn]
        exact lt_mul_left hpos hp.one_lt
      exact hg0 (ih _ hlt g rfl hgy)

/-- In characteristic `0`, an algebraically independent family extends to a transcendence basis
over which `E` is separable algebraic, so its differentials are linearly independent. -/
theorem linearIndependent_kaehler_D_of_algebraicIndependent [CharZero l] {ι : Type*} {y : ι → E}
    (hy : AlgebraicIndependent l y) : LinearIndependent E fun i ↦ D l E (y i) := by
  obtain ⟨t, hst, ht⟩ := exists_isTranscendenceBasis_superset hy.to_subtype_range
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap l E).injective
  have : Algebra.IsAlgebraic (adjoin l (Set.range ((↑) : t → E))) E := ht.isAlgebraic_field
  have hsep : Algebra.IsSeparable (adjoin l (Set.range ((↑) : t → E))) E :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  have hli := linearIndependent_kaehler_D ht.1 hsep
  let f : ι → t := fun i ↦ ⟨y i, hst (Set.mem_range_self i)⟩
  exact hli.comp f fun i j hij ↦ hy.injective (congrArg Subtype.val hij)

/-- **Characteristic `0` criterion** (blueprint Lemma 2.1 (S2) and Lemma 4.5 in characteristic
`0`): if `l` has characteristic `0`, a family `y` is algebraically independent over `l` if and
only if the differentials `d yᵢ` are linearly independent in `Ω[E⁄l]`. -/
theorem algebraicIndependent_iff_linearIndependent_kaehler_D [CharZero l] {ι : Type*}
    {y : ι → E} : AlgebraicIndependent l y ↔ LinearIndependent E fun i ↦ D l E (y i) :=
  ⟨linearIndependent_kaehler_D_of_algebraicIndependent,
    algebraicIndependent_of_linearIndependent_kaehler_D⟩

/-- In characteristic `0`, `d y = 0` in `Ω[E⁄l]` if and only if `y` is algebraic over `l`
(blueprint Lemma 2.1 (S3) for `p = 1`). -/
theorem kaehler_D_eq_zero_iff_isAlgebraic [CharZero l] {y : E} :
    D l E y = 0 ↔ IsAlgebraic l y := by
  have h := algebraicIndependent_iff_linearIndependent_kaehler_D (l := l) (y := fun _ : Unit ↦ y)
  rw [algebraicIndependent_unique_type_iff, linearIndependent_unique_iff] at h
  rw [← not_iff_not, ← ne_eq, ← h]
  rfl

end MilnorAlgDep
