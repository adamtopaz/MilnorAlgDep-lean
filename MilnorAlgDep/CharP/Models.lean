module

public import MilnorAlgDep.CharP.Levels
public import Mathlib.Order.Int.ConditionallyCompleteOrder

/-!
# Points in a model

Blueprint, Section 4: Lemma 4.3 (points in a model), Definition 4.4 (model level, model generator,
line of a point, height), Lemma 4.5 (`lem:lax`, lax property) for points, and "propagation"
(lines 342-344). (Definition 4.1 and Lemma 4.2 are in `MilnorAlgDep.CharP.Model`.)

Let `B` be a transcendence basis of `L / l` and `L_B = model l B`. The blueprint attaches to a
point `P` its model level `λ_B(P) ∈ Λ(P)` and to a level `α` its height `α - λ_B(P) ∈ ℤ`.
Element-wise we only use the *height* of an element `y ∈ L \ l`,
`hgt l p B y = ht_B(lev y) = lev(y) - λ_B(Q_y)`, defined as the largest `j` with
`y ∈ Frob^j(L_B)` (this is Lemma 4.3(a)). A *model generator* of `Q_y` is an element of height
`0`, e.g. `frobZ L p (-hgt l p B y) y`; and the *line* of `Q_y` is
`omega l p B y = L_B · d(frobZ L p (-hgt l p B y) y) ⊆ Ω_B`, which by Lemma 4.3(c) only depends on
the point `Q_y` (`omega_eq_of_samePoint`).

## Main definitions

* `MilnorAlgDep.hgt l p B y : ℤ`: the height of `y` (meaningful for `y` transcendental over `l`
  and `B` a transcendence basis; otherwise `0` for `y` algebraic, or the junk value of `sSup`).
* `MilnorAlgDep.omega l p B y : Submodule (model l B) Ω[model l B⁄l]`: the line `ω_B(Q_y)`.

## Main statements

* Lemma 4.3: `frobZ_neg_mem_model_iff` (a), `hgt_eq_zero_iff` (b),
  `span_modelD_eq_of_hgt_eq_zero` (c).
* Height calculus: `hgt_frobZ`, `hgt_sub_hgt` (`hgt y - hgt y' = lev(y) - lev(y')`),
  `hgt_apply` (elements of `B` are model generators).
* Lines: `omega_eq_span_of_hgt_eq_zero`, `omega_eq_of_samePoint`, `omega_ne_bot`.
* `not_linearIndependent_modelD_of_not_algebraicIndependent`: Lemma 4.5 (lax property) for
  points.
* `omega_le_sup_of_isAlgebraic`, `omega_eq_inf_of_isAlgebraic`: propagation.
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential IntermediateField

variable {l L : Type*} [Field l] [Field L] [Algebra l L] {ι κ : Type*}
variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]

section Defs

variable (l) in
/-- **Blueprint Definition 4.4** (height), element-wise: the height
`ht_B(lev y) = lev(y) - λ_B(Q_y)` of `y`, defined as the largest `j ∈ ℤ` with
`y ∈ Frob^j(L_B)`, i.e. with `Frob^{-j} y ∈ L_B` (Lemma 4.3(a), `frobZ_neg_mem_model_iff`).

It is meaningful for `y` transcendental over `l` and `B` a transcendence basis of `L / l`, which
all results below assume. (For `y` algebraic over `l` the set is all of `ℤ` and `hgt = 0`.) -/
noncomputable def hgt (B : ι → L) (y : L) : ℤ :=
  sSup {j : ℤ | frobZ L p (-j) y ∈ model l B}

variable (l) in
/-- **Blueprint Definition 4.4** (line of a point): `ω_B(Q_y) = L_B · d y₀ ⊆ Ω_B`, where
`y₀ = Frob^{-hgt y} y` is a model generator of the point `Q_y` (an element of height `0`). By
Lemma 4.3(c) it only depends on `Q_y` (`omega_eq_of_samePoint`), and it is `L_B · d y'` for every
model generator `y'` of `Q_y` (`omega_eq_span_of_hgt_eq_zero`). Meaningful for `y` transcendental
over `l` and `B` a transcendence basis. -/
noncomputable def omega (B : ι → L) (y : L) : Submodule (model l B) Ω[model l B⁄l] :=
  (model l B) ∙ modelD l B (frobZ L p (-hgt l p B y) y)

end Defs

variable {B : ι → L}

section PointsInModel

/-- **Blueprint Lemma 4.3(a)**: for `y ∈ L \ l`, `y ∈ Frob^j(L_B)` (i.e. `Frob^{-j} y ∈ L_B`) iff
`lev(y) ≥ λ_B(Q_y) + j`, i.e. `j ≤ hgt y`. -/
theorem frobZ_neg_mem_model_iff (hB : IsTranscendenceBasis l B) {y : L} (hy : Transcendental l y)
    (j : ℤ) : frobZ L p (-j) y ∈ model l B ↔ j ≤ hgt l p B y := by
  sorry

/-- **Blueprint Lemma 4.3(a)** for `j = 0`: `y ∈ L_B` iff `hgt y ≥ 0`. -/
theorem mem_model_iff_hgt_nonneg (hB : IsTranscendenceBasis l B) {y : L}
    (hy : Transcendental l y) : y ∈ model l B ↔ 0 ≤ hgt l p B y := by
  rw [← frobZ_neg_mem_model_iff p hB hy 0, neg_zero, frobZ_zero_apply]

/-- **Blueprint Lemma 4.3(b)**: for `y ∈ L \ l`, `y ∈ L_B` and `d y ≠ 0` in `Ω_B` iff
`lev(y) = λ_B(Q_y)`, i.e. `hgt y = 0` (`y` is a *model generator* of `Q_y`). -/
theorem hgt_eq_zero_iff (hB : IsTranscendenceBasis l B) {y : L} (hy : Transcendental l y) :
    hgt l p B y = 0 ↔ y ∈ model l B ∧ modelD l B y ≠ 0 := by
  sorry

/-- **Blueprint Lemma 4.3(c)**: the line `L_B · d y ⊆ Ω_B` is the same for all model generators
`y` of a point. -/
theorem span_modelD_eq_of_hgt_eq_zero (hB : IsTranscendenceBasis l B) {y y' : L}
    (h : SamePoint l y y') (hy : hgt l p B y = 0) (hy' : hgt l p B y' = 0) :
    (model l B) ∙ modelD l B y = (model l B) ∙ modelD l B y' := by
  sorry

/-- `ht(lev(Frob^j y)) = ht(lev y) + j`. -/
theorem hgt_frobZ (hB : IsTranscendenceBasis l B) {y : L} (hy : Transcendental l y) (j : ℤ) :
    hgt l p B (frobZ L p j y) = hgt l p B y + j := by
  sorry

/-- Heights and levels: `hgt y - hgt y' = lev(y) - lev(y')` for `y, y'` in the same point
(Definition 4.4: `ht_B(α) = α - λ_B(P)`). -/
theorem hgt_sub_hgt (hB : IsTranscendenceBasis l B) {y y' : L} (h : SamePoint l y y') :
    hgt l p B y - hgt l p B y' = levDiff l p y y' := by
  sorry

/-- The elements of the transcendence basis `B` are model generators: `hgt (B i) = 0`. -/
theorem hgt_apply (hB : IsTranscendenceBasis l B) (i : ι) : hgt l p B (B i) = 0 := by
  sorry

/-- The canonical model generator `Frob^{-hgt y} y` has height `0`. -/
theorem hgt_frobZ_neg_hgt (hB : IsTranscendenceBasis l B) {y : L} (hy : Transcendental l y) :
    hgt l p B (frobZ L p (-hgt l p B y) y) = 0 := by
  rw [hgt_frobZ p hB hy, add_neg_cancel]

end PointsInModel

section Lines

omit [IsRelAlgClosed l L] in
/-- If `y` is a model generator (`hgt y = 0`), then `ω_B(Q_y) = L_B · d y` (Definition 4.4). -/
theorem omega_eq_span_of_hgt_eq_zero {y : L} (hy : hgt l p B y = 0) :
    omega l p B y = (model l B) ∙ modelD l B y := by
  rw [omega, hy, neg_zero, frobZ_zero_apply]

/-- **Blueprint Lemma 4.3(c)** / Definition 4.4: the line `ω_B(Q_y)` only depends on the point
`Q_y`. -/
theorem omega_eq_of_samePoint (hB : IsTranscendenceBasis l B) {y y' : L} (h : SamePoint l y y') :
    omega l p B y = omega l p B y' := by
  sorry

/-- The line `ω_B(Q_y)` of a point is a line: it is spanned by a non-zero vector. -/
theorem omega_ne_bot (hB : IsTranscendenceBasis l B) {y : L} (hy : Transcendental l y) :
    omega l p B y ≠ ⊥ := by
  sorry

/-- `ω_B(Q_{B i}) = L_B · d (B i)`. -/
theorem omega_apply (hB : IsTranscendenceBasis l B) (i : ι) :
    omega l p B (B i) = (model l B) ∙ modelD l B (B i) :=
  omega_eq_span_of_hgt_eq_zero p (hgt_apply p hB i)

/-- **Blueprint Lemma 4.5 (Lax property)**: if `y : κ → L` are transcendental and algebraically
dependent over `l` (e.g. elements of distinct points `P₁, …, P_m` with `rk {P₁, …, P_m} < m`),
then the differentials of model generators of their points are linearly dependent in `Ω_B`, i.e.
the lines `ω_B(Q_{yₖ})` are linearly dependent. (See also the general form
`algebraicIndependent_of_linearIndependent_modelD`.) -/
theorem not_linearIndependent_modelD_of_not_algebraicIndependent (hB : IsTranscendenceBasis l B)
    {y : κ → L} (hy : ∀ k, Transcendental l (y k)) (hdep : ¬ AlgebraicIndependent l y) :
    ¬ LinearIndependent (model l B) fun k ↦ modelD l B (frobZ L p (-hgt l p B (y k)) (y k)) := by
  sorry

/-- Propagation, first half (from Lemma 4.5): if a point `X = Q_x` lies on the line `⟨Q, R⟩`
(`x` algebraic over `l(q, r)`) and `ω_B(Q) ≠ ω_B(R)`, then `ω_B(X) ⊆ ω_B(Q) + ω_B(R)`. -/
theorem omega_le_sup_of_isAlgebraic (hB : IsTranscendenceBasis l B) {x q r : L}
    (hx : Transcendental l x) (hq : Transcendental l q) (hr : Transcendental l r)
    (hxqr : IsAlgebraic l⟮q, r⟯ x) (hne : omega l p B q ≠ omega l p B r) :
    omega l p B x ≤ omega l p B q ⊔ omega l p B r := by
  sorry

/-- **Propagation** (blueprint lines 342-344): if a point `X = Q_x` is collinear with `Q₁, Q₂` and
with `R₁, R₂`, where `ω_B(Q₁) ≠ ω_B(Q₂)`, `ω_B(R₁) ≠ ω_B(R₂)` and the planes
`ω_B(Q₁) + ω_B(Q₂)`, `ω_B(R₁) + ω_B(R₂)` are distinct, then `ω_B(X)` is their intersection. -/
theorem omega_eq_inf_of_isAlgebraic (hB : IsTranscendenceBasis l B) {x q₁ q₂ r₁ r₂ : L}
    (hx : Transcendental l x) (hq₁ : Transcendental l q₁) (hq₂ : Transcendental l q₂)
    (hr₁ : Transcendental l r₁) (hr₂ : Transcendental l r₂)
    (hxq : IsAlgebraic l⟮q₁, q₂⟯ x) (hxr : IsAlgebraic l⟮r₁, r₂⟯ x)
    (hq : omega l p B q₁ ≠ omega l p B q₂) (hr : omega l p B r₁ ≠ omega l p B r₂)
    (hqr : omega l p B q₁ ⊔ omega l p B q₂ ≠ omega l p B r₁ ⊔ omega l p B r₂) :
    omega l p B x = (omega l p B q₁ ⊔ omega l p B q₂) ⊓ (omega l p B r₁ ⊔ omega l p B r₂) := by
  sorry

end Lines

end MilnorAlgDep
