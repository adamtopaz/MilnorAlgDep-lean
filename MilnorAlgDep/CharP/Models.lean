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
* Auxiliary: `bddAbove_frobZ_neg_mem_model` ((S3) for `L_B`: the set defining `hgt` is bounded
  above), `hgt_eq_of_sepEquiv` (`hgt` is constant on `≈`-classes), and two facts about lines and
  planes in a vector space (`linearIndependent_pair_of_span_singleton_ne`,
  `span_singleton_eq_inf_of_le`).

## Proof notes

The set `{j | Frob^{-j} y ∈ L_B}` is downward closed (`L_B` is a field, so stable under `Frob`),
non-empty by Lemma 4.2(c) and, for `y` transcendental, bounded above by (S3) applied to
`E = L_B`; so `hgt y` is its maximum, which is Lemma 4.3(a). Lemma 4.3(b) is the kernel statement
`ker (d : L_B → Ω_B) = L_B ^ p` of (S3). Instead of the case analysis on `i` in the blueprint's
proof, the relation with levels comes from two facts: `hgt` is constant on `≈`-classes (`≈` is
invariant under `Frob` and `L_B` is a union of `≈`-classes) and `hgt (Frob^j y) = hgt y + j`.
Then `y ≈ Frob^(lev y - lev y') y'` (Lemma 3.2) gives `hgt_sub_hgt`, and Lemma 4.3(c) follows
because `s ≈ t` implies `L_B d s = L_B d t`. The lax property for points is the general form
`algebraicIndependent_of_linearIndependent_modelD` applied to model generators, and propagation
follows from it by linear algebra.
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

section HeightSet

/-! ### The set defining the height

`hgt l p B y` is the supremum of `{j | Frob^{-j} y ∈ L_B}`. This set is downward closed (`L_B` is
stable under `Frob`), non-empty (Lemma 4.2(c)) and, for `y` transcendental, bounded above
((S3) for `E = L_B`). -/

omit [IsRelAlgClosed l L] in
/-- The set `{j | Frob^{-j} y ∈ L_B}` is downward closed: `L_B` is stable under `Frob`. -/
theorem frobZ_neg_mem_model_of_le {y : L} {i j : ℤ} (hj : frobZ L p (-j) y ∈ model l B)
    (hij : i ≤ j) : frobZ L p (-i) y ∈ model l B := by
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 hij)
  rw [show -i = (n : ℤ) + -j by omega, frobZ_add_apply, frobZ_natCast_apply]
  exact pow_mem hj _

omit [IsRelAlgClosed l L] in
/-- **Blueprint Lemma 4.2(c)**, with `Frob`: for `B` a transcendence basis, every `y` lies in some
`Frob^j(L_B)`. -/
theorem exists_frobZ_neg_mem_model (hB : IsTranscendenceBasis l B) (y : L) :
    ∃ j : ℤ, frobZ L p (-j) y ∈ model l B := by
  have : Algebra.IsAlgebraic (adjoin l (Set.range B)) L := hB.isAlgebraic_field
  obtain ⟨n, hn⟩ := exists_pow_pow_mem_model (l := l) (B := B) p (Algebra.IsAlgebraic.isAlgebraic y)
  exact ⟨-n, by rwa [neg_neg, frobZ_natCast_apply]⟩

/-- (S3) for the model: if `y` is transcendental over `l`, then `Frob^{-j} y ∈ L_B` only for `j`
bounded above. -/
theorem bddAbove_frobZ_neg_mem_model (hB : IsTranscendenceBasis l B) {y : L}
    (hy : Transcendental l y) : BddAbove {j : ℤ | frobZ L p (-j) y ∈ model l B} := by
  have : PerfectField l := IsRelAlgClosed.perfectField l L
  have : CharP (model l B) p := (Algebra.charP_iff (model l B) L p).mpr inferInstance
  obtain ⟨j₀, hj₀⟩ := exists_frobZ_neg_mem_model p hB y
  have hz : (⟨_, hj₀⟩ : model l B) ∉ (algebraMap l (model l B)).range := by
    rintro ⟨c, hc⟩
    obtain ⟨c', hc'⟩ := frobZ_algebraMap_mem_range (L := L) p j₀ c
    have hc'' : algebraMap l L c = frobZ L p (-j₀) y := congrArg Subtype.val hc
    rw [hc'', frobZ_apply_frobZ_neg] at hc'
    exact hy (hc' ▸ isAlgebraic_algebraMap c')
  have hl := relAlgClosed_intermediateField (model l B) fun x hx ↦ IsRelAlgClosed.mem_range hx
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ¬ ∃ w, w ^ p ^ n = (⟨_, hj₀⟩ : model l B) := by
    by_contra h
    push Not at h
    exact not_forall_exists_pow_pow_eq p (algebraicIndependent_restrictFamily_model hB.1)
      (isSeparable_adjoin_restrictFamily_model B) hl hz h
  refine ⟨j₀ + n - 1, fun j hj ↦ ?_⟩
  by_contra hlt
  have hmem := frobZ_neg_mem_model_of_le (i := j₀ + n) p hj (by omega)
  refine hn ⟨⟨_, hmem⟩, Subtype.ext ?_⟩
  rw [SubmonoidClass.coe_pow, ← frobZ_natCast_apply, ← frobZ_add_apply,
    show (n : ℤ) + -(j₀ + n) = -j₀ by ring]

/-- If `s ≈ t` then `hgt s = hgt t`: `Frob^{-j} s ≈ Frob^{-j} t`, so one lies in `L_B` iff the
other does. -/
theorem hgt_eq_of_sepEquiv {s t : L} (h : SepEquiv l s t) : hgt l p B s = hgt l p B t := by
  unfold hgt
  congr 1
  ext j
  have h' := (sepEquiv_frobZ_iff p (-j)).2 h
  exact ⟨h'.mem_model, h'.symm.mem_model⟩

end HeightSet

section PointsInModel

/-- **Blueprint Lemma 4.3(a)**: for `y ∈ L \ l`, `y ∈ Frob^j(L_B)` (i.e. `Frob^{-j} y ∈ L_B`) iff
`lev(y) ≥ λ_B(Q_y) + j`, i.e. `j ≤ hgt y`. -/
theorem frobZ_neg_mem_model_iff (hB : IsTranscendenceBasis l B) {y : L} (hy : Transcendental l y)
    (j : ℤ) : frobZ L p (-j) y ∈ model l B ↔ j ≤ hgt l p B y := by
  obtain ⟨j₀, hj₀⟩ := exists_frobZ_neg_mem_model p hB y
  have hbdd := bddAbove_frobZ_neg_mem_model p hB hy
  exact ⟨fun h ↦ le_csSup hbdd h,
    fun h ↦ frobZ_neg_mem_model_of_le p (Int.csSup_mem ⟨j₀, hj₀⟩ hbdd) h⟩

/-- **Blueprint Lemma 4.3(a)** for `j = 0`: `y ∈ L_B` iff `hgt y ≥ 0`. -/
theorem mem_model_iff_hgt_nonneg (hB : IsTranscendenceBasis l B) {y : L}
    (hy : Transcendental l y) : y ∈ model l B ↔ 0 ≤ hgt l p B y := by
  rw [← frobZ_neg_mem_model_iff p hB hy 0, neg_zero, frobZ_zero_apply]

/-- **Blueprint Lemma 4.3(b)**: for `y ∈ L \ l`, `y ∈ L_B` and `d y ≠ 0` in `Ω_B` iff
`lev(y) = λ_B(Q_y)`, i.e. `hgt y = 0` (`y` is a *model generator* of `Q_y`). -/
theorem hgt_eq_zero_iff (hB : IsTranscendenceBasis l B) {y : L} (hy : Transcendental l y) :
    hgt l p B y = 0 ↔ y ∈ model l B ∧ modelD l B y ≠ 0 := by
  have : PerfectField l := IsRelAlgClosed.perfectField l L
  have : CharP (model l B) p := (Algebra.charP_iff (model l B) L p).mpr inferInstance
  constructor
  · intro h0
    have hmem : y ∈ model l B := (mem_model_iff_hgt_nonneg p hB hy).2 h0.ge
    refine ⟨hmem, fun hd ↦ ?_⟩
    rw [modelD_of_mem hmem, kaehler_D_eq_zero_iff_exists_pow_eq p
      (algebraicIndependent_restrictFamily_model hB.1) (isSeparable_adjoin_restrictFamily_model B)]
      at hd
    obtain ⟨w, hw⟩ := hd
    have hw' : frobZ L p (-1) y = w := by
      have hw' : (w : L) ^ p = y := congrArg Subtype.val hw
      rw [← hw', ← frobZ_one_apply, frobZ_neg_apply_frobZ]
    have := (frobZ_neg_mem_model_iff p hB hy 1).1 (hw' ▸ w.2)
    omega
  · rintro ⟨hmem, hd⟩
    have h0 := (mem_model_iff_hgt_nonneg p hB hy).1 hmem
    by_contra hne
    have h1 := (frobZ_neg_mem_model_iff p hB hy 1).2 (by omega)
    refine hd ?_
    rw [show y = frobZ L p (-1) y ^ p by rw [← frobZ_one_apply, frobZ_apply_frobZ_neg]]
    exact modelD_pow_char p h1

/-- `ht(lev(Frob^j y)) = ht(lev y) + j`. -/
theorem hgt_frobZ (hB : IsTranscendenceBasis l B) {y : L} (hy : Transcendental l y) (j : ℤ) :
    hgt l p B (frobZ L p j y) = hgt l p B y + j := by
  have hy' : Transcendental l (frobZ L p j y) := (transcendental_frobZ_iff p j).2 hy
  have key : ∀ i, i ≤ hgt l p B (frobZ L p j y) ↔ i ≤ hgt l p B y + j := by
    intro i
    rw [← frobZ_neg_mem_model_iff p hB hy', ← frobZ_add_apply, show -i + j = -(i - j) by ring,
      frobZ_neg_mem_model_iff p hB hy]
    constructor <;> intro h <;> omega
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

/-- Heights and levels: `hgt y - hgt y' = lev(y) - lev(y')` for `y, y'` in the same point
(Definition 4.4: `ht_B(α) = α - λ_B(P)`). -/
theorem hgt_sub_hgt (hB : IsTranscendenceBasis l B) {y y' : L} (h : SamePoint l y y') :
    hgt l p B y - hgt l p B y' = levDiff l p y y' := by
  rw [hgt_eq_of_sepEquiv p (levDiff_spec p h), hgt_frobZ p hB h.transcendental_right]
  ring

/-- **Blueprint Lemma 4.3(c)**: the line `L_B · d y ⊆ Ω_B` is the same for all model generators
`y` of a point. -/
theorem span_modelD_eq_of_hgt_eq_zero (hB : IsTranscendenceBasis l B) {y y' : L}
    (h : SamePoint l y y') (hy : hgt l p B y = 0) (hy' : hgt l p B y' = 0) :
    (model l B) ∙ modelD l B y = (model l B) ∙ modelD l B y' := by
  have hlev : levDiff l p y y' = 0 := by rw [← hgt_sub_hgt p hB h, hy, hy', sub_zero]
  have hmem := ((hgt_eq_zero_iff p hB h.transcendental_left).1 hy).1
  exact ((levDiff_eq_zero_iff p h).1 hlev).span_modelD_eq hmem

/-- The elements of the transcendence basis `B` are model generators: `hgt (B i) = 0`. -/
theorem hgt_apply (hB : IsTranscendenceBasis l B) (i : ι) : hgt l p B (B i) = 0 := by
  refine (hgt_eq_zero_iff p hB (hB.1.transcendental i)).2 ⟨self_mem_model B i, ?_⟩
  rw [← modelBasis_apply hB.1]
  exact (modelBasis hB.1).ne_zero i

/-- The canonical model generator `Frob^{-hgt y} y` has height `0`. -/
theorem hgt_frobZ_neg_hgt (hB : IsTranscendenceBasis l B) {y : L} (hy : Transcendental l y) :
    hgt l p B (frobZ L p (-hgt l p B y) y) = 0 := by
  rw [hgt_frobZ p hB hy, add_neg_cancel]

/-- Two elements of the same point with the same height are `≈`-equivalent. -/
theorem sepEquiv_of_hgt_eq {B : ι → L} (hB : IsTranscendenceBasis l B) {s t : L}
    (h : SamePoint l s t) (hst : hgt l p B s = hgt l p B t) : SepEquiv l s t :=
  (levDiff_eq_zero_iff p h).1 (by rw [← hgt_sub_hgt p hB h, hst, sub_self])

/-- If `s, t` lie in the same point and `ht s ≥ ht t`, then `s` is separable over `l(t)`. -/
theorem isSeparable_of_hgt_le {B : ι → L} (hB : IsTranscendenceBasis l B) {s t : L}
    (h : SamePoint l s t) (hst : hgt l p B t ≤ hgt l p B s) : IsSeparable l⟮t⟯ s :=
  (levDiff_nonneg_iff p h).1 (by rw [← hgt_sub_hgt p hB h]; omega)

end PointsInModel

section LinearAlgebra

/-! ### Lines and planes in a vector space -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- Two non-zero vectors spanning distinct lines are linearly independent. -/
theorem linearIndependent_pair_of_span_singleton_ne {a b : V} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : K ∙ a ≠ K ∙ b) : LinearIndependent K ![a, b] := by
  rw [linearIndependent_fin2]
  refine ⟨hb, fun t ht ↦ h ?_⟩
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at ht
  have ht0 : t ≠ 0 := by
    rintro rfl
    rw [zero_smul] at ht
    exact ha ht.symm
  rw [← ht, Submodule.span_singleton_smul_eq (IsUnit.mk0 t ht0)]

theorem span_range_pair (a b : V) : Submodule.span K (Set.range ![a, b]) = K ∙ a ⊔ K ∙ b := by
  rw [Matrix.range_cons_cons_empty, Submodule.span_insert]

/-- A line contained in two distinct planes is their intersection. -/
theorem span_singleton_eq_inf_of_le {v a b c d : V} (hv : v ≠ 0)
    (hab : LinearIndependent K ![a, b]) (hcd : LinearIndependent K ![c, d])
    (hne : K ∙ a ⊔ K ∙ b ≠ K ∙ c ⊔ K ∙ d) (h₁ : K ∙ v ≤ K ∙ a ⊔ K ∙ b)
    (h₂ : K ∙ v ≤ K ∙ c ⊔ K ∙ d) : K ∙ v = (K ∙ a ⊔ K ∙ b) ⊓ (K ∙ c ⊔ K ∙ d) := by
  have hP := finrank_span_eq_card hab
  have hR := finrank_span_eq_card hcd
  rw [span_range_pair, Fintype.card_fin] at hP hR
  set P := K ∙ a ⊔ K ∙ b
  set R := K ∙ c ⊔ K ∙ d
  refine Submodule.eq_of_le_of_finrank_le (le_inf h₁ h₂) ?_
  rw [finrank_span_singleton hv]
  by_contra hlt
  push Not at hlt
  have e₁ : P ⊓ R = P := Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
  have e₂ : P ⊓ R = R := Submodule.eq_of_le_of_finrank_le inf_le_right (by omega)
  exact hne (e₁.symm.trans e₂)

/-- A non-zero vector of the line `K ∙ v` spans it. -/
theorem span_singleton_eq_of_mem {v w : V} (hw : w ≠ 0) (h : w ∈ K ∙ v) : K ∙ w = K ∙ v := by
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 h
  exact Submodule.span_singleton_smul_eq (left_ne_zero_of_smul hw).isUnit v

/-- Two lines `K ∙ v`, `K ∙ w` are different if a linear form vanishes at `w` but not at `v`. -/
theorem span_singleton_ne_of_apply (f : V →ₗ[K] K) {v w : V} (hv : f v ≠ 0) (hw : f w = 0) :
    K ∙ v ≠ K ∙ w := by
  intro h
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (h ▸ Submodule.mem_span_singleton_self v)
  rw [← hr, map_smul, hw, smul_zero] at hv
  exact hv rfl

/-- If a non-zero vector `u` of the plane `K ∙ v ⊔ K ∙ w` spans a line different from `K ∙ v` and
from `K ∙ w`, then `u = s • v + t • w` with `s, t ≠ 0`. -/
theorem exists_smul_add_smul_of_mem_sup {u v w : V} (hu : u ≠ 0) (h : u ∈ K ∙ v ⊔ K ∙ w)
    (hv : K ∙ u ≠ K ∙ v) (hw : K ∙ u ≠ K ∙ w) :
    ∃ s t : K, s ≠ 0 ∧ t ≠ 0 ∧ u = s • v + t • w := by
  obtain ⟨_, hv', _, hw', rfl⟩ := Submodule.mem_sup.1 h
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hv'
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hw'
  refine ⟨s, t, fun hs ↦ ?_, fun ht ↦ ?_, rfl⟩
  · rw [hs, zero_smul, zero_add] at hu hw
    exact hw (Submodule.span_singleton_smul_eq (left_ne_zero_of_smul hu).isUnit w)
  · rw [ht, zero_smul, add_zero] at hu hv
    exact hv (Submodule.span_singleton_smul_eq (left_ne_zero_of_smul hu).isUnit v)

end LinearAlgebra

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
  have h₀ : SamePoint l (frobZ L p (-hgt l p B y) y) (frobZ L p (-hgt l p B y') y') :=
    (samePoint_frobZ_left_iff p _).2 ((samePoint_frobZ_right_iff p _).2 h)
  exact span_modelD_eq_of_hgt_eq_zero p hB h₀ (hgt_frobZ_neg_hgt p hB h.transcendental_left)
    (hgt_frobZ_neg_hgt p hB h.transcendental_right)

/-- The line `ω_B(Q_y)` of a point is a line: it is spanned by a non-zero vector. -/
theorem omega_ne_bot (hB : IsTranscendenceBasis l B) {y : L} (hy : Transcendental l y) :
    omega l p B y ≠ ⊥ := by
  have hy₀ : Transcendental l (frobZ L p (-hgt l p B y) y) := (transcendental_frobZ_iff p _).2 hy
  rw [omega, Ne, Submodule.span_singleton_eq_bot]
  exact ((hgt_eq_zero_iff p hB hy₀).1 (hgt_frobZ_neg_hgt p hB hy)).2

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
  have : PerfectField l := IsRelAlgClosed.perfectField l L
  -- `y₀ k = Frob^{-hgt (y k)} (y k)` is a model generator of `Q_{y k}`
  have hmem (k : κ) : frobZ L p (-hgt l p B (y k)) (y k) ∈ model l B :=
    ((hgt_eq_zero_iff p hB ((transcendental_frobZ_iff p _).2 (hy k))).1
      (hgt_frobZ_neg_hgt p hB (hy k))).1
  intro hli
  refine hdep (algebraicIndependent_of_isAlgebraic_adjoin
    (algebraicIndependent_of_linearIndependent_modelD hmem hli) (fun k ↦ ?_) (fun k ↦ ?_))
  · rw [← mem_point_iff, ← point_frobZ p (-hgt l p B (y k)) (y k)]
    exact self_mem_point _
  · rw [← mem_point_iff, point_frobZ]
    exact self_mem_point _

/-- Propagation, first half (from Lemma 4.5): if a point `X = Q_x` lies on the line `⟨Q, R⟩`
(`x` algebraic over `l(q, r)`) and `ω_B(Q) ≠ ω_B(R)`, then `ω_B(X) ⊆ ω_B(Q) + ω_B(R)`. -/
theorem omega_le_sup_of_isAlgebraic (hB : IsTranscendenceBasis l B) {x q r : L}
    (hx : Transcendental l x) (hq : Transcendental l q) (hr : Transcendental l r)
    (hxqr : IsAlgebraic l⟮q, r⟯ x) (hne : omega l p B q ≠ omega l p B r) :
    omega l p B x ≤ omega l p B q ⊔ omega l p B r := by
  have hdep : ¬ AlgebraicIndependent l ![x, q, r] := by
    intro hind
    have h := hind.transcendental_adjoin (s := {1, 2}) (i := 0) (by decide)
    rw [Set.image_pair] at h
    exact h (IntermediateField.isAlgebraic_adjoin_iff.1 hxqr)
  have hlax := not_linearIndependent_modelD_of_not_algebraicIndependent p hB (y := ![x, q, r])
    (fun k ↦ by fin_cases k <;> assumption) hdep
  have hq₀ := omega_ne_bot p hB hq
  have hr₀ := omega_ne_bot p hB hr
  rw [omega, Ne, Submodule.span_singleton_eq_bot] at hq₀ hr₀
  have hqr := linearIndependent_pair_of_span_singleton_ne hq₀ hr₀ hne
  have hfun : (fun k ↦ modelD l B (frobZ L p (-hgt l p B (![x, q, r] k)) (![x, q, r] k))) =
      Fin.cons (modelD l B (frobZ L p (-hgt l p B x) x))
        ![modelD l B (frobZ L p (-hgt l p B q) q), modelD l B (frobZ L p (-hgt l p B r) r)] := by
    funext k
    fin_cases k <;> rfl
  rw [hfun, linearIndependent_finCons, not_and, not_not, span_range_pair] at hlax
  rw [omega, omega, omega, Submodule.span_singleton_le_iff_mem]
  exact hlax hqr

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
  have h₁ := omega_le_sup_of_isAlgebraic p hB hx hq₁ hq₂ hxq hq
  have h₂ := omega_le_sup_of_isAlgebraic p hB hx hr₁ hr₂ hxr hr
  have hne : ∀ {y : L}, Transcendental l y → modelD l B (frobZ L p (-hgt l p B y) y) ≠ 0 := by
    intro y hy
    have := omega_ne_bot p hB hy
    rwa [omega, Ne, Submodule.span_singleton_eq_bot] at this
  unfold omega at *
  exact span_singleton_eq_inf_of_le (hne hx)
    (linearIndependent_pair_of_span_singleton_ne (hne hq₁) (hne hq₂) hq)
    (linearIndependent_pair_of_span_singleton_ne (hne hr₁) (hne hr₂) hr) hqr h₁ h₂

/-- `ω_B(Q_{Frob^j y}) = ω_B(Q_y)`: points are stable under Frobenius. -/
theorem omega_frobZ (hB : IsTranscendenceBasis l B) {y : L} (hy : Transcendental l y) (j : ℤ) :
    omega l p B (frobZ L p j y) = omega l p B y :=
  omega_eq_of_samePoint p hB ((samePoint_frobZ_left_iff p j).2 (samePoint_refl hy))

end Lines

end MilnorAlgDep
