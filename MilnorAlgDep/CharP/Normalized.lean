module

public import MilnorAlgDep.CharP.Levels

/-!
# Normalized triples

Blueprint, Section 3.2: Definition 3.4 (normalized triples), Lemma 3.5 and level triples,
element-wise.

Three distinct collinear points `P, Q, R` are given by elements `x ∈ P, y ∈ Q, z ∈ R` which are
pairwise algebraically independent over `l` and jointly dependent
(`MilnorAlgDep.IsCollinearTriple l x y z`). Such a triple is *normalized*
(`MilnorAlgDep.IsNormalized l x y z`) if each of `x, y, z` is separable algebraic over the field
generated over `l` by the other two.

The *level triple* `lt(P, Q, R)`, the diagonal `Γ`-orbit of the levels of normalized triples, is
recorded relative to a given collinear triple `(x, y, z)`: `levelTriple l p x y z = (j, k)` is
the unique pair with `(x, Frob^j y, Frob^k z)` normalized, so that
`(lev x, lev y + j, lev z + k)` is a level triple of `(Q_x, Q_y, Q_z)` (Lemma 3.5,
`isNormalized_levelTriple`, `levelTriple_eq_of_isNormalized`). For example, the integer `c(u, w)`
of blueprint (6.2) is `(levelTriple l p a b d).1` for representatives `a, b, d` of
`ψ(u), ψ(w), ψ(u + w)`.

## Main definitions

* `MilnorAlgDep.IsCollinearTriple l x y z`: `Q_x, Q_y, Q_z` are three distinct collinear points.
* `MilnorAlgDep.IsNormalized l x y z`: Definition 3.4 (including `IsCollinearTriple l x y z`).
* `MilnorAlgDep.levelTriple l p x y z : ℤ × ℤ`: the level triple of `(Q_x, Q_y, Q_z)` relative to
  `(x, y, z)` (`0` if `¬ IsCollinearTriple l x y z`).

## Main statements

* `exists_isNormalized` (Lemma 3.5(a)): `(x, Frob^j y, Frob^k z)` is normalized for some `j, k`.
* `IsNormalized.isNormalized_iff` (Lemma 3.5(b)): if `(x, y, z)` is normalized, then for
  `x', y', z'` in the same points, `(x', y', z')` is normalized iff
  `lev x' - lev x = lev y' - lev y = lev z' - lev z`.
* `IsNormalized.of_sepEquiv` (the "if" part of Lemma 3.5(b)), `IsNormalized.frobZ_iff`.
* `isNormalized_of_linearIndependent_modelD`: elements of a model with pairwise linearly
  independent differentials which are collinear form a normalized triple (the mechanism behind
  Lemma 4.6(d); also the convenient way to check normalization in the proof of Lemma 6.2).
* `isNormalized_mul`: `(x, y, x y)` is normalized (used in the proof of Lemma 6.11).
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential IntermediateField

variable {l L : Type*} [Field l] [Field L] [Algebra l L]

section Defs

variable (l) in
/-- `Q_x, Q_y, Q_z` are three distinct collinear points (blueprint Section 2.1): `x, y, z` are
pairwise algebraically independent over `l` and `z` is algebraic over `l(x, y)`. (This is
symmetric in `x, y, z`, see `IsCollinearTriple.swap₁₂`, `IsCollinearTriple.swap₂₃`.) -/
structure IsCollinearTriple (x y z : L) : Prop where
  indep₁₂ : AlgebraicIndependent l ![x, y]
  indep₁₃ : AlgebraicIndependent l ![x, z]
  indep₂₃ : AlgebraicIndependent l ![y, z]
  isAlgebraic : IsAlgebraic l⟮x, y⟯ z

variable (l) in
/-- **Blueprint Definition 3.4**: for three distinct collinear points `P, Q, R`, a triple
`(x, y, z)` with `x ∈ P \ l`, `y ∈ Q \ l`, `z ∈ R \ l` is *normalized* if each of `x, y, z` is
separable algebraic over the field generated over `l` by the other two. The hypothesis on the
points is part of the definition (`IsNormalized.toIsCollinearTriple`). -/
structure IsNormalized (x y z : L) : Prop extends IsCollinearTriple l x y z where
  isSeparable₁ : IsSeparable l⟮y, z⟯ x
  isSeparable₂ : IsSeparable l⟮x, z⟯ y
  isSeparable₃ : IsSeparable l⟮x, y⟯ z

end Defs

section LinearAlgebra

/-! ### Pairs of vectors in a vector space -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {u v w : V}

theorem notMem_span_singleton_of_linearIndependent_pair (h : LinearIndependent K ![u, v]) :
    v ∉ K ∙ u := by
  rw [Submodule.mem_span_singleton]
  have hu : u ≠ 0 := by simpa using h.ne_zero 0
  exact fun ⟨a, ha⟩ ↦ (LinearIndependent.pair_iff' hu).1 h a ha

theorem linearIndependent_pair_of_mem_span_pair (h : LinearIndependent K ![u, v])
    (hv : v ∈ Submodule.span K {u, w}) : LinearIndependent K ![u, w] := by
  have hu : u ≠ 0 := by simpa using h.ne_zero 0
  rw [LinearIndependent.pair_iff' hu]
  rintro a rfl
  apply notMem_span_singleton_of_linearIndependent_pair h
  obtain ⟨c, d, hcd⟩ := Submodule.mem_span_pair.1 hv
  rw [Submodule.mem_span_singleton]
  exact ⟨c + d * a, by rw [← hcd, smul_smul, add_smul]⟩

theorem linearIndependent_pair_smul_add_left (h : LinearIndependent K ![u, v]) (a : K) {b : K}
    (hb : b ≠ 0) : LinearIndependent K ![u, a • u + b • v] := by
  have hu : u ≠ 0 := by simpa using h.ne_zero 0
  rw [LinearIndependent.pair_iff' hu]
  intro c hc
  have := (LinearIndependent.pair_iff.1 h) (a - c) b (by rw [sub_smul, hc]; abel)
  exact hb this.2

theorem linearIndependent_pair_smul_add_right (h : LinearIndependent K ![u, v]) {a : K}
    (ha : a ≠ 0) (b : K) : LinearIndependent K ![v, a • u + b • v] := by
  have hv : v ≠ 0 := by simpa using h.ne_zero 1
  rw [LinearIndependent.pair_iff' hv]
  intro c hc
  have := (LinearIndependent.pair_iff.1 h) a (b - c) (by rw [sub_smul, hc]; abel)
  exact ha this.1

/-- A line contains at most one of two linearly independent vectors. -/
theorem notMem_span_singleton_of_mem_of_linearIndependent {u u' v : V}
    (h : LinearIndependent K ![u, u']) (hu : u ∈ K ∙ v) : u' ∉ K ∙ v := by
  intro hu'
  obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.1 hu
  have hα : α ≠ 0 := by
    rintro rfl
    simpa using h.ne_zero 0
  apply notMem_span_singleton_of_linearIndependent_pair h
  obtain ⟨β, rfl⟩ := Submodule.mem_span_singleton.1 hu'
  exact Submodule.mem_span_singleton.2
    ⟨β * α⁻¹, by rw [smul_smul, mul_assoc, inv_mul_cancel₀ hα, mul_one]⟩

/-- If `e₁, e₂` are linearly independent, so are `α e₁ + β e₂` and `γ e₁ + δ e₂` when
`α δ - β γ ≠ 0`. -/
theorem linearIndependent_pair_smul_add {R M : Type*} [Field R] [AddCommGroup M] [Module R M]
    {e₁ e₂ : M} (h : LinearIndependent R ![e₁, e₂]) {α β γ δ : R}
    (hdet : α * δ - β * γ ≠ 0) : LinearIndependent R ![α • e₁ + β • e₂, γ • e₁ + δ • e₂] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  obtain ⟨h₁, h₂⟩ := LinearIndependent.pair_iff.1 h (s * α + t * γ) (s * β + t * δ) (by
    rw [← hst]
    simp only [add_smul, mul_smul, smul_add]
    abel)
  have hs : s * (α * δ - β * γ) = 0 := by linear_combination δ * h₁ - γ * h₂
  have ht : t * (α * δ - β * γ) = 0 := by linear_combination α * h₂ - β * h₁
  exact ⟨(mul_eq_zero.1 hs).resolve_right hdet, (mul_eq_zero.1 ht).resolve_right hdet⟩

end LinearAlgebra

section Collinear

variable {x y z : L}

theorem IsCollinearTriple.transcendental₁ (h : IsCollinearTriple l x y z) : Transcendental l x :=
  (algebraicIndependent_pair_iff.1 h.indep₁₂).1

theorem IsCollinearTriple.transcendental₂ (h : IsCollinearTriple l x y z) : Transcendental l y :=
  (algebraicIndependent_pair_iff.1 h.indep₂₃).1

theorem IsCollinearTriple.transcendental₃ (h : IsCollinearTriple l x y z) : Transcendental l z :=
  (algebraicIndependent_pair_iff.1 (algebraicIndependent_pair_comm.1 h.indep₂₃)).1

theorem isAlgebraic_adjoin_pair_iff_mem_closure {x y z : L} :
    IsAlgebraic l⟮x, y⟯ z ↔ z ∈ (AlgebraicIndependent.matroid l L).closure {x, y} := by
  rw [mem_matroid_closure_iff, IntermediateField.isAlgebraic_adjoin_iff]

theorem IsCollinearTriple.swap₁₂ (h : IsCollinearTriple l x y z) : IsCollinearTriple l y x z :=
  ⟨algebraicIndependent_pair_comm.1 h.indep₁₂, h.indep₂₃, h.indep₁₃, by
    rw [Set.pair_comm]; exact h.isAlgebraic⟩

theorem IsCollinearTriple.swap₂₃ (h : IsCollinearTriple l x y z) : IsCollinearTriple l x z y := by
  refine ⟨h.indep₁₃, h.indep₁₂, algebraicIndependent_pair_comm.1 h.indep₂₃, ?_⟩
  set Mt := AlgebraicIndependent.matroid l L
  have hz : z ∈ Mt.closure (insert y {x}) \ Mt.closure {x} := by
    refine ⟨?_, fun hz ↦ ?_⟩
    · rw [Set.pair_comm, ← isAlgebraic_adjoin_pair_iff_mem_closure]
      exact h.isAlgebraic
    · rw [← isAlgebraic_adjoin_simple_iff_mem_closure] at hz
      exact (algebraicIndependent_pair_iff.1 h.indep₁₃).2 hz
  have := (Mt.closure_exchange hz).1
  rw [Set.pair_comm] at this
  exact isAlgebraic_adjoin_pair_iff_mem_closure.2 this

/-- Being three distinct collinear points only depends on the points. -/
theorem IsCollinearTriple.of_samePoint {x' y' z' : L} (h : IsCollinearTriple l x y z)
    (hx : SamePoint l x' x) (hy : SamePoint l y' y) (hz : SamePoint l z' z) :
    IsCollinearTriple l x' y' z' := by
  have pair : ∀ {a b a' b' : L}, AlgebraicIndependent l ![a, b] → SamePoint l a' a →
      SamePoint l b' b → AlgebraicIndependent l ![a', b'] := fun hab ha hb ↦ by
    refine algebraicIndependent_of_isAlgebraic_adjoin hab (fun i ↦ ?_) (fun i ↦ ?_) <;>
      fin_cases i
    exacts [ha.symm.isAlgebraic, hb.symm.isAlgebraic, ha.isAlgebraic, hb.isAlgebraic]
  refine ⟨pair h.indep₁₂ hx hy, pair h.indep₁₃ hx hz, pair h.indep₂₃ hy hz, ?_⟩
  set Mt := AlgebraicIndependent.matroid l L
  rw [isAlgebraic_adjoin_pair_iff_mem_closure]
  have hxy : ({x, y} : Set L) ⊆ Mt.closure {x', y'} := by
    rintro _ (rfl | rfl)
    · exact Mt.closure_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
        (isAlgebraic_adjoin_simple_iff_mem_closure.1 hx.symm.isAlgebraic)
    · exact Mt.closure_mono (Set.subset_insert _ _)
        (isAlgebraic_adjoin_simple_iff_mem_closure.1 hy.symm.isAlgebraic)
  have hz' : z ∈ Mt.closure {x', y'} :=
    Mt.closure_subset_closure_of_subset_closure hxy
      (isAlgebraic_adjoin_pair_iff_mem_closure.1 h.isAlgebraic)
  exact Mt.closure_subset_closure_of_subset_closure (Set.singleton_subset_iff.2 hz')
    (isAlgebraic_adjoin_simple_iff_mem_closure.1 hz.isAlgebraic)

/-- "`Z` lies on the line `⟨X, Y⟩`" only depends on the points `X, Y, Z`: if `z` is algebraic over
`l(x, y)`, then so is `z'` over `l(x', y')` for `x', y', z'` in the points of `x, y, z`. -/
theorem isAlgebraic_adjoin_pair_of_samePoint {x y z x' y' z' : L} (h : IsAlgebraic l⟮x, y⟯ z)
    (hx : SamePoint l x' x) (hy : SamePoint l y' y) (hz : SamePoint l z' z) :
    IsAlgebraic l⟮x', y'⟯ z' := by
  set M := AlgebraicIndependent.matroid l L
  have key : ∀ {s : Set L} {w : L}, IsAlgebraic (adjoin l s) w ↔ w ∈ M.closure s :=
    isAlgebraic_adjoin_iff_mem_closure l
  have hsub : ({x, y} : Set L) ⊆ M.closure {x', y'} := by
    refine Set.insert_subset ?_ (Set.singleton_subset_iff.2 ?_)
    · exact M.closure_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
        (isAlgebraic_adjoin_simple_iff_mem_closure.1 hx.symm.isAlgebraic)
    · exact M.closure_mono (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem _ rfl))
        (isAlgebraic_adjoin_simple_iff_mem_closure.1 hy.symm.isAlgebraic)
  have hz' : z ∈ M.closure {x', y'} := M.closure_subset_closure_of_subset_closure hsub (key.1 h)
  exact key.2 (M.closure_subset_closure_of_subset_closure (Set.singleton_subset_iff.2 hz')
    (isAlgebraic_adjoin_simple_iff_mem_closure.1 hz.isAlgebraic))

theorem IsNormalized.swap₁₂ (h : IsNormalized l x y z) : IsNormalized l y x z :=
  ⟨h.toIsCollinearTriple.swap₁₂, h.isSeparable₂, h.isSeparable₁, by
    rw [Set.pair_comm]; exact h.isSeparable₃⟩

theorem IsNormalized.swap₂₃ (h : IsNormalized l x y z) : IsNormalized l x z y :=
  ⟨h.toIsCollinearTriple.swap₂₃, by rw [Set.pair_comm]; exact h.isSeparable₁, h.isSeparable₃,
    h.isSeparable₂⟩

theorem mem_model_pair_iff {a b w : L} : w ∈ model l ![a, b] ↔ IsSeparable l⟮a, b⟯ w := by
  rw [mem_model_iff, Matrix.range_cons_cons_empty]

/-- Separability over `l(y, z)` only depends on the `≈`-classes. -/
theorem isSeparable_adjoin_pair_of_sepEquiv {x' y' z' : L} (h : IsSeparable l⟮y, z⟯ x)
    (hx : SepEquiv l x' x) (hy : SepEquiv l y' y) (hz : SepEquiv l z' z) :
    IsSeparable l⟮y', z'⟯ x' := by
  rw [← mem_model_pair_iff]
  have hy' : y' ∈ model l ![y', z'] := self_mem_model ![y', z'] 0
  have hz' : z' ∈ model l ![y', z'] := self_mem_model ![y', z'] 1
  have hyM : y ∈ model l ![y', z'] := hy.mem_model hy'
  have hzM : z ∈ model l ![y', z'] := hz.mem_model hz'
  have hxM : x ∈ model l ![y', z'] := by
    refine mem_model_of_isSeparable ?_ h
    rw [adjoin_le_iff]
    rintro _ (rfl | rfl)
    exacts [hyM, hzM]
  exact hx.symm.mem_model hxM

/-- The "if" part of **blueprint Lemma 3.5(b)**: being normalized only depends on the levels, i.e.
on the `≈`-classes of `x, y, z`. -/
theorem IsNormalized.of_sepEquiv {x' y' z' : L} (h : IsNormalized l x y z)
    (hx : SepEquiv l x' x) (hy : SepEquiv l y' y) (hz : SepEquiv l z' z) :
    IsNormalized l x' y' z' :=
  ⟨h.toIsCollinearTriple.of_samePoint (hx.symm.samePoint h.transcendental₁).symm
      (hy.symm.samePoint h.transcendental₂).symm (hz.symm.samePoint h.transcendental₃).symm,
    isSeparable_adjoin_pair_of_sepEquiv h.isSeparable₁ hx hy hz,
    isSeparable_adjoin_pair_of_sepEquiv h.isSeparable₂ hy hx hz,
    isSeparable_adjoin_pair_of_sepEquiv h.isSeparable₃ hz hx hy⟩

theorem algebraicIndependent_pair_of_linearIndependent_modelD [PerfectField l] {ι : Type*}
    {B : ι → L} (hx : x ∈ model l B) (hy : y ∈ model l B)
    (hxy : LinearIndependent (model l B) ![modelD l B x, modelD l B y]) :
    AlgebraicIndependent l ![x, y] := by
  refine algebraicIndependent_of_linearIndependent_modelD (B := B) (fun k ↦ ?_) ?_
  · fin_cases k
    exacts [hx, hy]
  · convert hxy using 1
    ext k
    fin_cases k <;> rfl

/-- Normalization via differentials (the mechanism of blueprint Lemma 4.6(d)): if `x, y, z ∈ L_B`
have pairwise linearly independent differentials in `Ω_B` and `z` is algebraic over `l(x, y)`,
then `(x, y, z)` is normalized. (Pairwise algebraic independence follows from Lemma 4.5 and
separability from `isSeparable_of_linearIndependent_modelD_pair`.) -/
theorem isNormalized_of_linearIndependent_modelD [PerfectField l] {ι : Type*} {B : ι → L}
    (hx : x ∈ model l B) (hy : y ∈ model l B) (hz : z ∈ model l B)
    (hxy : LinearIndependent (model l B) ![modelD l B x, modelD l B y])
    (hxz : LinearIndependent (model l B) ![modelD l B x, modelD l B z])
    (hyz : LinearIndependent (model l B) ![modelD l B y, modelD l B z])
    (halg : IsAlgebraic l⟮x, y⟯ z) : IsNormalized l x y z := by
  have hc : IsCollinearTriple l x y z :=
    ⟨algebraicIndependent_pair_of_linearIndependent_modelD hx hy hxy,
      algebraicIndependent_pair_of_linearIndependent_modelD hx hz hxz,
      algebraicIndependent_pair_of_linearIndependent_modelD hy hz hyz, halg⟩
  exact ⟨hc, isSeparable_of_linearIndependent_modelD_pair hy hz hyz hx hc.swap₁₂.swap₂₃.isAlgebraic,
    isSeparable_of_linearIndependent_modelD_pair hx hz hxz hy hc.swap₂₃.isAlgebraic,
    isSeparable_of_linearIndependent_modelD_pair hx hy hxy hz halg⟩

/-- `(x, y, x y)` is normalized for `x, y` algebraically independent (used in the proof of blueprint
Lemma 6.11). -/
theorem isNormalized_mul (h : AlgebraicIndependent l ![x, y]) : IsNormalized l x y (x * y) := by
  obtain ⟨hx, hxy⟩ := algebraicIndependent_pair_iff.1 h
  obtain ⟨hy, hyx⟩ := algebraicIndependent_pair_iff.1 (algebraicIndependent_pair_comm.1 h)
  have hx0 : x ≠ 0 := fun h0 ↦ hx (h0 ▸ isAlgebraic_zero)
  have hy0 : y ≠ 0 := fun h0 ↦ hy (h0 ▸ isAlgebraic_zero)
  have hxl : x ∈ l⟮x, y⟯ := subset_adjoin _ _ (Set.mem_insert _ _)
  have hyl : y ∈ l⟮x, y⟯ := subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
  -- `x y` is transcendental over `l(a)` for `a ∈ {x, y}`
  have key : ∀ {a b : L}, a ≠ 0 → Transcendental l⟮a⟯ b → Transcendental l⟮a⟯ (a * b) := by
    intro a b ha hb hab
    apply hb
    have hinv : IsIntegral l⟮a⟯ a⁻¹ :=
      isIntegral_algebraMap (x := (⟨a⁻¹, inv_mem (mem_adjoin_simple_self l a)⟩ : l⟮a⟯))
    have := (hinv.mul hab.isIntegral).isAlgebraic
    rwa [← mul_assoc, inv_mul_cancel₀ ha, one_mul] at this
  refine ⟨⟨h, algebraicIndependent_pair_iff.2 ⟨hx, key hx0 hxy⟩,
    algebraicIndependent_pair_iff.2 ⟨hy, by rw [mul_comm]; exact key hy0 hyx⟩,
    (isSeparable_of_mem (mul_mem hxl hyl)).isIntegral.isAlgebraic⟩, ?_, ?_,
    isSeparable_of_mem (mul_mem hxl hyl)⟩
  · refine isSeparable_of_mem ?_
    have hmem : x * y * y⁻¹ ∈ l⟮y, x * y⟯ := mul_mem
      (subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl))
      (inv_mem (subset_adjoin _ _ (Set.mem_insert _ _)))
    convert hmem using 1
    field_simp
  · refine isSeparable_of_mem ?_
    have hmem : x⁻¹ * (x * y) ∈ l⟮x, x * y⟯ := mul_mem
      (inv_mem (subset_adjoin _ _ (Set.mem_insert _ _)))
      (subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl))
    convert hmem using 1
    field_simp

/-- (S2) in a model: if `w` is separable over `l(u, v)` with `u, v ∈ L_B`, then `w ∈ L_B` and
`d w ∈ L_B d u + L_B d v`. -/
theorem modelD_mem_span_pair_of_isSeparable {ι : Type*} {B : ι → L} {u v w : L}
    (hw : IsSeparable l⟮u, v⟯ w) (hu : u ∈ model l B) (hv : v ∈ model l B) :
    w ∈ model l B ∧ modelD l B w ∈ Submodule.span (model l B) {modelD l B u, modelD l B v} := by
  have hle : l⟮u, v⟯ ≤ model l B := by
    rw [adjoin_le_iff]
    rintro _ (rfl | rfl)
    exacts [hu, hv]
  have hwM := mem_model_of_isSeparable hle hw
  refine ⟨hwM, ?_⟩
  have himage : Subtype.val '' ({⟨u, hu⟩, ⟨v, hv⟩} : Set (model l B)) = {u, v} := by
    rw [Set.image_insert_eq, Set.image_singleton]
  have hsep : IsSeparable (adjoin l ({⟨u, hu⟩, ⟨v, hv⟩} : Set (model l B)))
      (⟨w, hwM⟩ : model l B) := by
    rw [← isSeparable_adjoin_val_iff, himage]
    exact hw
  have := kaehler_D_mem_span_of_isSeparable_adjoin _ hsep
  rw [Set.image_insert_eq, Set.image_singleton] at this
  rwa [modelD_of_mem hwM, modelD_of_mem hu, modelD_of_mem hv]

end Collinear

section LevelTriples

variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]
variable {x y z : L}

/-- Being normalized is invariant under a diagonal Frobenius twist (blueprint proof of
Lemma 3.5(b)). -/
theorem IsNormalized.frobZ_iff (j : ℤ) :
    IsNormalized l (frobZ L p j x) (frobZ L p j y) (frobZ L p j z) ↔ IsNormalized l x y z := by
  have hsp : ∀ {a : L}, Transcendental l a → SamePoint l (frobZ L p j a) a := fun ha ↦
    (samePoint_frobZ_left_iff p j).2 (samePoint_refl ha)
  constructor
  · intro h
    have hx := (transcendental_frobZ_iff p j).1 h.transcendental₁
    have hy := (transcendental_frobZ_iff p j).1 h.transcendental₂
    have hz := (transcendental_frobZ_iff p j).1 h.transcendental₃
    exact ⟨h.toIsCollinearTriple.of_samePoint (hsp hx).symm (hsp hy).symm (hsp hz).symm,
      (isSeparable_adjoin_pair_frobZ_iff p j).1 h.isSeparable₁,
      (isSeparable_adjoin_pair_frobZ_iff p j).1 h.isSeparable₂,
      (isSeparable_adjoin_pair_frobZ_iff p j).1 h.isSeparable₃⟩
  · intro h
    exact ⟨h.toIsCollinearTriple.of_samePoint (hsp h.transcendental₁) (hsp h.transcendental₂)
        (hsp h.transcendental₃),
      (isSeparable_adjoin_pair_frobZ_iff p j).2 h.isSeparable₁,
      (isSeparable_adjoin_pair_frobZ_iff p j).2 h.isSeparable₂,
      (isSeparable_adjoin_pair_frobZ_iff p j).2 h.isSeparable₃⟩

omit [Fact p.Prime] [PerfectField L] [IsRelAlgClosed l L] in
theorem modelD_pow_pow {ι : Type*} {B : ι → L} {y : L} (hy : y ∈ model l B) {n : ℕ}
    (hn : 0 < n) : modelD l B (y ^ p ^ n) = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  rw [zero_add, pow_succ, pow_mul]
  exact modelD_pow_char p (pow_mem hy _)

/-- Existence of a model generator (the existence part of blueprint Lemma 4.3, for any
algebraically independent family): some `Frob^c y` lies in `L_B` and has non-zero differential. -/
theorem exists_frobZ_mem_model_modelD_ne_zero {ι : Type*} {B : ι → L}
    (hB : AlgebraicIndependent l B) {y : L} (hy : Transcendental l y)
    (halg : IsAlgebraic (adjoin l (Set.range B)) y) :
    ∃ c : ℤ, frobZ L p c y ∈ model l B ∧ modelD l B (frobZ L p c y) ≠ 0 := by
  have : PerfectField l := IsRelAlgClosed.perfectField l L
  obtain ⟨m, hm⟩ := exists_pow_pow_mem_model p halg
  have : CharP (model l B) p := (Algebra.charP_iff (model l B) L p).mpr inferInstance
  have hl := relAlgClosed_intermediateField (model l B) fun x hx ↦ IsRelAlgClosed.mem_range hx
  have hy' : (⟨y ^ p ^ m, hm⟩ : model l B) ∉ (algebraMap l (model l B)).range := by
    rintro ⟨c, hc⟩
    have hc' : algebraMap l L c = y ^ p ^ m := congrArg Subtype.val hc
    exact hy (IsAlgebraic.of_pow (pow_pos (Fact.out : p.Prime).pos m)
      (hc' ▸ isAlgebraic_algebraMap c))
  obtain ⟨k, z, hz, hDz⟩ := exists_pow_pow_eq_kaehler_D_ne_zero p
    (algebraicIndependent_restrictFamily _ (mem_separableClosure_adjoin B) hB)
    (isSeparable_adjoin_restrictFamily_separableClosure B) hl hy'
  have hz' : (z : L) ^ p ^ k = y ^ p ^ m := congrArg Subtype.val hz
  have hzy : (z : L) = frobZ L p ((m : ℤ) - k) y := by
    apply frobZ_injective p k
    rw [frobZ_natCast_apply, hz', ← frobZ_add_apply, show (k : ℤ) + ((m : ℤ) - k) = m by ring,
      frobZ_natCast_apply]
  refine ⟨m - k, hzy ▸ z.2, ?_⟩
  rw [← hzy, modelD_of_mem z.2]
  exact hDz

omit [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L] in
theorem modelD_eq_repr_pair {a b : L} (hB : AlgebraicIndependent l ![a, b])
    (v : model l ![a, b]) :
    D l (model l ![a, b]) v = (modelBasis hB).repr (D l _ v) 0 • modelD l ![a, b] a +
      (modelBasis hB).repr (D l _ v) 1 • modelD l ![a, b] b := by
  conv_lhs => rw [← (modelBasis hB).sum_repr (D l _ v)]
  rw [Fin.sum_univ_two, modelBasis_apply, modelBasis_apply]
  rfl

omit [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L] in
theorem linearIndependent_modelD_pair {a b : L} (hB : AlgebraicIndependent l ![a, b]) :
    LinearIndependent (model l ![a, b]) ![modelD l ![a, b] a, modelD l ![a, b] b] := by
  convert linearIndependent_modelD hB using 1
  ext i
  fin_cases i <;> rfl

/-- The key step of **blueprint Lemma 3.5(a)**: let `(a, b, w)` be three distinct collinear
points, with `a, b, w ∈ L_B`, `d a, d b` linearly independent and `0 ≠ d w ∈ L_B d a`. Then
`(a, Frob^c b, w)` is normalized for some `c`. (Proof: in the model `L'` of `![a, w]`, a model
generator `b₀ = Frob^c b` of `Q_b` has `d b₀ = γ d a + δ d w`; mapping to `Ω_B`, where
`d w ∈ L_B d a` and `d b ≠ 0`, forces `c > 0` and then `γ, δ ≠ 0`.) -/
theorem exists_isNormalized_of_modelD_mem_span {ι : Type*} {B : ι → L} {a b w : L}
    (hcol : IsCollinearTriple l a b w) (ha : a ∈ model l B) (hb : b ∈ model l B)
    (hw : w ∈ model l B)
    (hab : LinearIndependent (model l B) ![modelD l B a, modelD l B b])
    {α : model l B} (hwa : modelD l B w = α • modelD l B a) (hw0 : modelD l B w ≠ 0) :
    ∃ c : ℤ, IsNormalized l a (frobZ L p c b) w := by
  have : PerfectField l := IsRelAlgClosed.perfectField l L
  have hB' : AlgebraicIndependent l ![a, w] := hcol.indep₁₃
  have hbalg : IsAlgebraic (adjoin l (Set.range ![a, w])) b := by
    rw [Matrix.range_cons_cons_empty]
    exact hcol.swap₂₃.isAlgebraic
  obtain ⟨c, hcE', hc0⟩ :=
    exists_frobZ_mem_model_modelD_ne_zero p hB' hcol.transcendental₂ hbalg
  have haE' : a ∈ model l ![a, w] := self_mem_model ![a, w] 0
  have hwE' : w ∈ model l ![a, w] := self_mem_model ![a, w] 1
  have hE'E : model l ![a, w] ≤ model l B := fun v hv ↦ by
    refine mem_model_of_isSeparable ?_ (mem_model_iff.1 hv)
    rw [adjoin_le_iff, Matrix.range_cons_cons_empty]
    rintro _ (rfl | rfl)
    exacts [ha, hw]
  -- the coordinates of `d b₀` in `Ω_{L'}`, `b₀ = Frob^c b`
  obtain ⟨γ, δ, hrel⟩ : ∃ γ δ : model l ![a, w], modelD l ![a, w] (frobZ L p c b) =
      γ • modelD l ![a, w] a + δ • modelD l ![a, w] w := by
    refine ⟨(modelBasis hB').repr (D l _ ⟨_, hcE'⟩) 0, (modelBasis hB').repr (D l _ ⟨_, hcE'⟩) 1,
      ?_⟩
    rw [modelD_of_mem hcE']
    exact modelD_eq_repr_pair hB' ⟨_, hcE'⟩
  -- map the relation to `Ω_B`
  let : Algebra (model l ![a, w]) (model l B) :=
    (IntermediateField.inclusion hE'E).toRingHom.toAlgebra
  have : IsScalarTower l (model l ![a, w]) (model l B) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hmapD : ∀ v (hv : v ∈ model l ![a, w]),
      KaehlerDifferential.map l l (model l ![a, w]) (model l B) (modelD l ![a, w] v) =
        modelD l B v := fun v hv ↦ by
    rw [modelD_of_mem hv, KaehlerDifferential.map_D, modelD_of_mem (hE'E hv)]
    rfl
  set e := algebraMap (model l ![a, w]) (model l B)
  have hrelE : modelD l B (frobZ L p c b) = (e γ + e δ * α) • modelD l B a := by
    have := congrArg (KaehlerDifferential.map l l (model l ![a, w]) (model l B)) hrel
    rw [map_add, LinearMap.map_smul, LinearMap.map_smul, hmapD _ hcE', hmapD _ haE',
      hmapD _ hwE', hwa, ← algebraMap_smul (model l B) γ, ← algebraMap_smul (model l B) δ,
      smul_smul, ← add_smul] at this
    exact this
  have ha0 : modelD l B a ≠ 0 := by simpa using hab.ne_zero 0
  have hb0 : modelD l B b ≠ 0 := by simpa using hab.ne_zero 1
  -- `c > 0`
  have hc_pos : 0 < c := by
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · exfalso
      obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hc.le
      have hn0 : 0 < n := by omega
      have hbb : b = frobZ L p c b ^ p ^ n := by
        rw [← frobZ_natCast_apply, ← frobZ_add_apply, hn]
        simp [frobZ_zero_apply]
      apply hb0
      rw [hbb]
      exact modelD_pow_pow p (hE'E hcE') hn0
    · exfalso
      rw [frobZ_zero_apply] at hrelE
      exact (LinearIndependent.pair_iff' ha0).1 hab _ hrelE.symm
    · exact hc
  -- `γ + δ α = 0`
  have hsum : e γ + e δ * α = 0 := by
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hc_pos.le
    have h0 : modelD l B (frobZ L p c b) = 0 := by
      rw [hn, frobZ_natCast_apply]
      exact modelD_pow_pow p hb (by omega)
    rw [h0] at hrelE
    exact (smul_eq_zero.1 hrelE.symm).resolve_right ha0
  have hα : α ≠ 0 := by
    rintro rfl
    exact hw0 (by rw [hwa, zero_smul])
  have hinj : Function.Injective e := e.injective
  have hδ : δ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul, add_zero] at hsum
    have hγ : γ = 0 := hinj (by rw [hsum, map_zero])
    apply hc0
    rw [hrel, hγ, zero_smul, zero_smul, add_zero]
  have hγ : γ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_add] at hsum
    exact hδ (hinj (by rw [(mul_eq_zero.1 hsum).resolve_right hα, map_zero]))
  -- pairwise linear independence in `Ω_{L'}`
  have haw := linearIndependent_modelD_pair hB'
  have hab₀ : LinearIndependent (model l ![a, w])
      ![modelD l ![a, w] a, modelD l ![a, w] (frobZ L p c b)] := by
    rw [hrel]
    exact linearIndependent_pair_smul_add_left haw γ hδ
  have hwb₀ : LinearIndependent (model l ![a, w])
      ![modelD l ![a, w] w, modelD l ![a, w] (frobZ L p c b)] := by
    rw [hrel]
    exact linearIndependent_pair_smul_add_right haw hγ δ
  have hb₀alg : IsAlgebraic l⟮a, w⟯ (frobZ L p c b) :=
    (mem_model_pair_iff.1 hcE').isIntegral.isAlgebraic
  exact ⟨c, (isNormalized_of_linearIndependent_modelD haE' hwE' hcE' haw hab₀ hwb₀
    hb₀alg).swap₂₃⟩

/-- **Blueprint Lemma 3.5(a)**: normalized triples exist. More precisely, for three distinct
collinear points with elements `x, y, z`, there are `j, k ∈ ℤ` such that `(x, Frob^j y, Frob^k z)`
is normalized (the first entry can be prescribed, by Lemma 3.5(b)). -/
theorem exists_isNormalized (h : IsCollinearTriple l x y z) :
    ∃ j k : ℤ, IsNormalized l x (frobZ L p j y) (frobZ L p k z) := by
  have : PerfectField l := IsRelAlgClosed.perfectField l L
  have hB : AlgebraicIndependent l ![x, y] := h.indep₁₂
  have hzalg : IsAlgebraic (adjoin l (Set.range ![x, y])) z := by
    rw [Matrix.range_cons_cons_empty]
    exact h.isAlgebraic
  obtain ⟨k, hkE, hk0⟩ := exists_frobZ_mem_model_modelD_ne_zero p hB h.transcendental₃ hzalg
  have hxE : x ∈ model l ![x, y] := self_mem_model ![x, y] 0
  have hyE : y ∈ model l ![x, y] := self_mem_model ![x, y] 1
  have hcol : IsCollinearTriple l x y (frobZ L p k z) :=
    h.of_samePoint (samePoint_refl h.transcendental₁) (samePoint_refl h.transcendental₂)
      ((samePoint_frobZ_left_iff p k).2 (samePoint_refl h.transcendental₃))
  have hxy := linearIndependent_modelD_pair hB
  obtain ⟨α, β, hrel⟩ : ∃ α β : model l ![x, y], modelD l ![x, y] (frobZ L p k z) =
      α • modelD l ![x, y] x + β • modelD l ![x, y] y := by
    refine ⟨(modelBasis hB).repr (D l _ ⟨_, hkE⟩) 0, (modelBasis hB).repr (D l _ ⟨_, hkE⟩) 1, ?_⟩
    rw [modelD_of_mem hkE]
    exact modelD_eq_repr_pair hB ⟨_, hkE⟩
  by_cases hβ : β = 0
  · -- `d z₀ ∈ L_B d x`: twist `y`
    rw [hβ, zero_smul, add_zero] at hrel
    obtain ⟨c, hc⟩ := exists_isNormalized_of_modelD_mem_span p hcol hxE hyE hkE hxy hrel hk0
    exact ⟨c, k, hc⟩
  by_cases hα : α = 0
  · -- `d z₀ ∈ L_B d y`: twist `x`, then shift diagonally
    rw [hα, zero_smul, zero_add] at hrel
    obtain ⟨c, hc⟩ := exists_isNormalized_of_modelD_mem_span p hcol.swap₁₂ hyE hxE hkE
      (LinearIndependent.pair_symm_iff.1 hxy) hrel hk0
    refine ⟨-c, -c + k, ?_⟩
    have := (IsNormalized.frobZ_iff p (-c)).2 hc.swap₁₂
    rwa [frobZ_neg_apply_frobZ, ← frobZ_add_apply] at this
  · -- generic case: `(x, y, z₀)` is normalized
    refine ⟨0, k, ?_⟩
    rw [frobZ_zero_apply]
    refine isNormalized_of_linearIndependent_modelD hxE hyE hkE hxy ?_ ?_ hcol.isAlgebraic
    · rw [hrel]
      exact linearIndependent_pair_smul_add_left hxy α hβ
    · rw [hrel]
      exact linearIndependent_pair_smul_add_right hxy hα β

omit [Fact p.Prime] [PerfectField L] [IsRelAlgClosed l L] in
/-- The core of the "only if" part of **blueprint Lemma 3.5(b)**: if `(x, y, z)` and
`(x ^ p ^ a, y ^ p ^ b, z ^ p ^ c)` are normalized and `min(a, b, c) = 0`, then `a = b = c = 0`. -/
theorem eq_zero_of_isNormalized_pow_pow (h : IsNormalized l x y z) {a b c : ℕ}
    (h' : IsNormalized l (x ^ p ^ a) (y ^ p ^ b) (z ^ p ^ c)) (hmin : a = 0 ∨ b = 0 ∨ c = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hB : AlgebraicIndependent l ![x, y] := h.indep₁₂
  have hxE : x ∈ model l ![x, y] := self_mem_model ![x, y] 0
  have hyE : y ∈ model l ![x, y] := self_mem_model ![x, y] 1
  have hzE : z ∈ model l ![x, y] := mem_model_pair_iff.2 h.isSeparable₃
  have hxy := linearIndependent_modelD_pair hB
  have hx_span := (modelD_mem_span_pair_of_isSeparable h.isSeparable₁ hyE hzE).2
  have hy_span := (modelD_mem_span_pair_of_isSeparable h.isSeparable₂ hxE hzE).2
  have hxz := linearIndependent_pair_of_mem_span_pair hxy hy_span
  have hyz := linearIndependent_pair_of_mem_span_pair (LinearIndependent.pair_symm_iff.1 hxy)
    hx_span
  have hu := (modelD_mem_span_pair_of_isSeparable h'.isSeparable₁ (pow_mem hyE _)
    (pow_mem hzE _)).2
  have hv := (modelD_mem_span_pair_of_isSeparable h'.isSeparable₂ (pow_mem hxE _)
    (pow_mem hzE _)).2
  have hw := (modelD_mem_span_pair_of_isSeparable h'.isSeparable₃ (pow_mem hxE _)
    (pow_mem hyE _)).2
  have hpow : ∀ {t : L}, t ∈ model l ![x, y] → ∀ n : ℕ,
      (n = 0 ∧ modelD l ![x, y] (t ^ p ^ n) = modelD l ![x, y] t) ∨
      (0 < n ∧ modelD l ![x, y] (t ^ p ^ n) = 0) := by
    intro t ht n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact Or.inl ⟨rfl, by rw [pow_zero, pow_one]⟩
    · exact Or.inr ⟨hn, modelD_pow_pow p ht hn⟩
  have span00 : Submodule.span (model l ![x, y]) {(0 : Ω[model l ![x, y]⁄l]), 0} = ⊥ := by
    rw [Submodule.span_insert_zero, Submodule.span_zero_singleton]
  have span0r : ∀ v : Ω[model l ![x, y]⁄l],
      Submodule.span (model l ![x, y]) {0, v} = (model l ![x, y]) ∙ v := fun v ↦
    Submodule.span_insert_zero
  have spanr0 : ∀ v : Ω[model l ![x, y]⁄l],
      Submodule.span (model l ![x, y]) {v, 0} = (model l ![x, y]) ∙ v := fun v ↦ by
    rw [Set.pair_comm, Submodule.span_insert_zero]
  rcases hpow hxE a with ⟨ha, hda⟩ | ⟨ha, hda⟩ <;>
  rcases hpow hyE b with ⟨hb, hdb⟩ | ⟨hb, hdb⟩ <;>
  rcases hpow hzE c with ⟨hc, hdc⟩ | ⟨hc, hdc⟩
  · exact ⟨ha, hb, hc⟩
  · -- `a = b = 0 < c`
    rw [hda, hdb, hdc, spanr0] at hu
    exact absurd hu (notMem_span_singleton_of_linearIndependent_pair
      (LinearIndependent.pair_symm_iff.1 hxy))
  · -- `a = c = 0 < b`
    rw [hda, hdb, hdc, span0r] at hu
    exact absurd hu (notMem_span_singleton_of_linearIndependent_pair
      (LinearIndependent.pair_symm_iff.1 hxz))
  · -- `a = 0 < b, c`
    rw [hda, hdb, hdc, span00, Submodule.mem_bot] at hu
    exact absurd hu (by simpa using hxy.ne_zero 0)
  · -- `b = c = 0 < a`
    rw [hda, hdb, hdc, span0r] at hv
    exact absurd hv (notMem_span_singleton_of_linearIndependent_pair
      (LinearIndependent.pair_symm_iff.1 hyz))
  · -- `b = 0 < a, c`
    rw [hda, hdb, hdc, span00, Submodule.mem_bot] at hv
    exact absurd hv (by simpa using hxy.ne_zero 1)
  · -- `c = 0 < a, b`
    rw [hda, hdb, hdc, span00, Submodule.mem_bot] at hw
    exact absurd hw (by simpa using hxz.ne_zero 1)
  · omega

/-- **Blueprint Lemma 3.5(b)**: if `(x, y, z)` is normalized and `x', y', z'` lie in the points of
`x, y, z`, then `(x', y', z')` is normalized iff there is `j` with `lev x' = lev x + j`,
`lev y' = lev y + j` and `lev z' = lev z + j`. -/
theorem IsNormalized.isNormalized_iff (h : IsNormalized l x y z) {x' y' z' : L}
    (hx : SamePoint l x' x) (hy : SamePoint l y' y) (hz : SamePoint l z' z) :
    IsNormalized l x' y' z' ↔
      levDiff l p x' x = levDiff l p y' y ∧ levDiff l p y' y = levDiff l p z' z := by
  constructor
  · intro h'
    have : PerfectField l := IsRelAlgClosed.perfectField l L
    set a := levDiff l p x' x
    set b := levDiff l p y' y
    set c := levDiff l p z' z
    have h1 : IsNormalized l (frobZ L p a x) (frobZ L p b y) (frobZ L p c z) :=
      h'.of_sepEquiv (levDiff_spec p hx).symm (levDiff_spec p hy).symm (levDiff_spec p hz).symm
    set m := min a (min b c)
    have h2 := (IsNormalized.frobZ_iff p (-m)).2 h1
    rw [← frobZ_add_apply, ← frobZ_add_apply, ← frobZ_add_apply] at h2
    obtain ⟨a', ha'⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -m + a)
    obtain ⟨b', hb'⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -m + b)
    obtain ⟨c', hc'⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -m + c)
    rw [ha', hb', hc', frobZ_natCast_apply, frobZ_natCast_apply, frobZ_natCast_apply] at h2
    have hmin : a' = 0 ∨ b' = 0 ∨ c' = 0 := by omega
    obtain ⟨ha0, hb0, hc0⟩ := eq_zero_of_isNormalized_pow_pow p h h2 hmin
    omega
  · rintro ⟨hab, hbc⟩
    have h1 := (IsNormalized.frobZ_iff p (levDiff l p x' x)).2 h
    refine h1.of_sepEquiv (levDiff_spec p hx) ?_ ?_
    · rw [hab]
      exact levDiff_spec p hy
    · rw [hab, hbc]
      exact levDiff_spec p hz

open Classical in
variable (l) in
/-- **Blueprint Lemma 3.5 and the definition after it** (level triple `lt(P, Q, R)`), relative
to elements `x, y, z` of the points: the unique `(j, k) ∈ ℤ × ℤ` such that `(x, Frob^j y, Frob^k z)`
is normalized (`isNormalized_levelTriple`). Thus `(lev x, lev y + j, lev z + k)` is the level
triple of `(Q_x, Q_y, Q_z)`, and for any normalized triple `(x', y', z')` in these points,
`(j, k) = (lev y' - lev y - (lev x' - lev x), lev z' - lev z - (lev x' - lev x))`
(`levelTriple_eq_of_isNormalized`). It is `0` if no such pair exists, i.e. if
`¬ IsCollinearTriple l x y z`. -/
noncomputable def levelTriple (x y z : L) : ℤ × ℤ :=
  if h : ∃ jk : ℤ × ℤ, IsNormalized l x (frobZ L p jk.1 y) (frobZ L p jk.2 z) then h.choose else 0

/-- **Blueprint Lemma 3.5**: `(x, Frob^j y, Frob^k z)` is normalized for
`(j, k) = levelTriple l p x y z`. -/
theorem isNormalized_levelTriple (h : IsCollinearTriple l x y z) :
    IsNormalized l x (frobZ L p (levelTriple l p x y z).1 y)
      (frobZ L p (levelTriple l p x y z).2 z) := by
  obtain ⟨j, k, hjk⟩ := exists_isNormalized p h
  have hex : ∃ jk : ℤ × ℤ, IsNormalized l x (frobZ L p jk.1 y) (frobZ L p jk.2 z) :=
    ⟨(j, k), hjk⟩
  rw [levelTriple, dite_eq_left hex]
  exact hex.choose_spec

/-- **Blueprint Lemma 3.5(b)**: the level triple can be computed from any normalized triple
`(x', y', z')` in the points of `x, y, z`. -/
theorem levelTriple_eq_of_isNormalized {x' y' z' : L} (h : IsNormalized l x' y' z')
    (hx : SamePoint l x' x) (hy : SamePoint l y' y) (hz : SamePoint l z' z) :
    levelTriple l p x y z =
      (levDiff l p y' y - levDiff l p x' x, levDiff l p z' z - levDiff l p x' x) := by
  have hcol : IsCollinearTriple l x y z :=
    h.toIsCollinearTriple.of_samePoint hx.symm hy.symm hz.symm
  have hN := isNormalized_levelTriple p hcol
  set j := (levelTriple l p x y z).1
  set k := (levelTriple l p x y z).2
  have hy' : SamePoint l (frobZ L p j y) y' := (samePoint_frobZ_left_iff p j).2 hy.symm
  have hz' : SamePoint l (frobZ L p k z) z' := (samePoint_frobZ_left_iff p k).2 hz.symm
  obtain ⟨h1, h2⟩ := (h.isNormalized_iff p hx.symm hy' hz').1 hN
  rw [levDiff_frobZ_left p hy.symm, levDiff_swap p hy, levDiff_swap p hx] at h1
  rw [levDiff_frobZ_left p hy.symm, levDiff_frobZ_left p hz.symm, levDiff_swap p hy,
    levDiff_swap p hz] at h2
  ext
  · change j = _
    omega
  · change k = _
    omega

/-- Swapping the first two points of a collinear triple negates the first entry of the level
triple relative to the given elements: if `(a, Frob^j b, *)` is normalized, then so is
`(b, Frob^{-j} a, *)`. (This is "`c(w, u) = -c(u, w)`", blueprint line 434.) -/
theorem levelTriple_swap_fst {a b d : L} (h : IsCollinearTriple l a b d) :
    (levelTriple l p b a d).1 = -(levelTriple l p a b d).1 := by
  set j := (levelTriple l p a b d).1
  set k := (levelTriple l p a b d).2
  have hn : IsNormalized l (frobZ L p j b) a (frobZ L p k d) :=
    (isNormalized_levelTriple p h).swap₁₂
  have hn' : IsNormalized l b (frobZ L p (-j) a) (frobZ L p (-j + k) d) := by
    have := (IsNormalized.frobZ_iff p (-j)).2 hn
    rwa [frobZ_neg_apply_frobZ, ← frobZ_add_apply] at this
  have ha : SamePoint l (frobZ L p (-j) a) a :=
    (samePoint_frobZ_left_iff p (-j)).2 (samePoint_refl h.transcendental₁)
  have hd : SamePoint l (frobZ L p (-j + k) d) d :=
    (samePoint_frobZ_left_iff p (-j + k)).2 (samePoint_refl h.transcendental₃)
  rw [levelTriple_eq_of_isNormalized p hn' (samePoint_refl h.transcendental₂) ha hd,
    levDiff_frobZ_left p (samePoint_refl h.transcendental₁), levDiff_self p h.transcendental₁,
    levDiff_self p h.transcendental₂]
  ring

end LevelTriples

end MilnorAlgDep
