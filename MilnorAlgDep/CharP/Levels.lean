module

public import MilnorAlgDep.CharP.Model

/-!
# Levels

Blueprint, Section 3.1 (Lemma 3.2 and the definition of levels), element-wise.

The blueprint attaches to a point `P` the `Γ`-torsor `Λ(P) = (P \ l)/≈` of *levels*, where
`s ≈ t` iff `s` is separable algebraic over `l(t)` and `t` over `l(s)`. We avoid the quotient: we
only use the relation `≈` (`MilnorAlgDep.SepEquiv`) and the *level difference*
`levDiff l p s t = lev(s) - lev(t) ∈ ℤ` of two transcendental elements of the same point
(`MilnorAlgDep.SamePoint`), characterized by `s ≈ Frob^(levDiff l p s t) t` (Lemma 3.2,
`levDiff_eq_iff`). For instance `lev(s) ≥ lev(t)` is `0 ≤ levDiff l p s t`.

## Main definitions

* `MilnorAlgDep.SamePoint l s t`: `s, t` are transcendental over `l` and `Q_s = Q_t`.
* `MilnorAlgDep.SepEquiv l s t`: the relation `s ≈ t` of Section 3.1.
* `MilnorAlgDep.levDiff l p s t : ℤ`: the level difference `lev(s) - lev(t)`. It is meaningful
  when `SamePoint l s t`; otherwise it is `0` (`levDiff_of_not_samePoint`).

## Main statements

* `existsUnique_sepEquiv_frobZ` (Lemma 3.2): for `s, t` in the same point there is a unique
  `j : ℤ` with `s ≈ Frob^j t`. Together with `SepEquiv.refl`, `SepEquiv.symm`, `SepEquiv.trans`
  this is Lemma 3.2.
* The calculus of `levDiff`: `levDiff_eq_iff`, `levDiff_eq_zero_iff`, `levDiff_self`,
  `levDiff_swap`, `levDiff_add_levDiff` (cocycle rule), `levDiff_frobZ_left`,
  `levDiff_frobZ_right`, `SepEquiv.levDiff_left`, `SepEquiv.levDiff_right`, and the invariance of
  levels under `s ↦ c s` (`c ∈ lˣ`), `s ↦ s ^ N` (`N` prime to `p`) and `s ↦ s⁻¹` used to define
  `lev(v)` for `v ∈ V` (blueprint lines 406-407).
* `levDiff_nonneg_iff`: `lev(s) ≥ lev(t)` iff `s` is separable over `l(t)` (the "if" direction is
  the remark of blueprint line 460).
* `SepEquiv.span_modelD_eq`: `s ≈ t` implies `L_B d s = L_B d t` in `Ω_B`.
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential IntermediateField

variable {l L : Type*} [Field l] [Field L] [Algebra l L]

section SamePoint

variable (l) in
/-- `s` and `t` are transcendental over `l` and lie in the same point, `Q_s = Q_t` (blueprint
Section 2.1). Equivalently (`samePoint_iff_not_algebraicIndependent`): both are transcendental and
they are algebraically dependent over `l`. -/
def SamePoint (s t : L) : Prop :=
  Transcendental l s ∧ Transcendental l t ∧ point l s = point l t

theorem SamePoint.transcendental_left {s t : L} (h : SamePoint l s t) : Transcendental l s :=
  h.1

theorem SamePoint.transcendental_right {s t : L} (h : SamePoint l s t) : Transcendental l t :=
  h.2.1

theorem SamePoint.point_eq {s t : L} (h : SamePoint l s t) : point l s = point l t :=
  h.2.2

theorem samePoint_refl {s : L} (hs : Transcendental l s) : SamePoint l s s :=
  ⟨hs, hs, rfl⟩

theorem SamePoint.symm {s t : L} (h : SamePoint l s t) : SamePoint l t s :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem SamePoint.trans {s t u : L} (hst : SamePoint l s t) (htu : SamePoint l t u) :
    SamePoint l s u :=
  ⟨hst.1, htu.2.1, hst.2.2.trans htu.2.2⟩

theorem samePoint_iff_not_algebraicIndependent {s t : L} :
    SamePoint l s t ↔
      Transcendental l s ∧ Transcendental l t ∧ ¬ AlgebraicIndependent l ![s, t] := by
  refine ⟨fun h ↦ ⟨h.1, h.2.1, ?_⟩, fun ⟨hs, ht, h⟩ ↦ ⟨hs, ht, ?_⟩⟩
  · exact (point_eq_point_iff_not_algebraicIndependent h.1 h.2.1).1 h.2.2
  · exact (point_eq_point_iff_not_algebraicIndependent hs ht).2 h

theorem SamePoint.mem_point {s t : L} (h : SamePoint l s t) : s ∈ point l t := by
  rw [← h.point_eq]
  exact self_mem_point s

theorem SamePoint.isAlgebraic {s t : L} (h : SamePoint l s t) : IsAlgebraic l⟮t⟯ s :=
  mem_point_iff.1 h.mem_point

end SamePoint

section SepEquiv

variable (l) in
/-- Blueprint Section 3.1: `s ≈ t` iff `s` is separable algebraic over `l(t)` and `t` is separable
algebraic over `l(s)`. (Defined for all `s, t : L`; the blueprint uses it on `P \ l` for a point
`P`.) -/
def SepEquiv (s t : L) : Prop :=
  IsSeparable l⟮t⟯ s ∧ IsSeparable l⟮s⟯ t

/-- Blueprint Lemma 3.2: `≈` is reflexive. -/
theorem SepEquiv.refl (s : L) : SepEquiv l s s :=
  ⟨isSeparable_algebraMap (⟨s, mem_adjoin_simple_self l s⟩ : l⟮s⟯),
    isSeparable_algebraMap (⟨s, mem_adjoin_simple_self l s⟩ : l⟮s⟯)⟩

/-- Blueprint Lemma 3.2: `≈` is symmetric. -/
theorem SepEquiv.symm {s t : L} (h : SepEquiv l s t) : SepEquiv l t s :=
  ⟨h.2, h.1⟩

/-- An element of an intermediate field `K` is separable over `K`. -/
theorem isSeparable_of_mem {K : IntermediateField l L} {x : L} (hx : x ∈ K) : IsSeparable K x :=
  isSeparable_algebraMap (⟨x, hx⟩ : K)

/-- Separability over an intermediate field passes to larger intermediate fields. -/
theorem IsSeparable.of_le {K K' : IntermediateField l L} (hKK' : K ≤ K') {x : L}
    (hx : IsSeparable K x) : IsSeparable K' x := by
  let : Algebra K K' := (IntermediateField.inclusion hKK').toRingHom.toAlgebra
  have : IsScalarTower K K' L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact hx.tower_top K'

theorem mem_model_singleton_iff {t y : L} : y ∈ model l ![t] ↔ IsSeparable l⟮t⟯ y := by
  rw [mem_model_iff, Matrix.range_cons_empty]

theorem self_mem_model_singleton (t : L) : t ∈ model l ![t] :=
  self_mem_model ![t] 0

/-- If `u` is separable over `l(s)` and `s` is separable over `l(t)`, then `u` is separable over
`l(t)`. -/
theorem isSeparable_adjoin_simple_trans {s t u : L} (hus : IsSeparable l⟮s⟯ u)
    (hst : IsSeparable l⟮t⟯ s) : IsSeparable l⟮t⟯ u := by
  rw [← mem_model_singleton_iff] at hst ⊢
  exact mem_model_of_isSeparable (adjoin_simple_le_iff.2 hst) hus

/-- Blueprint Lemma 3.2: `≈` is transitive. -/
theorem SepEquiv.trans {s t u : L} (hst : SepEquiv l s t) (htu : SepEquiv l t u) :
    SepEquiv l s u :=
  ⟨isSeparable_adjoin_simple_trans hst.1 htu.1, isSeparable_adjoin_simple_trans htu.2 hst.2⟩

/-- If `s ≈ t` and `s` is transcendental over `l`, then `s` and `t` lie in the same point. -/
theorem SepEquiv.samePoint {s t : L} (h : SepEquiv l s t) (hs : Transcendental l s) :
    SamePoint l s t := by
  have hst : IsAlgebraic l⟮t⟯ s := h.1.isIntegral.isAlgebraic
  have hts : IsAlgebraic l⟮s⟯ t := h.2.isIntegral.isAlgebraic
  have ht : Transcendental l t := by
    intro ht
    have : Algebra.IsAlgebraic l l⟮t⟯ := IntermediateField.isAlgebraic_adjoin_simple ht.isIntegral
    exact hs (hst.restrictScalars l)
  exact ⟨hs, ht, point_eq_point_of_isAlgebraic hts hst⟩

/-- `c s ≈ s` for `c ∈ lˣ` (used for the well-definedness of `lev(v)`, `v ∈ V`, blueprint
line 406). -/
theorem sepEquiv_algebraMap_mul {c : l} (hc : c ≠ 0) (s : L) :
    SepEquiv l (algebraMap l L c * s) s := by
  refine ⟨isSeparable_of_mem
    (mul_mem (IntermediateField.algebraMap_mem _ c) (mem_adjoin_simple_self l s)),
    isSeparable_of_mem ?_⟩
  have hc' : algebraMap l L c ≠ 0 := (map_ne_zero _).2 hc
  have hmem : (algebraMap l L c)⁻¹ * (algebraMap l L c * s) ∈ l⟮algebraMap l L c * s⟯ :=
    mul_mem (inv_mem (IntermediateField.algebraMap_mem _ c)) (mem_adjoin_simple_self l _)
  convert hmem using 1
  field_simp

/-- `s⁻¹ ≈ s` (used for `lev(-v) = lev(v)`, blueprint line 407). -/
theorem sepEquiv_inv (s : L) : SepEquiv l s⁻¹ s := by
  refine ⟨isSeparable_of_mem (inv_mem (mem_adjoin_simple_self l s)), isSeparable_of_mem ?_⟩
  rw [← inv_inv s, inv_inv s⁻¹]
  exact inv_mem (mem_adjoin_simple_self l _)

/-- `s ^ N ≈ s` if `N` is prime to the characteristic, i.e. `(N : L) ≠ 0` (used for the
well-definedness of `lev(v)`, `v ∈ V`, blueprint line 406). -/
theorem sepEquiv_pow {N : ℕ} (hN : (N : L) ≠ 0) (s : L) : SepEquiv l (s ^ N) s := by
  refine ⟨isSeparable_of_mem (pow_mem (mem_adjoin_simple_self l s) N), ?_⟩
  rcases eq_or_ne s 0 with rfl | hs
  · exact isSeparable_of_mem (zero_mem _)
  set K := l⟮s ^ N⟯
  set a : K := ⟨s ^ N, mem_adjoin_simple_self l _⟩
  have ha : a ≠ 0 := fun h ↦ pow_ne_zero N hs (congrArg Subtype.val h)
  have hNK : (N : K) ≠ 0 := by
    intro h
    apply hN
    have := congrArg (algebraMap K L) h
    rwa [map_natCast, map_zero] at this
  have hsep := Polynomial.separable_X_pow_sub_C a hNK ha
  refine hsep.of_dvd (minpoly.dvd K s ?_)
  simp [a]

/-- The field `L_t` of elements separable algebraic over `l(t)` is contained in the point `Q_t`. -/
theorem model_le_point (t : L) : model l ![t] ≤ point l t := fun _ hy ↦
  mem_point_iff.2 (mem_model_singleton_iff.1 hy).isIntegral.isAlgebraic

/-- If `s` is separable algebraic over `l(t)` and `t ∈ L_B`, then `s ∈ L_B` and `d s = c • d t` in
`Ω_B` for some `c` which is separable algebraic over `l(t)`, hence lies in the point `Q_t`
(`model_le_point`). This is the fact "`db = b_a da` with `b_a` in the field of elements separable
over `l(a)`, which is contained in `Q_x`" of blueprint lines 535, 676-677 and 700. -/
theorem exists_modelD_eq_smul_of_isSeparable {ι : Type*} {B : ι → L} {s t : L}
    (hs : IsSeparable l⟮t⟯ s) (ht : t ∈ model l B) :
    ∃ (c : L) (hc : c ∈ model l B), c ∈ model l ![t] ∧
      modelD l B s = (⟨c, hc⟩ : model l B) • modelD l B t := by
  set E := model l ![t]
  set M := model l B
  have htE : t ∈ E := self_mem_model_singleton t
  have hsE : s ∈ E := mem_model_singleton_iff.2 hs
  have hEM : E ≤ M := fun y hy ↦
    mem_model_of_isSeparable (adjoin_simple_le_iff.2 ht) (mem_model_singleton_iff.1 hy)
  have hsep' : IsSeparable (adjoin l {(⟨t, htE⟩ : E)}) (⟨s, hsE⟩ : E) := by
    rw [← isSeparable_adjoin_val_iff, Set.image_singleton]
    exact hs
  have hmem := kaehler_D_mem_span_of_isSeparable_adjoin _ hsep'
  rw [Set.image_singleton, Submodule.mem_span_singleton] at hmem
  obtain ⟨a, ha⟩ := hmem
  refine ⟨a, hEM a.2, a.2, ?_⟩
  let : Algebra E M := (IntermediateField.inclusion hEM).toRingHom.toAlgebra
  have : IsScalarTower l E M := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hmap := congrArg (KaehlerDifferential.map l l E M) ha
  rw [LinearMap.map_smul, KaehlerDifferential.map_D, KaehlerDifferential.map_D] at hmap
  have e1 : algebraMap E M ⟨s, hsE⟩ = ⟨s, hEM hsE⟩ := rfl
  have e2 : algebraMap E M ⟨t, htE⟩ = ⟨t, ht⟩ := rfl
  rw [e1, e2] at hmap
  rw [modelD_of_mem (hEM hsE), modelD_of_mem ht, ← hmap, ← algebraMap_smul M a]
  rfl

/-- If `s ≈ t` and `s ∈ L_B`, then `t ∈ L_B`. -/
theorem SepEquiv.mem_model {ι : Type*} {B : ι → L} {s t : L} (h : SepEquiv l s t)
    (hs : s ∈ model l B) : t ∈ model l B :=
  mem_model_of_isSeparable (adjoin_simple_le_iff.2 hs) h.2

/-- If `s ≈ t` and `s ∈ L_B`, then `t ∈ L_B` and `d s`, `d t` span the same line of `Ω_B` (by
Lemma 2.1 (S2), each differential is a multiple of the other). In particular `d s ≠ 0` iff
`d t ≠ 0` (used in the proofs of Lemmas 4.3 and 6.2). -/
theorem SepEquiv.span_modelD_eq {ι : Type*} {B : ι → L} {s t : L} (h : SepEquiv l s t)
    (hs : s ∈ model l B) :
    (model l B) ∙ modelD l B s = (model l B) ∙ modelD l B t := by
  obtain ⟨c, hc, -, hst⟩ := exists_modelD_eq_smul_of_isSeparable h.1 (h.mem_model hs)
  obtain ⟨c', hc', -, hts⟩ := exists_modelD_eq_smul_of_isSeparable h.2 hs
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_singleton_le_iff_mem, hst]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem, hts]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- `b ^ A ≈ b` for `A` prime to the characteristic. -/
theorem sepEquiv_zpow {A : ℤ} (hA : (A : L) ≠ 0) (b : L) : SepEquiv l (b ^ A) b := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg A
  · rw [zpow_natCast]
    exact sepEquiv_pow (by exact_mod_cast hA) b
  · rw [zpow_neg, zpow_natCast]
    have hn : (n : L) ≠ 0 := fun h ↦ hA (by push_cast; rw [h, neg_zero])
    exact (sepEquiv_inv (b ^ n)).trans (sepEquiv_pow hn b)

end SepEquiv

section Levels

variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]

section Transport

omit [IsRelAlgClosed l L] in
/-- `Frob^j x` is algebraic over `l(x)`. -/
theorem isAlgebraic_adjoin_frobZ (j : ℤ) (x : L) : IsAlgebraic l⟮x⟯ (frobZ L p j x) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · rw [frobZ_natCast_apply]
    exact (isSeparable_of_mem (pow_mem (mem_adjoin_simple_self l x) _)).isIntegral.isAlgebraic
  · refine IsAlgebraic.of_pow (pow_pos (Fact.out : p.Prime).pos n) ?_
    rw [frobZ_neg_natCast_pow]
    exact (isSeparable_of_mem (mem_adjoin_simple_self l x)).isIntegral.isAlgebraic

theorem frobZ_mem_range_iff (j : ℤ) {x : L} :
    frobZ L p j x ∈ (algebraMap l L).range ↔ x ∈ (algebraMap l L).range := by
  constructor
  · rintro ⟨c, hc⟩
    have := frobZ_algebraMap_mem_range (L := L) p (-j) c
    rwa [hc, frobZ_neg_apply_frobZ] at this
  · rintro ⟨c, rfl⟩
    exact frobZ_algebraMap_mem_range (L := L) p j c

/-- `Frob^j` maps `l(S)` into `l(Frob^j S)`. -/
theorem frobZ_mem_adjoin (j : ℤ) {S : Set L} {x : L} (hx : x ∈ adjoin l S) :
    frobZ L p j x ∈ adjoin l (frobZ L p j '' S) := by
  have hle : Subfield.closure (Set.range (algebraMap l L) ∪ S) ≤
      (adjoin l (frobZ L p j '' S)).toSubfield.comap (frobZ L p j : L →+* L) := by
    rw [Subfield.closure_le]
    rintro y (⟨c, rfl⟩ | hy)
    · obtain ⟨c', hc'⟩ := frobZ_algebraMap_mem_range (L := L) p j c
      change frobZ L p j (algebraMap l L c) ∈ adjoin l _
      rw [← hc']
      exact IntermediateField.algebraMap_mem _ c'
    · exact subset_adjoin _ _ ⟨y, hy, rfl⟩
  exact hle hx

theorem frobZ_neg_image_frobZ_image (j : ℤ) (S : Set L) :
    frobZ L p (-j) '' (frobZ L p j '' S) = S := by
  rw [Set.image_image]
  simp

variable (l) in
/-- The ring isomorphism `l(S) ≃ l(Frob^j S)` induced by `Frob^j`. -/
noncomputable def adjoinFrobZEquiv (j : ℤ) (S : Set L) :
    adjoin l S ≃+* adjoin l (frobZ L p j '' S) where
  toFun k := ⟨frobZ L p j k, frobZ_mem_adjoin p j k.2⟩
  invFun k := ⟨frobZ L p (-j) k, by
    have := frobZ_mem_adjoin p (-j) k.2
    rwa [frobZ_neg_image_frobZ_image] at this⟩
  left_inv k := Subtype.ext (frobZ_neg_apply_frobZ p j (k : L))
  right_inv k := Subtype.ext (frobZ_apply_frobZ_neg p j (k : L))
  map_mul' a b := Subtype.ext (map_mul (frobZ L p j) (a : L) b)
  map_add' a b := Subtype.ext (map_add (frobZ L p j) (a : L) b)

/-- Separability is invariant under `Frob^j`. -/
theorem isSeparable_adjoin_frobZ_iff (j : ℤ) {S : Set L} {x : L} :
    IsSeparable (adjoin l (frobZ L p j '' S)) (frobZ L p j x) ↔ IsSeparable (adjoin l S) x := by
  have key : ∀ (j : ℤ) (S : Set L) (x : L), IsSeparable (adjoin l S) x →
      IsSeparable (adjoin l (frobZ L p j '' S)) (frobZ L p j x) := fun j S x h ↦
    h.of_equiv_equiv (adjoinFrobZEquiv l p j S) (frobZ L p j) rfl
  refine ⟨fun h ↦ ?_, key j S x⟩
  have := key (-j) _ _ h
  rwa [frobZ_neg_image_frobZ_image, frobZ_neg_apply_frobZ] at this

theorem isSeparable_adjoin_simple_frobZ_iff (j : ℤ) {s t : L} :
    IsSeparable l⟮frobZ L p j t⟯ (frobZ L p j s) ↔ IsSeparable l⟮t⟯ s := by
  have := isSeparable_adjoin_frobZ_iff (l := l) p j (S := {t}) (x := s)
  rwa [Set.image_singleton] at this

theorem isSeparable_adjoin_pair_frobZ_iff (j : ℤ) {s t u : L} :
    IsSeparable l⟮frobZ L p j t, frobZ L p j u⟯ (frobZ L p j s) ↔ IsSeparable l⟮t, u⟯ s := by
  have := isSeparable_adjoin_frobZ_iff (l := l) p j (S := {t, u}) (x := s)
  rwa [Set.image_insert_eq, Set.image_singleton] at this

end Transport

omit [IsRelAlgClosed l L] in
/-- Every point is stable under `Frob^{±1}` (blueprint Section 3, preamble). -/
theorem point_frobZ (j : ℤ) (s : L) : point l (frobZ L p j s) = point l s := by
  have h := isAlgebraic_adjoin_frobZ (l := l) p (-j) (frobZ L p j s)
  rw [frobZ_neg_apply_frobZ] at h
  exact point_eq_point_of_isAlgebraic h (isAlgebraic_adjoin_frobZ p j s)

theorem transcendental_frobZ_iff (j : ℤ) {s : L} :
    Transcendental l (frobZ L p j s) ↔ Transcendental l s := by
  rw [transcendental_iff_not_mem_range (l := l), transcendental_iff_not_mem_range (l := l),
    frobZ_mem_range_iff]

theorem samePoint_frobZ_left_iff (j : ℤ) {s t : L} :
    SamePoint l (frobZ L p j s) t ↔ SamePoint l s t := by
  rw [SamePoint, SamePoint, transcendental_frobZ_iff, point_frobZ]

theorem samePoint_frobZ_right_iff (j : ℤ) {s t : L} :
    SamePoint l s (frobZ L p j t) ↔ SamePoint l s t := by
  rw [SamePoint, SamePoint, transcendental_frobZ_iff, point_frobZ]

/-- `≈` is invariant under `Frob^j` (an automorphism of `L` preserving `l`). -/
theorem sepEquiv_frobZ_iff (j : ℤ) {s t : L} :
    SepEquiv l (frobZ L p j s) (frobZ L p j t) ↔ SepEquiv l s t := by
  rw [SepEquiv, SepEquiv, isSeparable_adjoin_simple_frobZ_iff (l := l),
    isSeparable_adjoin_simple_frobZ_iff (l := l)]

omit [Fact p.Prime] [PerfectField L] [IsRelAlgClosed l L] in
/-- A transcendental `u` is not separable over `l(u ^ p ^ n)` for `n > 0`: in the model `L_u`,
`d u ≠ 0` but `d (u ^ p ^ n) = 0`. -/
theorem not_isSeparable_adjoin_pow_pow {u : L} (hu : Transcendental l u) {n : ℕ} (hn : 0 < n) :
    ¬ IsSeparable l⟮u ^ p ^ n⟯ u := by
  intro h
  have hmem : u ∈ model l ![u] := self_mem_model_singleton u
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hn
  have hpow : u ^ p ^ (0 + m + 1) = (u ^ p ^ m) ^ p := by
    rw [zero_add, pow_succ, pow_mul]
  obtain ⟨c, hc, -, hd⟩ :=
    exists_modelD_eq_smul_of_isSeparable h (pow_mem hmem (p ^ (0 + m + 1)))
  rw [hpow, modelD_pow_char p (pow_mem hmem _), smul_zero] at hd
  have hb : AlgebraicIndependent l ![u] := algebraicIndependent_unique_type_iff.2 hu
  exact (linearIndependent_modelD hb).ne_zero 0 hd

/-- `t ≈ Frob^k t` only for `k = 0` (uniqueness in blueprint Lemma 3.2). -/
theorem eq_zero_of_sepEquiv_frobZ {t : L} (ht : Transcendental l t) {k : ℤ}
    (h : SepEquiv l t (frobZ L p k t)) : k = 0 := by
  have key : ∀ n : ℕ, 0 < n → ¬ IsSeparable l⟮frobZ L p n t⟯ t := fun n hn h' ↦ by
    rw [frobZ_natCast_apply] at h'
    exact not_isSeparable_adjoin_pow_pow p ht hn h'
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    · exact (key n hn h.1).elim
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rfl
    · have h2 := h.2
      rw [← isSeparable_adjoin_simple_frobZ_iff (l := l) p n, frobZ_apply_frobZ_neg] at h2
      exact (key n hn h2).elim

/-- **Blueprint Lemma 3.2**: for `s, t ∈ P \ l` (`P` a point) there is a unique `j ∈ Γ = ℤ` with
`s ≈ Frob^j t`. (That `≈` is an equivalence relation is `SepEquiv.refl`, `SepEquiv.symm`,
`SepEquiv.trans`.) -/
theorem existsUnique_sepEquiv_frobZ {s t : L} (h : SamePoint l s t) :
    ∃! j : ℤ, SepEquiv l s (frobZ L p j t) := by
  have : PerfectField l := IsRelAlgClosed.perfectField l L
  refine existsUnique_of_exists_of_unique ?_ fun j j' hj hj' ↦ ?_
  · -- existence, in the model `E = L_t` of elements separable over `l(t)`
    set E := model l ![t]
    have hb : AlgebraicIndependent l ![t] := algebraicIndependent_unique_type_iff.2 h.2.1
    have hsalg : IsAlgebraic (adjoin l (Set.range ![t])) s := by
      rw [Matrix.range_cons_empty]
      exact h.isAlgebraic
    obtain ⟨m, hm⟩ := exists_pow_pow_mem_model p hsalg
    have : CharP E p := (Algebra.charP_iff E L p).mpr inferInstance
    have hl := relAlgClosed_intermediateField E fun x hx ↦ IsRelAlgClosed.mem_range hx
    have hy : (⟨s ^ p ^ m, hm⟩ : E) ∉ (algebraMap l E).range := by
      rintro ⟨c, hc⟩
      have hc' : algebraMap l L c = s ^ p ^ m := congrArg Subtype.val hc
      exact h.1 (IsAlgebraic.of_pow (pow_pos (Fact.out : p.Prime).pos m)
        (hc' ▸ isAlgebraic_algebraMap c))
    obtain ⟨k, z, hz, hDz⟩ := exists_pow_pow_eq_kaehler_D_ne_zero p
      (algebraicIndependent_restrictFamily _ (mem_separableClosure_adjoin ![t]) hb)
      (isSeparable_adjoin_restrictFamily_separableClosure ![t]) hl hy
    have hz' : (z : L) ^ p ^ k = s ^ p ^ m := congrArg Subtype.val hz
    have hmodelD : modelD l ![t] z ≠ 0 := by
      rw [modelD_of_mem z.2]
      exact hDz
    -- `z ≈ t`
    have hzt : IsSeparable l⟮t⟯ (z : L) := mem_model_singleton_iff.1 z.2
    have hztr : Transcendental l (z : L) := by
      intro hzalg
      obtain ⟨c, hc⟩ := IsRelAlgClosed.mem_range hzalg
      apply hmodelD
      rw [← hc, modelD_algebraMap]
    have hpt : point l (z : L) = point l t :=
      point_eq_of_mem h.2.1 hztr (mem_point_iff.2 hzt.isIntegral.isAlgebraic)
    have htz : IsAlgebraic l⟮(z : L)⟯ t := by
      rw [← mem_point_iff, hpt]
      exact self_mem_point t
    have htz' : IsSeparable l⟮(z : L)⟯ t := by
      have := isSeparable_of_linearIndependent_modelD (B := ![t]) (x := ![(z : L)])
        (fun k ↦ by fin_cases k; exact z.2)
        (by rw [linearIndependent_unique_iff]; exact hmodelD) (self_mem_model_singleton t)
        (by rw [Matrix.range_cons_empty]; exact htz)
      rwa [Matrix.range_cons_empty] at this
    -- `z = Frob^(m - k) s`
    have hzs : (z : L) = frobZ L p ((m : ℤ) - k) s := by
      apply frobZ_injective p k
      rw [frobZ_natCast_apply, hz', ← frobZ_add_apply, show (k : ℤ) + ((m : ℤ) - k) = m by ring,
        frobZ_natCast_apply]
    refine ⟨k - m, ?_⟩
    have hsep : SepEquiv l (frobZ L p ((m : ℤ) - k) s) t := by
      rw [← hzs]
      exact ⟨hzt, htz'⟩
    rw [← sepEquiv_frobZ_iff p ((k : ℤ) - m), ← frobZ_add_apply,
      show (k : ℤ) - m + (m - k) = 0 by ring, frobZ_zero_apply] at hsep
    exact hsep
  · -- uniqueness
    have h1 : SepEquiv l (frobZ L p j t) (frobZ L p j' t) := hj.symm.trans hj'
    rw [← sepEquiv_frobZ_iff p (-j), frobZ_neg_apply_frobZ, ← frobZ_add_apply] at h1
    have := eq_zero_of_sepEquiv_frobZ p h.2.1 h1
    omega

open Classical in
variable (l) in
/-- **Blueprint Definition 3.3**, element-wise: the *level difference* `lev(s) - lev(t) ∈ Γ = ℤ`
of two transcendental elements `s, t` of the same point, i.e. the unique `j` with
`s ≈ Frob^j t` (Lemma 3.2, `levDiff_eq_iff`). If `¬ SamePoint l s t` it is `0`
(`levDiff_of_not_samePoint`); all other results assume `SamePoint l s t`. -/
noncomputable def levDiff (s t : L) : ℤ :=
  if h : ∃ j : ℤ, SamePoint l s t ∧ SepEquiv l s (frobZ L p j t) then h.choose else 0

omit [IsRelAlgClosed l L] in
theorem levDiff_of_not_samePoint {s t : L} (h : ¬ SamePoint l s t) : levDiff l p s t = 0 :=
  dite_eq_right fun h' ↦ (h h'.choose_spec.1).elim

/-- **Blueprint Lemma 3.2 / Definition 3.3**: `s ≈ Frob^(lev(s) - lev(t)) t`. -/
theorem levDiff_spec {s t : L} (h : SamePoint l s t) :
    SepEquiv l s (frobZ L p (levDiff l p s t) t) := by
  obtain ⟨j, hj, -⟩ := existsUnique_sepEquiv_frobZ p h
  have hex : ∃ j : ℤ, SamePoint l s t ∧ SepEquiv l s (frobZ L p j t) := ⟨j, h, hj⟩
  rw [levDiff, dite_eq_left hex]
  exact hex.choose_spec.2

/-- **Blueprint Lemma 3.2 / Definition 3.3**: `lev(s) - lev(t) = j` iff `s ≈ Frob^j t`. -/
theorem levDiff_eq_iff {s t : L} (h : SamePoint l s t) {j : ℤ} :
    levDiff l p s t = j ↔ SepEquiv l s (frobZ L p j t) := by
  refine ⟨fun hj ↦ hj ▸ levDiff_spec p h, fun hj ↦ ?_⟩
  exact (existsUnique_sepEquiv_frobZ p h).unique (levDiff_spec p h) hj

/-- `lev(s) = lev(t)` iff `s ≈ t`. -/
theorem levDiff_eq_zero_iff {s t : L} (h : SamePoint l s t) :
    levDiff l p s t = 0 ↔ SepEquiv l s t := by
  rw [levDiff_eq_iff p h, frobZ_zero_apply]

theorem levDiff_self {s : L} (hs : Transcendental l s) : levDiff l p s s = 0 :=
  (levDiff_eq_zero_iff p (samePoint_refl hs)).2 (SepEquiv.refl s)

/-- Antisymmetry: `lev(t) - lev(s) = -(lev(s) - lev(t))`. -/
theorem levDiff_swap {s t : L} (h : SamePoint l s t) : levDiff l p t s = -levDiff l p s t := by
  rw [levDiff_eq_iff p h.symm]
  have := levDiff_spec p h
  rw [← sepEquiv_frobZ_iff p (-levDiff l p s t), frobZ_neg_apply_frobZ] at this
  exact this.symm

/-- Cocycle rule: `(lev(s) - lev(t)) + (lev(t) - lev(u)) = lev(s) - lev(u)`. -/
theorem levDiff_add_levDiff {s t u : L} (hst : SamePoint l s t) (htu : SamePoint l t u) :
    levDiff l p s t + levDiff l p t u = levDiff l p s u := by
  symm
  rw [levDiff_eq_iff p (hst.trans htu), frobZ_add_apply]
  have h2 := levDiff_spec p htu
  rw [← sepEquiv_frobZ_iff p (levDiff l p s t)] at h2
  exact (levDiff_spec p hst).trans h2

/-- `lev(Frob^j s) = lev(s) + j` (the action of `Γ` on `Λ(P)`, Definition 3.3). -/
theorem levDiff_frobZ_left {s t : L} (h : SamePoint l s t) (j : ℤ) :
    levDiff l p (frobZ L p j s) t = levDiff l p s t + j := by
  rw [levDiff_eq_iff p ((samePoint_frobZ_left_iff p j).2 h), add_comm, frobZ_add_apply,
    sepEquiv_frobZ_iff]
  exact levDiff_spec p h

theorem levDiff_frobZ_right {s t : L} (h : SamePoint l s t) (j : ℤ) :
    levDiff l p s (frobZ L p j t) = levDiff l p s t - j := by
  rw [levDiff_eq_iff p ((samePoint_frobZ_right_iff p j).2 h), ← frobZ_add_apply, sub_add_cancel]
  exact levDiff_spec p h

/-- The level of `s` only depends on its `≈`-class (left argument). -/
theorem SepEquiv.levDiff_left {s s' t : L} (hs : SepEquiv l s' s) (h : SamePoint l s t) :
    levDiff l p s' t = levDiff l p s t := by
  have hs' : SamePoint l s' t := (hs.symm.samePoint h.1).symm.trans h
  rw [levDiff_eq_iff p hs']
  exact hs.trans (levDiff_spec p h)

/-- The level of `t` only depends on its `≈`-class (right argument). -/
theorem SepEquiv.levDiff_right {s t t' : L} (ht : SepEquiv l t' t) (h : SamePoint l s t) :
    levDiff l p s t' = levDiff l p s t := by
  have ht' : SamePoint l s t' := h.trans (ht.symm.samePoint h.2.1)
  rw [levDiff_eq_iff p ht']
  exact (levDiff_spec p h).trans ((sepEquiv_frobZ_iff p _).2 ht.symm)

/-- `lev(c s) = lev(s)` for `c ∈ lˣ` (blueprint line 406). -/
theorem levDiff_algebraMap_mul_left {c : l} (hc : c ≠ 0) {s t : L} (h : SamePoint l s t) :
    levDiff l p (algebraMap l L c * s) t = levDiff l p s t :=
  (sepEquiv_algebraMap_mul hc s).levDiff_left p h

/-- `lev(s ^ N) = lev(s)` for `N` prime to `p` (blueprint line 406). -/
theorem levDiff_pow_left {N : ℕ} (hN : N.Coprime p) {s t : L} (h : SamePoint l s t) :
    levDiff l p (s ^ N) t = levDiff l p s t := by
  have hN' : (N : L) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff L p]
    intro hpN
    exact (Fact.out : p.Prime).one_lt.ne' ((Nat.coprime_comm.1 hN).eq_one_of_dvd hpN)
  exact (sepEquiv_pow hN' s).levDiff_left p h

/-- `lev(s⁻¹) = lev(s)` (blueprint line 407). -/
theorem levDiff_inv_left {s t : L} (h : SamePoint l s t) :
    levDiff l p s⁻¹ t = levDiff l p s t :=
  (sepEquiv_inv s).levDiff_left p h

/-- `lev(s) ≥ lev(t)` iff `s` is separable algebraic over `l(t)`. The "if" direction is the remark
of blueprint line 460; the "only if" direction is used in the proof of Proposition 6.12
(line 700). -/
theorem levDiff_nonneg_iff {s t : L} (h : SamePoint l s t) :
    0 ≤ levDiff l p s t ↔ IsSeparable l⟮t⟯ s := by
  have hspec := levDiff_spec p h
  constructor
  · intro hd
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hd
    rw [hn, frobZ_natCast_apply] at hspec
    exact IsSeparable.of_le (adjoin_simple_le_iff.2 (pow_mem (mem_adjoin_simple_self l t) _))
      hspec.1
  · intro hs
    by_contra hd
    replace hd := not_le.1 hd
    obtain ⟨n, hn⟩ := Int.exists_eq_neg_ofNat hd.le
    have hn0 : 0 < n := by omega
    set u := frobZ L p (levDiff l p s t) t
    have hut : IsSeparable l⟮t⟯ u := isSeparable_adjoin_simple_trans hspec.2 hs
    have htu : t = u ^ p ^ n := by
      rw [← frobZ_natCast_apply, ← frobZ_add_apply, hn]
      simp [frobZ_zero_apply]
    rw [htu] at hut
    have hu : Transcendental l u := (transcendental_frobZ_iff p _).2 h.2.1
    exact not_isSeparable_adjoin_pow_pow p hu hn0 hut

end Levels

end MilnorAlgDep
