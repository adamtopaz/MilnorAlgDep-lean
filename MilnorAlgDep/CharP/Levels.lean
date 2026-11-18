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

/-- Blueprint Lemma 3.2: `≈` is transitive. -/
theorem SepEquiv.trans {s t u : L} (hst : SepEquiv l s t) (htu : SepEquiv l t u) :
    SepEquiv l s u := by
  sorry

/-- If `s ≈ t` and `s` is transcendental over `l`, then `s` and `t` lie in the same point. -/
theorem SepEquiv.samePoint {s t : L} (h : SepEquiv l s t) (hs : Transcendental l s) :
    SamePoint l s t := by
  sorry

/-- `c s ≈ s` for `c ∈ lˣ` (used for the well-definedness of `lev(v)`, `v ∈ V`, blueprint
line 406). -/
theorem sepEquiv_algebraMap_mul {c : l} (hc : c ≠ 0) (s : L) :
    SepEquiv l (algebraMap l L c * s) s := by
  sorry

/-- `s⁻¹ ≈ s` (used for `lev(-v) = lev(v)`, blueprint line 407). -/
theorem sepEquiv_inv (s : L) : SepEquiv l s⁻¹ s := by
  sorry

/-- `s ^ N ≈ s` if `N` is prime to the characteristic, i.e. `(N : L) ≠ 0` (used for the
well-definedness of `lev(v)`, `v ∈ V`, blueprint line 406). -/
theorem sepEquiv_pow {N : ℕ} (hN : (N : L) ≠ 0) (s : L) : SepEquiv l (s ^ N) s := by
  sorry

/-- If `s ≈ t` and `s ∈ L_B`, then `t ∈ L_B` and `d s`, `d t` span the same line of `Ω_B` (by
Lemma 2.3 (S2), each differential is a multiple of the other). In particular `d s ≠ 0` iff
`d t ≠ 0` (used in the proofs of Lemmas 4.3 and 6.2). -/
theorem SepEquiv.span_modelD_eq {ι : Type*} {B : ι → L} {s t : L} (h : SepEquiv l s t)
    (hs : s ∈ model l B) :
    (model l B) ∙ modelD l B s = (model l B) ∙ modelD l B t := by
  sorry

/-- If `s ≈ t` and `s ∈ L_B`, then `t ∈ L_B`. -/
theorem SepEquiv.mem_model {ι : Type*} {B : ι → L} {s t : L} (h : SepEquiv l s t)
    (hs : s ∈ model l B) : t ∈ model l B := by
  sorry

/-- The field `L_t` of elements separable algebraic over `l(t)` is contained in the point `Q_t`. -/
theorem model_le_point (t : L) : model l ![t] ≤ point l t := by
  sorry

/-- If `s` is separable algebraic over `l(t)` and `t ∈ L_B`, then `s ∈ L_B` and `d s = c • d t` in
`Ω_B` for some `c` which is separable algebraic over `l(t)`, hence lies in the point `Q_t`
(`model_le_point`). This is the fact "`db = b_a da` with `b_a` in the field of elements separable
over `l(a)`, which is contained in `Q_x`" of blueprint lines 535, 676-677 and 700. -/
theorem exists_modelD_eq_smul_of_isSeparable {ι : Type*} {B : ι → L} {s t : L}
    (hs : IsSeparable l⟮t⟯ s) (ht : t ∈ model l B) :
    ∃ (c : L) (hc : c ∈ model l B), c ∈ model l ![t] ∧
      modelD l B s = (⟨c, hc⟩ : model l B) • modelD l B t := by
  sorry

end SepEquiv

section Levels

variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]

/-- Every point is stable under `Frob^{±1}` (blueprint Section 3, preamble). -/
theorem point_frobZ (j : ℤ) (s : L) : point l (frobZ L p j s) = point l s := by
  sorry

theorem transcendental_frobZ_iff (j : ℤ) {s : L} :
    Transcendental l (frobZ L p j s) ↔ Transcendental l s := by
  sorry

theorem samePoint_frobZ_left_iff (j : ℤ) {s t : L} :
    SamePoint l (frobZ L p j s) t ↔ SamePoint l s t := by
  sorry

theorem samePoint_frobZ_right_iff (j : ℤ) {s t : L} :
    SamePoint l s (frobZ L p j t) ↔ SamePoint l s t := by
  sorry

/-- `≈` is invariant under `Frob^j` (an automorphism of `L` preserving `l`). -/
theorem sepEquiv_frobZ_iff (j : ℤ) {s t : L} :
    SepEquiv l (frobZ L p j s) (frobZ L p j t) ↔ SepEquiv l s t := by
  sorry

/-- **Blueprint Lemma 3.2**: for `s, t ∈ P \ l` (`P` a point) there is a unique `j ∈ Γ = ℤ` with
`s ≈ Frob^j t`. (That `≈` is an equivalence relation is `SepEquiv.refl`, `SepEquiv.symm`,
`SepEquiv.trans`.) -/
theorem existsUnique_sepEquiv_frobZ {s t : L} (h : SamePoint l s t) :
    ∃! j : ℤ, SepEquiv l s (frobZ L p j t) := by
  sorry

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
  sorry

/-- **Blueprint Lemma 3.2 / Definition 3.3**: `lev(s) - lev(t) = j` iff `s ≈ Frob^j t`. -/
theorem levDiff_eq_iff {s t : L} (h : SamePoint l s t) {j : ℤ} :
    levDiff l p s t = j ↔ SepEquiv l s (frobZ L p j t) := by
  sorry

/-- `lev(s) = lev(t)` iff `s ≈ t`. -/
theorem levDiff_eq_zero_iff {s t : L} (h : SamePoint l s t) :
    levDiff l p s t = 0 ↔ SepEquiv l s t := by
  sorry

theorem levDiff_self {s : L} (hs : Transcendental l s) : levDiff l p s s = 0 := by
  sorry

/-- Antisymmetry: `lev(t) - lev(s) = -(lev(s) - lev(t))`. -/
theorem levDiff_swap {s t : L} (h : SamePoint l s t) : levDiff l p t s = -levDiff l p s t := by
  sorry

/-- Cocycle rule: `(lev(s) - lev(t)) + (lev(t) - lev(u)) = lev(s) - lev(u)`. -/
theorem levDiff_add_levDiff {s t u : L} (hst : SamePoint l s t) (htu : SamePoint l t u) :
    levDiff l p s t + levDiff l p t u = levDiff l p s u := by
  sorry

/-- `lev(Frob^j s) = lev(s) + j` (the action of `Γ` on `Λ(P)`, Definition 3.3). -/
theorem levDiff_frobZ_left {s t : L} (h : SamePoint l s t) (j : ℤ) :
    levDiff l p (frobZ L p j s) t = levDiff l p s t + j := by
  sorry

theorem levDiff_frobZ_right {s t : L} (h : SamePoint l s t) (j : ℤ) :
    levDiff l p s (frobZ L p j t) = levDiff l p s t - j := by
  sorry

/-- The level of `s` only depends on its `≈`-class (left argument). -/
theorem SepEquiv.levDiff_left {s s' t : L} (hs : SepEquiv l s' s) (h : SamePoint l s t) :
    levDiff l p s' t = levDiff l p s t := by
  sorry

/-- The level of `t` only depends on its `≈`-class (right argument). -/
theorem SepEquiv.levDiff_right {s t t' : L} (ht : SepEquiv l t' t) (h : SamePoint l s t) :
    levDiff l p s t' = levDiff l p s t := by
  sorry

/-- `lev(c s) = lev(s)` for `c ∈ lˣ` (blueprint line 406). -/
theorem levDiff_algebraMap_mul_left {c : l} (hc : c ≠ 0) {s t : L} (h : SamePoint l s t) :
    levDiff l p (algebraMap l L c * s) t = levDiff l p s t := by
  sorry

/-- `lev(s ^ N) = lev(s)` for `N` prime to `p` (blueprint line 406). -/
theorem levDiff_pow_left {N : ℕ} (hN : N.Coprime p) {s t : L} (h : SamePoint l s t) :
    levDiff l p (s ^ N) t = levDiff l p s t := by
  sorry

/-- `lev(s⁻¹) = lev(s)` (blueprint line 407). -/
theorem levDiff_inv_left {s t : L} (h : SamePoint l s t) :
    levDiff l p s⁻¹ t = levDiff l p s t := by
  sorry

/-- `lev(s) ≥ lev(t)` iff `s` is separable algebraic over `l(t)`. The "if" direction is the remark
of blueprint line 460; the "only if" direction is used in the proof of Proposition 6.9
(line 700). -/
theorem levDiff_nonneg_iff {s t : L} (h : SamePoint l s t) :
    0 ≤ levDiff l p s t ↔ IsSeparable l⟮t⟯ s := by
  sorry

end Levels

end MilnorAlgDep
