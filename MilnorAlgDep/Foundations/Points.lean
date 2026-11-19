module

public import MilnorAlgDep.Foundations.AlgIndep
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# Points

Blueprint, Section 2.1 (points) and (V3) in Section 2.3.

Let `l ⊆ L` be relatively algebraically closed. For `a ∈ L \ l` the *point* `Q_a` is the relative
algebraic closure of `l(a)` in `L`; it is a relatively algebraically closed subfield of
transcendence degree one over `l`. For `v ∈ V l L` non-zero, `Q_v = Q_a` for any representative
`(N, a)` of `v`; and for a point `Q`, `G_Q ≤ V l L` is the image of `(Qˣ/lˣ) ⊗ ℚ`.

## Main definitions

* `MilnorAlgDep.point l a : IntermediateField l L`: the point `Q_a` (defined for every `a : L`;
  for `a` algebraic over `l` it is the relative algebraic closure of `l` in `L`).
* `MilnorAlgDep.pointV v : IntermediateField l L`: the point `Q_v` of `v ∈ V l L`, defined as
  `Q_a` for a chosen representative; `pointV_eq_point` shows it does not depend on the choice.
* `MilnorAlgDep.pointGroup Q : Submodule ℚ (V l L)`: the subgroup `G_Q`, the span of the classes
  `[a]` with `a ∈ Qˣ`.

## Main statements

* `point_eq_point_iff_mem`, `mem_point_iff_not_algebraicIndependent`: for `a, b ∉ l`,
  `Q_a = Q_b ↔ b ∈ Q_a ↔ a, b are algebraically dependent over l`.
* `point_inf_point_eq_bot`, `pointV_inf_pointV_eq_bot`: two distinct points intersect in `l`.
* `mem_pointGroup_point_iff`: `G_Q = {v | v = 0 ∨ Q_v = Q}`.
* `vAlgIndep_pair_iff`: non-zero `v, w ∈ V l L` are algebraically dependent iff `Q_v = Q_w`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf IntermediateField

variable {l L : Type*} [Field l] [Field L] [Algebra l L]

section point

variable (l) in
/-- Blueprint 2.1: the *point* `Q_a = [a]_L`, the relative algebraic closure of `l(a)` in `L`.
(For `a` algebraic over `l` this is the relative algebraic closure of `l` in `L`; the blueprint only
uses `Q_a` for `a ∉ l`.) -/
noncomputable def point (a : L) : IntermediateField l L :=
  (algebraicClosure l⟮a⟯ L).restrictScalars l

theorem mem_point_iff {a x : L} : x ∈ point l a ↔ IsAlgebraic l⟮a⟯ x := by
  rw [point, mem_restrictScalars, mem_algebraicClosure_iff]

theorem self_mem_point (a : L) : a ∈ point l a := by
  rw [mem_point_iff]
  exact isAlgebraic_algebraMap (⟨a, mem_adjoin_simple_self l a⟩ : l⟮a⟯)

/-- A point is relatively algebraically closed in `L` (it is a flat). -/
theorem point_isRelAlgClosed (a : L) : ∀ x : L, IsAlgebraic (point l a) x → x ∈ point l a := by
  intro x hx
  have h : x ∈ algebraicClosure (algebraicClosure l⟮a⟯ L) L := mem_algebraicClosure_iff.2 hx
  rw [algebraicClosure.algebraicClosure_eq_bot, mem_bot] at h
  obtain ⟨y, rfl⟩ := h
  exact y.2

/-- The point `Q_a` is the closure of `{a}` in the algebraic matroid of `L / l`. -/
theorem coe_point (a : L) :
    (point l a : Set L) = (AlgebraicIndependent.matroid l L).closure {a} := by
  ext x
  rw [SetLike.mem_coe, mem_point_iff, isAlgebraic_adjoin_simple_iff_mem_closure]

/-- If `a` and `b` are algebraic over each other (over `l`), they define the same point. -/
theorem point_eq_point_of_isAlgebraic {a b : L} (hab : IsAlgebraic l⟮a⟯ b)
    (hba : IsAlgebraic l⟮b⟯ a) : point l a = point l b := by
  have h1 := isAlgebraic_adjoin_simple_iff_mem_closure.1 hab
  have h2 := isAlgebraic_adjoin_simple_iff_mem_closure.1 hba
  refine SetLike.coe_injective ?_
  rw [coe_point, coe_point]
  exact (Matroid.closure_subset_closure_of_subset_closure (Set.singleton_subset_iff.2 h2)).antisymm
    (Matroid.closure_subset_closure_of_subset_closure (Set.singleton_subset_iff.2 h1))

/-- Blueprint 2.1: for `a ∉ l`, an element `b` lies in `Q_a` if and only if `a` and `b` are
algebraically dependent over `l`. -/
theorem mem_point_iff_not_algebraicIndependent {a b : L} (ha : Transcendental l a) :
    b ∈ point l a ↔ ¬ AlgebraicIndependent l ![a, b] := by
  rw [mem_point_iff, algebraicIndependent_pair_iff]
  constructor
  · rintro hb ⟨_, hb'⟩
    exact hb' hb
  · intro h
    by_contra hb
    exact h ⟨ha, hb⟩

/-- Blueprint 2.1: for `a, b ∉ l`, `Q_a = Q_b` if and only if `b ∈ Q_a`. -/
theorem point_eq_point_iff_mem {a b : L} (ha : Transcendental l a) (hb : Transcendental l b) :
    point l a = point l b ↔ b ∈ point l a := by
  refine ⟨fun h ↦ by rw [h]; exact self_mem_point b, fun hmem ↦ ?_⟩
  have hdep : ¬ AlgebraicIndependent l ![b, a] := by
    rw [← algebraicIndependent_pair_comm]
    exact (mem_point_iff_not_algebraicIndependent ha).1 hmem
  have hamem : a ∈ point l b := (mem_point_iff_not_algebraicIndependent hb).2 hdep
  exact point_eq_point_of_isAlgebraic (mem_point_iff.1 hmem) (mem_point_iff.1 hamem)

/-- Blueprint 2.1: for `a, b ∉ l`, `Q_a = Q_b` if and only if `a` and `b` are algebraically
dependent over `l`. -/
theorem point_eq_point_iff_not_algebraicIndependent {a b : L} (ha : Transcendental l a)
    (hb : Transcendental l b) : point l a = point l b ↔ ¬ AlgebraicIndependent l ![a, b] := by
  rw [point_eq_point_iff_mem ha hb, mem_point_iff_not_algebraicIndependent ha]

/-- If `b ∉ l` lies in `Q_a`, then `Q_b = Q_a`: a point is the point of each of its
non-constant elements. -/
theorem point_eq_of_mem {a b : L} (ha : Transcendental l a) (hb : Transcendental l b)
    (h : b ∈ point l a) : point l b = point l a :=
  ((point_eq_point_iff_mem ha hb).2 h).symm

/-- Blueprint 2.1: two distinct points intersect in `l`. -/
theorem point_inf_point_eq_bot [IsRelAlgClosed l L] {a b : L} (ha : Transcendental l a)
    (hb : Transcendental l b) (h : point l a ≠ point l b) : point l a ⊓ point l b = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  rw [mem_bot]
  by_contra hx'
  have htr : Transcendental l x := IsRelAlgClosed.transcendental fun h ↦ hx' h
  have h1 := point_eq_of_mem ha htr hx.1
  have h2 := point_eq_of_mem hb htr hx.2
  exact h (h1.symm.trans h2)

end point

section pointV

variable (l) in
/-- Blueprint (V3): the point `Q_v` of `v ∈ V l L`, defined as `Q_a` for the representative
`(repNat v, repUnit v)` chosen by `VOf.repNat`/`VOf.repUnit`; by `pointV_eq_point` it equals
`Q_a` for every `(N, a)` with `N ≥ 1` and `N • v = [a]`. (For `v = 0` this is the relative algebraic
closure of `l` in `L`; the blueprint only uses `Q_v` for `v ≠ 0`.) -/
noncomputable def pointV (v : V l L) : IntermediateField l L :=
  point l (repUnit v : L)

/-- Blueprint (V3): `Q_v = Q_a` for every `(N, a)` with `N ≥ 1` and `N • v = [a]`; in particular
`Q_v` does not depend on the choice of representative. -/
theorem pointV_eq_point {v : V l L} {N : ℕ} {a : Lˣ} (hN : 0 < N)
    (h : N • v = cls (constUnits l L) (.ofMul a)) : pointV l v = point l (a : L) := by
  have hr := repNat_nsmul v
  refine point_eq_point_of_isAlgebraic ?_ ?_
  · refine V.isAlgebraic_adjoin_of_zsmul_cls_eq (repNat_pos v) (N := N) ?_
    rw [natCast_zsmul, natCast_zsmul, ← h, ← hr, smul_smul, smul_smul, mul_comm]
  · refine V.isAlgebraic_adjoin_of_zsmul_cls_eq hN (N := repNat v) ?_
    rw [natCast_zsmul, natCast_zsmul, ← h, ← hr, smul_smul, smul_smul, mul_comm]

theorem pointV_cls (a : Lˣ) : pointV l (cls (constUnits l L) (.ofMul a)) = point l (a : L) :=
  pointV_eq_point one_pos (one_nsmul _)

/-- `Q_{q • v} = Q_v` for `q ≠ 0`. -/
theorem pointV_smul {v : V l L} {q : ℚ} (hq : q ≠ 0) : pointV l (q • v) = pointV l v := by
  rw [pointV_eq_point (Nat.mul_pos q.den_pos (repNat_pos v)) (nsmul_smul_eq_cls (repNat_nsmul v) q),
    pointV]
  have hnum : q.num ≠ 0 := Rat.num_ne_zero.2 hq
  refine point_eq_point_of_isAlgebraic ?_ ?_
  · refine V.isAlgebraic_adjoin_of_zsmul_cls_eq (Int.natAbs_pos.2 hnum) (N := q.num.sign) ?_
    rw [cls_zpow, smul_smul, Int.sign_mul_self_eq_natAbs]
  · refine V.isAlgebraic_adjoin_of_zsmul_cls_eq one_pos (N := q.num) ?_
    rw [Nat.cast_one, one_smul, cls_zpow]

theorem pointV_neg (v : V l L) : pointV l (-v) = pointV l v := by
  rw [← neg_one_smul ℚ v, pointV_smul (by norm_num)]

/-- Blueprint (V3): non-zero `v, w ∈ V l L` are algebraically dependent if and only if
`Q_v = Q_w`. -/
theorem vAlgIndep_pair_iff [IsRelAlgClosed l L] {v w : V l L} (hv : v ≠ 0) (hw : w ≠ 0) :
    VAlgIndep l ![v, w] ↔ pointV l v ≠ pointV l w := by
  have ha : Transcendental l (repUnit v : L) := IsRelAlgClosed.transcendental
    (V.not_mem_range_of_nsmul_eq_cls hv (repNat_pos v) (repNat_nsmul v))
  have hb : Transcendental l (repUnit w : L) := IsRelAlgClosed.transcendental
    (V.not_mem_range_of_nsmul_eq_cls hw (repNat_pos w) (repNat_nsmul w))
  have hN : ∀ i, 0 < ![repNat v, repNat w] i := by
    intro i
    fin_cases i
    exacts [repNat_pos v, repNat_pos w]
  have hrep : ∀ i, ![repNat v, repNat w] i • ![v, w] i =
      cls (constUnits l L) (.ofMul (![repUnit v, repUnit w] i)) := by
    intro i
    fin_cases i
    exacts [repNat_nsmul v, repNat_nsmul w]
  have hfun : (fun i ↦ ((![repUnit v, repUnit w] i : Lˣ) : L)) =
      ![(repUnit v : L), (repUnit w : L)] := by
    ext i
    fin_cases i <;> rfl
  rw [VAlgIndep.iff_of_nsmul_eq_cls hN hrep, hfun, pointV, pointV, Ne,
    point_eq_point_iff_not_algebraicIndependent ha hb, not_not]

/-- Two distinct points meet in `l`, for points of elements of `V l L`: if `v, w` are
algebraically independent, then `Q_v ∩ Q_w = l`. -/
theorem pointV_inf_pointV_eq_bot [IsRelAlgClosed l L] {v w : V l L} (h : VAlgIndep l ![v, w]) :
    pointV l v ⊓ pointV l w = ⊥ := by
  have hv : v ≠ 0 := h.ne_zero 0
  have hw : w ≠ 0 := h.ne_zero 1
  exact point_inf_point_eq_bot
    (IsRelAlgClosed.transcendental (V.not_mem_range_of_nsmul_eq_cls hv (VOf.repNat_pos v)
      (VOf.repNat_nsmul v)))
    (IsRelAlgClosed.transcendental (V.not_mem_range_of_nsmul_eq_cls hw (VOf.repNat_pos w)
      (VOf.repNat_nsmul w)))
    ((vAlgIndep_pair_iff hv hw).1 h)

/-- An element of `Q_v ∩ Q_w`, for algebraically independent `v, w`, lies in `l`. -/
theorem mem_range_of_mem_pointV_of_vAlgIndep [IsRelAlgClosed l L] {v w : V l L}
    (h : VAlgIndep l ![v, w]) {z : L} (hv : z ∈ pointV l v) (hw : z ∈ pointV l w) :
    z ∈ (algebraMap l L).range := by
  have hz : z ∈ pointV l v ⊓ pointV l w := ⟨hv, hw⟩
  rw [pointV_inf_pointV_eq_bot h, IntermediateField.mem_bot] at hz
  obtain ⟨c, hc⟩ := hz
  exact ⟨c, hc⟩

end pointV

section pointGroup

/-- Blueprint (V3): for an intermediate field `Q` of `L / l` (typically a point), the subgroup
`G_Q ≤ V l L`, the image of `(Qˣ/lˣ) ⊗ ℚ`: the `ℚ`-span of the classes `[a]` with `a ∈ Qˣ`. -/
noncomputable def pointGroup (Q : IntermediateField l L) : Submodule ℚ (V l L) :=
  Submodule.span ℚ ((fun a : Lˣ ↦ cls (constUnits l L) (.ofMul a)) '' {a | (a : L) ∈ Q})

theorem mem_pointGroup_iff {Q : IntermediateField l L} {v : V l L} :
    v ∈ pointGroup Q ↔ ∃ (N : ℕ) (a : Lˣ), 0 < N ∧ (a : L) ∈ Q ∧
      N • v = cls (constUnits l L) (.ofMul a) := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact ⟨1, a, one_pos, ha, one_nsmul _⟩
    | zero => exact ⟨1, 1, one_pos, by simp, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨N, a, hN, ha, hxa⟩ := hx
      obtain ⟨M, b, hM, hb, hyb⟩ := hy
      refine ⟨N * M, a ^ M * b ^ N, Nat.mul_pos hN hM, ?_, ?_⟩
      · push_cast
        exact mul_mem (pow_mem ha M) (pow_mem hb N)
      · rw [smul_add, cls_mul, cls_pow, cls_pow, ← hxa, ← hyb, smul_smul, smul_smul, mul_comm M N]
    | smul q x _ hx =>
      obtain ⟨N, a, hN, ha, hxa⟩ := hx
      refine ⟨q.den * N, a ^ q.num, Nat.mul_pos q.den_pos hN, ?_, nsmul_smul_eq_cls hxa q⟩
      rw [Units.val_zpow_eq_zpow_val]
      exact zpow_mem ha _
  · rintro ⟨N, a, hN, ha, h⟩
    have hv : v = (N : ℚ)⁻¹ • cls (constUnits l L) (.ofMul a) := by
      rw [← h, ← Nat.cast_smul_eq_nsmul ℚ, inv_smul_smul₀ (Nat.cast_ne_zero.2 hN.ne')]
    rw [hv]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩)

/-- Blueprint (V3): for a point `Q = Q_b` (`b ∉ l`), `G_Q = {v | v = 0 or Q_v = Q}`. -/
theorem mem_pointGroup_point_iff [IsRelAlgClosed l L] {b : L} (hb : Transcendental l b)
    {v : V l L} : v ∈ pointGroup (point l b) ↔ v = 0 ∨ pointV l v = point l b := by
  constructor
  · rintro hmem
    obtain ⟨N, a, hN, ha, h⟩ := mem_pointGroup_iff.1 hmem
    by_cases hv : v = 0
    · exact Or.inl hv
    refine Or.inr ?_
    have htr : Transcendental l (a : L) :=
      IsRelAlgClosed.transcendental (V.not_mem_range_of_nsmul_eq_cls hv hN h)
    rw [pointV_eq_point hN h, point_eq_of_mem hb htr ha]
  · rintro (rfl | h)
    · exact Submodule.zero_mem _
    · refine mem_pointGroup_iff.2 ⟨repNat v, repUnit v, repNat_pos v, ?_, repNat_nsmul v⟩
      rw [← h]
      exact self_mem_point _

/-- Blueprint (V3): for `v ≠ 0`, `G_{Q_v} = {w | w = 0 or Q_w = Q_v}`. -/
theorem mem_pointGroup_pointV_iff [IsRelAlgClosed l L] {v w : V l L} (hv : v ≠ 0) :
    w ∈ pointGroup (pointV l v) ↔ w = 0 ∨ pointV l w = pointV l v :=
  mem_pointGroup_point_iff (IsRelAlgClosed.transcendental
    (V.not_mem_range_of_nsmul_eq_cls hv (repNat_pos v) (repNat_nsmul v)))

theorem mem_pointGroup_pointV (v : V l L) : v ∈ pointGroup (pointV l v) :=
  mem_pointGroup_iff.2 ⟨repNat v, repUnit v, repNat_pos v, self_mem_point _, repNat_nsmul v⟩

end pointGroup

section Closure

/-! ### Points and the algebraic matroid -/

variable [IsRelAlgClosed l L]

/-- If `w ∈ G_{Q_v}`, then representatives of `w` lie in the closure of representatives of
`v`. -/
theorem mem_closure_of_mem_pointGroup {v w : V l L} (hv : v ≠ 0) {N K : ℕ} {a b : Lˣ}
    (hN : 0 < N) (ha : N • v = cls (constUnits l L) (.ofMul a)) (hK : 0 < K)
    (hb : K • w = cls (constUnits l L) (.ofMul b)) (hw : w ∈ pointGroup (pointV l v)) :
    (b : L) ∈ (AlgebraicIndependent.matroid l L).closure {(a : L)} := by
  rcases (mem_pointGroup_pointV_iff hv).1 hw with rfl | hpt
  · rw [smul_zero, eq_comm, V.cls_eq_zero_iff'] at hb
    exact mem_closure_of_mem_range hb
  · rw [← coe_point, ← pointV_eq_point hN ha, ← hpt, pointV_eq_point hK hb]
    exact self_mem_point _

/-- If `v, w` are non-zero and in different points, then `v + w` is non-zero and lies in neither
of the two points (blueprint line 413). -/
theorem pointV_add_ne {v w : V l L} (hv : v ≠ 0) (hw : w ≠ 0) (hvw : pointV l v ≠ pointV l w) :
    v + w ≠ 0 ∧ pointV l (v + w) ≠ pointV l v ∧ pointV l (v + w) ≠ pointV l w := by
  have hw' : w ∉ pointGroup (pointV l v) := fun h ↦ by
    rcases (mem_pointGroup_pointV_iff hv).1 h with h | h
    · exact hw h
    · exact hvw h.symm
  have hv' : v ∉ pointGroup (pointV l w) := fun h ↦ by
    rcases (mem_pointGroup_pointV_iff hw).1 h with h | h
    · exact hv h
    · exact hvw h
  refine ⟨fun h0 ↦ hw' ?_, fun he ↦ hw' ?_, fun he ↦ hv' ?_⟩
  · rw [eq_neg_of_add_eq_zero_right h0]
    exact neg_mem (mem_pointGroup_pointV v)
  · have hs : v + w ≠ 0 := fun h0 ↦ hw' (by
      rw [eq_neg_of_add_eq_zero_right h0]
      exact neg_mem (mem_pointGroup_pointV v))
    have := sub_mem ((mem_pointGroup_pointV_iff hv).2 (Or.inr he)) (mem_pointGroup_pointV v)
    rwa [add_sub_cancel_left] at this
  · have hs : v + w ≠ 0 := fun h0 ↦ hw' (by
      rw [eq_neg_of_add_eq_zero_right h0]
      exact neg_mem (mem_pointGroup_pointV v))
    have := sub_mem ((mem_pointGroup_pointV_iff hw).2 (Or.inr he)) (mem_pointGroup_pointV w)
    rwa [add_sub_cancel_right] at this

/-- If `v, w` are algebraically independent and `v'` lies in `G_{Q_v}`, then `v, w + v'` are
algebraically independent (used in the proof of Proposition 6.1). -/
theorem VAlgIndep.add_of_mem_pointGroup {v w v' : V l L} (h : VAlgIndep l ![v, w])
    (hv' : v' ∈ pointGroup (pointV l v)) : VAlgIndep l ![v, w + v'] := by
  have hv : v ≠ 0 := h.ne_zero 0
  have hw : w ≠ 0 := h.ne_zero 1
  have hpt := (vAlgIndep_pair_iff hv hw).1 h
  have hw' : w ∉ pointGroup (pointV l v) := fun hm ↦ by
    rcases (mem_pointGroup_pointV_iff hv).1 hm with h0 | h0
    · exact hw h0
    · exact hpt h0.symm
  have hsum : w + v' ∉ pointGroup (pointV l v) := fun hm ↦ hw' (by
    have := sub_mem hm hv'
    rwa [add_sub_cancel_right] at this)
  have hs0 : w + v' ≠ 0 := fun h0 ↦ hsum (by rw [h0]; exact zero_mem _)
  rw [vAlgIndep_pair_iff hv hs0]
  exact fun he ↦ hsum ((mem_pointGroup_pointV_iff hv).2 (Or.inr he.symm))

end Closure

end MilnorAlgDep
