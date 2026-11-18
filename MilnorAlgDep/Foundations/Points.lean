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
* `point_inf_point_eq_bot`: two distinct points intersect in `l`.
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
  sorry

/-- If `a` and `b` are algebraic over each other (over `l`), they define the same point. -/
theorem point_eq_point_of_isAlgebraic {a b : L} (hab : IsAlgebraic l⟮a⟯ b)
    (hba : IsAlgebraic l⟮b⟯ a) : point l a = point l b := by
  sorry

/-- Blueprint 2.1: for `a ∉ l`, an element `b` lies in `Q_a` if and only if `a` and `b` are
algebraically dependent over `l`. -/
theorem mem_point_iff_not_algebraicIndependent {a b : L} (ha : Transcendental l a) :
    b ∈ point l a ↔ ¬ AlgebraicIndependent l ![a, b] := by
  sorry

/-- Blueprint 2.1: for `a, b ∉ l`, `Q_a = Q_b` if and only if `b ∈ Q_a`. -/
theorem point_eq_point_iff_mem {a b : L} (ha : Transcendental l a) (hb : Transcendental l b) :
    point l a = point l b ↔ b ∈ point l a := by
  sorry

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
  sorry

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
  sorry

theorem pointV_cls (a : Lˣ) : pointV l (cls (constUnits l L) (.ofMul a)) = point l (a : L) :=
  pointV_eq_point one_pos (one_nsmul _)

/-- `Q_{q • v} = Q_v` for `q ≠ 0`. -/
theorem pointV_smul {v : V l L} {q : ℚ} (hq : q ≠ 0) : pointV l (q • v) = pointV l v := by
  sorry

theorem pointV_neg (v : V l L) : pointV l (-v) = pointV l v := by
  rw [← neg_one_smul ℚ v, pointV_smul (by norm_num)]

/-- Blueprint (V3): non-zero `v, w ∈ V l L` are algebraically dependent if and only if
`Q_v = Q_w`. -/
theorem vAlgIndep_pair_iff [IsRelAlgClosed l L] {v w : V l L} (hv : v ≠ 0) (hw : w ≠ 0) :
    VAlgIndep l ![v, w] ↔ pointV l v ≠ pointV l w := by
  sorry

end pointV

section pointGroup

/-- Blueprint (V3): for an intermediate field `Q` of `L / l` (typically a point), the subgroup
`G_Q ≤ V l L`, the image of `(Qˣ/lˣ) ⊗ ℚ`: the `ℚ`-span of the classes `[a]` with `a ∈ Qˣ`. -/
noncomputable def pointGroup (Q : IntermediateField l L) : Submodule ℚ (V l L) :=
  Submodule.span ℚ ((fun a : Lˣ ↦ cls (constUnits l L) (.ofMul a)) '' {a | (a : L) ∈ Q})

theorem mem_pointGroup_iff {Q : IntermediateField l L} {v : V l L} :
    v ∈ pointGroup Q ↔ ∃ (N : ℕ) (a : Lˣ), 0 < N ∧ (a : L) ∈ Q ∧
      N • v = cls (constUnits l L) (.ofMul a) := by
  sorry

/-- Blueprint (V3): for a point `Q = Q_b` (`b ∉ l`), `G_Q = {v | v = 0 or Q_v = Q}`. -/
theorem mem_pointGroup_point_iff [IsRelAlgClosed l L] {b : L} (hb : Transcendental l b)
    {v : V l L} : v ∈ pointGroup (point l b) ↔ v = 0 ∨ pointV l v = point l b := by
  sorry

/-- Blueprint (V3): for `v ≠ 0`, `G_{Q_v} = {w | w = 0 or Q_w = Q_v}`. -/
theorem mem_pointGroup_pointV_iff [IsRelAlgClosed l L] {v w : V l L} (hv : v ≠ 0) :
    w ∈ pointGroup (pointV l v) ↔ w = 0 ∨ pointV l w = pointV l v := by
  sorry

theorem mem_pointGroup_pointV (v : V l L) : v ∈ pointGroup (pointV l v) := by
  sorry

end pointGroup

end MilnorAlgDep
