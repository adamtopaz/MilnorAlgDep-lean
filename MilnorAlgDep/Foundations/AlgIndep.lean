module

public import MilnorAlgDep.Foundations.V
public import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# Algebraic independence in `V_{L|l}`

Blueprint, Section 1.1 and (V3) in Section 2.3.

A family `v : ι → V l L` is *algebraically independent over `l`* if there are representatives
`N i ≥ 1`, `a i : Lˣ` with `N i • v i = [a i]` such that the family `a` is algebraically
independent over `l` (in the sense of Mathlib's `AlgebraicIndependent`). This does not depend on
the choice of representatives (`VAlgIndep.iff_of_nsmul_eq_cls`). Elements are *algebraically
dependent* if they are not algebraically independent.

Note that an algebraically independent family consists of non-zero elements
(`VAlgIndep.ne_zero`), and is injective.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

variable {l L : Type*} [Field l] [Field L] [Algebra l L] {ι : Type*}

variable (l) in
/-- Blueprint 1.1 / (V3): a family `v : ι → V l L` is *algebraically independent over `l`* if
for some choice of integers `N i ≥ 1` and units `a i` with `N i • v i = [a i]`, the family
`(a i)` is algebraically independent over `l`.

By `VAlgIndep.iff_of_nsmul_eq_cls` the choice does not matter. Elements are *algebraically
dependent* if they are not algebraically independent (`¬ VAlgIndep l v`). -/
def VAlgIndep (v : ι → V l L) : Prop :=
  ∃ (N : ι → ℕ) (a : ι → Lˣ), (∀ i, 0 < N i) ∧
    (∀ i, N i • v i = cls (constUnits l L) (.ofMul (a i))) ∧
    AlgebraicIndependent l (fun i ↦ (a i : L))

namespace VAlgIndep

/-- Blueprint 1.1: algebraic independence in `V l L` does not depend on the choice of
representatives. -/
theorem iff_of_nsmul_eq_cls {v : ι → V l L} {N : ι → ℕ} {a : ι → Lˣ} (hN : ∀ i, 0 < N i)
    (ha : ∀ i, N i • v i = cls (constUnits l L) (.ofMul (a i))) :
    VAlgIndep l v ↔ AlgebraicIndependent l (fun i ↦ (a i : L)) := by
  sorry

/-- The members of an algebraically independent family are non-zero. -/
theorem ne_zero {v : ι → V l L} (hv : VAlgIndep l v) (i : ι) : v i ≠ 0 := by
  sorry

/-- An algebraically independent family is injective. -/
theorem injective {v : ι → V l L} (hv : VAlgIndep l v) : Function.Injective v := by
  sorry

/-- Algebraic independence of `[a i]` is algebraic independence of `a i`. -/
theorem cls_iff {a : ι → Lˣ} :
    VAlgIndep l (fun i ↦ cls (constUnits l L) (.ofMul (a i))) ↔
      AlgebraicIndependent l (fun i ↦ (a i : L)) :=
  iff_of_nsmul_eq_cls (fun _ ↦ one_pos) (fun _ ↦ one_nsmul _)

/-- Algebraic independence is invariant under multiplying each member by a non-zero rational
number. -/
theorem smul_iff {v : ι → V l L} {q : ι → ℚ} (hq : ∀ i, q i ≠ 0) :
    VAlgIndep l (fun i ↦ q i • v i) ↔ VAlgIndep l v := by
  sorry

/-- Subfamilies of algebraically independent families are algebraically independent. -/
theorem comp {ι' : Type*} {v : ι → V l L} (hv : VAlgIndep l v) (f : ι' → ι)
    (hf : Function.Injective f) : VAlgIndep l (v ∘ f) := by
  sorry

end VAlgIndep

end MilnorAlgDep
