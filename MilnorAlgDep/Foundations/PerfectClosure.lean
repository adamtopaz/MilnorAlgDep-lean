module

public import MilnorAlgDep.Foundations.Points
public import Mathlib.FieldTheory.IsPerfectClosure

/-!
# `V_{L|l}` does not change under perfect closure

Blueprint, Section 1.1 ("The group does not change if `L` and `l` are replaced by their perfect
closures `L^i` and `l^i`") and Section 6.1 ("Also `V_{L|l} = V_{L^i|l^i}`").

Let `M / L` be a field extension of exponential characteristic `p` and `l` a subfield of `L`.
We define `perfectClosureIn l M p`, the subfield of `M` of elements some `p ^ n`-th power of which
lies in (the image of) `l`. When `M` is a perfect closure of `L` (Mathlib's
`IsPerfectClosure (algebraMap L M) p`), this is the blueprint's `l^i`, and the natural map
`V.toPerfectClosure : V l L → V l^i M`, `[a] ↦ [a]`, is a bijection.

## Main definitions

* `MilnorAlgDep.perfectClosureIn l M p : Subfield M`: the blueprint's `l^i`.
* `MilnorAlgDep.V.toPerfectClosure l M p : V l L →ₗ[ℚ] V (perfectClosureIn l M p) M`: the
  comparison map.

## Main statements

* `V.toPerfectClosure_bijective`: the comparison map is bijective when `M` is a perfect closure
  of `L`.
* `perfectClosureIn_isRelAlgClosed`: `l^i` is relatively algebraically closed in `M` if `l` is
  relatively algebraically closed in `L`.
* `V.vAlgIndep_toPerfectClosure_iff`: the comparison map preserves and reflects algebraic
  independence.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

variable {L : Type*} [Field L]

section perfectClosureIn

variable (l : Subfield L) (M : Type*) [Field M] [Algebra L M] (p : ℕ) [ExpChar M p]

omit [ExpChar M p] in
/-- Auxiliary: if `y ^ p ^ n` lies in a subfield `S`, so does `y ^ p ^ m` for `m ≥ n`. -/
private theorem pow_expChar_pow_mem_of_le {S : Subfield M} {y : M} {n m : ℕ}
    (h : y ^ p ^ n ∈ S) (hnm : n ≤ m) : y ^ p ^ m ∈ S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, pow_mul]
  exact S.pow_mem h _

/-- For a field extension `M / L` of exponential characteristic `p` and a subfield `l` of `L`,
the subfield of `M` consisting of the elements `y` such that `y ^ p ^ n` lies in (the image of)
`l` for some `n`. When `M` is a perfect closure of `L`, this is the blueprint's `l^i`, the perfect
closure of `l` inside `M`. -/
def perfectClosureIn : Subfield M where
  carrier := {y | ∃ n : ℕ, y ^ p ^ n ∈ l.map (algebraMap L M)}
  mul_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    refine ⟨n + m, ?_⟩
    rw [mul_pow]
    exact Subfield.mul_mem _ (pow_expChar_pow_mem_of_le M p hx le_self_add)
      (pow_expChar_pow_mem_of_le M p hy le_add_self)
  one_mem' := ⟨0, by rw [one_pow]; exact Subfield.one_mem _⟩
  add_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    refine ⟨n + m, ?_⟩
    rw [add_pow_expChar_pow]
    exact Subfield.add_mem _ (pow_expChar_pow_mem_of_le M p hx le_self_add)
      (pow_expChar_pow_mem_of_le M p hy le_add_self)
  zero_mem' := ⟨0, by rw [zero_pow (by positivity)]; exact Subfield.zero_mem _⟩
  neg_mem' := by
    rintro x ⟨n, hx⟩
    refine ⟨n, ?_⟩
    rw [neg_pow]
    exact Subfield.mul_mem _ (Subfield.pow_mem _ (Subfield.neg_mem _ (Subfield.one_mem _)) _) hx
  inv_mem' := by
    rintro x ⟨n, hx⟩
    exact ⟨n, by rw [inv_pow]; exact Subfield.inv_mem _ hx⟩

variable {l M p} in
theorem mem_perfectClosureIn {y : M} :
    y ∈ perfectClosureIn l M p ↔ ∃ n : ℕ, y ^ p ^ n ∈ l.map (algebraMap L M) :=
  Iff.rfl

theorem algebraMap_mem_perfectClosureIn {x : L} (hx : x ∈ l) :
    algebraMap L M x ∈ perfectClosureIn l M p :=
  ⟨0, by rw [pow_zero, pow_one]; exact Subfield.mem_map.2 ⟨x, hx, rfl⟩⟩

theorem constUnits_le_comap_perfectClosureIn :
    constUnits l L ≤
      (constUnits (perfectClosureIn l M p) M).comap (Units.map (algebraMap L M : L →* M)) := by
  intro a ha
  rw [Subgroup.mem_comap, mem_constUnits_subfield]
  exact algebraMap_mem_perfectClosureIn l M p (mem_constUnits_subfield.1 ha)

/-- Blueprint 6.1: `l^i` is relatively algebraically closed in `L^i` if `l` is relatively
algebraically closed in `L`. -/
theorem perfectClosureIn_isRelAlgClosed [PerfectRing M p] [IsPerfectClosure (algebraMap L M) p]
    (hl : ∀ x : L, IsAlgebraic l x → x ∈ l) :
    ∀ y : M, IsAlgebraic (perfectClosureIn l M p) y → y ∈ perfectClosureIn l M p := by
  sorry

end perfectClosureIn

namespace V

variable (l : Subfield L) (M : Type*) [Field M] [Algebra L M] (p : ℕ) [ExpChar M p]

/-- Blueprint 1.1 / 6.1: the comparison map `V_{L|l} → V_{L^i|l^i}`, `[a] ↦ [a]`, where
`l^i = perfectClosureIn l M p`. It is bijective when `M` is a perfect closure of `L`
(`V.toPerfectClosure_bijective`). -/
noncomputable def toPerfectClosure : V l L →ₗ[ℚ] V (perfectClosureIn l M p) M :=
  VOf.mapRingHom (algebraMap L M) (constUnits_le_comap_perfectClosureIn l M p)

@[simp]
theorem toPerfectClosure_cls (a : Lˣ) :
    toPerfectClosure l M p (cls (constUnits l L) (.ofMul a)) =
      cls (constUnits (perfectClosureIn l M p) M)
        (.ofMul (Units.map (algebraMap L M : L →* M) a)) :=
  mapRingHom_cls _ _ a

/-- Blueprint 1.1 / 6.1: `V_{L|l} = V_{L^i|l^i}`: if `M` is a perfect closure of `L`, the
comparison map `V l L → V l^i M` is bijective. -/
theorem toPerfectClosure_bijective [PerfectRing M p] [IsPerfectClosure (algebraMap L M) p] :
    Function.Bijective (toPerfectClosure l M p) := by
  sorry

/-- The comparison map preserves and reflects algebraic independence. -/
theorem vAlgIndep_toPerfectClosure_iff [PerfectRing M p] [IsPerfectClosure (algebraMap L M) p]
    {ι : Type*} (v : ι → V l L) :
    VAlgIndep (perfectClosureIn l M p) (fun i ↦ toPerfectClosure l M p (v i)) ↔
      VAlgIndep l v := by
  sorry

end V

end MilnorAlgDep
