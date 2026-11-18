module

public import MilnorAlgDep.Foundations.VOf
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# The group `V_{L|l}`

Blueprint, Section 1.1 and Section 2.3 ((V1), (V2)).

For a field extension `L / l` let `constUnits l L ≤ Lˣ` be the image of `lˣ`, and
`V l L = VOf (constUnits l L) = ℚ ⊗[ℤ] Additive (Lˣ ⧸ lˣ)`, the blueprint's
`V_{L|l} = (L^×/l^×) ⊗ ℚ`.

## Main definitions

* `MilnorAlgDep.constUnits l L : Subgroup Lˣ`: the image of `lˣ` in `Lˣ`.
* `MilnorAlgDep.V l L`: the `ℚ`-vector space `V_{L|l}`.
* `MilnorAlgDep.IsRelAlgClosed l L`: `l` is relatively algebraically closed in `L`, i.e. every
  element of `L` algebraic over `l` lies in (the image of) `l`.

## Main statements

* `V.cls_eq_zero_iff` (V1): if `l` is relatively algebraically closed in `L`, then `[a] = 0` in
  `V l L` if and only if `a ∈ lˣ`.
* `V.exists_rep` (V2): every `v ≠ 0` has a representative `(N, a)`, `N ≥ 1`, `a ∉ l`,
  `N • v = [a]`; `V.exists_rep_coprime`: if `L` is perfect, `N` can be taken prime to the
  characteristic exponent.
* `V.rep_unique` (V2): two representatives `(N, a)`, `(N', a')` of the same element satisfy
  `a ^ N' = c * a' ^ N` with `c ∈ l`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

section Defs

variable (l L : Type*) [Field l] [Field L] [Algebra l L]

/-- The subgroup of `Lˣ` of non-zero constants: the image of `lˣ` under `algebraMap l L`. -/
def constUnits : Subgroup Lˣ :=
  (Units.map (algebraMap l L : l →* L)).range

/-- Blueprint 1.1: the group `V_{L|l} = (L^×/l^×) ⊗ ℚ`, a `ℚ`-vector space written additively.
The class of `a : Lˣ` is `〚a〛 = VOf.cls _ (Additive.ofMul a)`. -/
abbrev V : Type _ :=
  VOf (constUnits l L)

/-- `l` is *relatively algebraically closed* in `L`: every element of `L` which is algebraic over
`l` lies in (the image of) `l`. (For `l : Subfield L` see `isRelAlgClosed_subfield_iff`.) -/
class IsRelAlgClosed : Prop where
  mem_range_of_isAlgebraic : ∀ x : L, IsAlgebraic l x → x ∈ (algebraMap l L).range

end Defs

variable {l L : Type*} [Field l] [Field L] [Algebra l L]

theorem mem_constUnits {a : Lˣ} : a ∈ constUnits l L ↔ (a : L) ∈ (algebraMap l L).range := by
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, rfl⟩
  · rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      rw [map_zero] at hc
      exact a.ne_zero hc.symm
    refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
    simpa using hc

theorem mem_constUnits_subfield {l : Subfield L} {a : Lˣ} :
    a ∈ constUnits l L ↔ (a : L) ∈ l := by
  rw [mem_constUnits]
  exact ⟨fun ⟨c, hc⟩ ↦ hc ▸ c.2, fun h ↦ ⟨⟨a, h⟩, rfl⟩⟩

/-- A ring homomorphism `τ : K →+* L` with `τ(k) ⊆ l` maps `kˣ` into `lˣ`. -/
theorem constUnits_le_comap {K : Type*} [Field K] {k : Subfield K} {l : Subfield L}
    {τ : K →+* L} (h : ∀ x ∈ k, τ x ∈ l) :
    constUnits k K ≤ (constUnits l L).comap (Units.map (τ : K →* L)) := by
  intro a ha
  rw [Subgroup.mem_comap, mem_constUnits_subfield]
  exact h _ (mem_constUnits_subfield.1 ha)

theorem isRelAlgClosed_subfield_iff {l : Subfield L} :
    IsRelAlgClosed l L ↔ ∀ x : L, IsAlgebraic l x → x ∈ l := by
  constructor
  · intro h x hx
    obtain ⟨c, hc⟩ := h.mem_range_of_isAlgebraic x hx
    exact hc ▸ c.2
  · intro h
    exact ⟨fun x hx ↦ ⟨⟨x, h x hx⟩, rfl⟩⟩

theorem IsRelAlgClosed.of_subfield {l : Subfield L} (h : ∀ x : L, IsAlgebraic l x → x ∈ l) :
    IsRelAlgClosed l L :=
  isRelAlgClosed_subfield_iff.2 h

theorem IsRelAlgClosed.mem_range [IsRelAlgClosed l L] {x : L} (hx : IsAlgebraic l x) :
    x ∈ (algebraMap l L).range :=
  IsRelAlgClosed.mem_range_of_isAlgebraic x hx

/-- If `l` is relatively algebraically closed in `L`, an element of `L` not in `l` is
transcendental over `l`. -/
theorem IsRelAlgClosed.transcendental [IsRelAlgClosed l L] {x : L}
    (hx : x ∉ (algebraMap l L).range) : Transcendental l x :=
  fun h ↦ hx (IsRelAlgClosed.mem_range h)

theorem transcendental_iff_not_mem_range [IsRelAlgClosed l L] {x : L} :
    Transcendental l x ↔ x ∉ (algebraMap l L).range := by
  refine ⟨fun h hx ↦ ?_, IsRelAlgClosed.transcendental⟩
  obtain ⟨c, rfl⟩ := hx
  exact h (isAlgebraic_algebraMap c)

namespace V

/-- If `a ^ n` is constant for some `n ≥ 1`, then `a` is algebraic over `l`. -/
theorem isAlgebraic_of_pow_mem {a : Lˣ} {n : ℕ} (hn : 0 < n) (ha : a ^ n ∈ constUnits l L) :
    IsAlgebraic l (a : L) := by
  rw [mem_constUnits, Units.val_pow_eq_pow_val] at ha
  obtain ⟨c, hc⟩ := ha
  exact IsAlgebraic.of_pow hn (hc ▸ isAlgebraic_algebraMap c)

/-- `[a] = 0` in `V l L` implies that `a` is algebraic over `l` (no assumption on `l`). -/
theorem isAlgebraic_of_cls_eq_zero {a : Lˣ} (ha : cls (constUnits l L) (.ofMul a) = 0) :
    IsAlgebraic l (a : L) := by
  obtain ⟨n, hn, h⟩ := (VOf.cls_eq_zero_iff a).1 ha
  exact isAlgebraic_of_pow_mem hn h

/-- Blueprint (V1): if `l` is relatively algebraically closed in `L`, then `[a] = 0` in `V l L`
if and only if `a ∈ lˣ` (because `Lˣ / lˣ` is torsion-free). -/
theorem cls_eq_zero_iff [IsRelAlgClosed l L] (a : Lˣ) :
    cls (constUnits l L) (.ofMul a) = 0 ↔ a ∈ constUnits l L := by
  refine ⟨fun h ↦ ?_, cls_eq_zero_of_mem⟩
  rw [mem_constUnits]
  exact IsRelAlgClosed.mem_range (isAlgebraic_of_cls_eq_zero h)

/-- Blueprint (V1), in terms of elements of `L`. -/
theorem cls_eq_zero_iff' [IsRelAlgClosed l L] (a : Lˣ) :
    cls (constUnits l L) (.ofMul a) = 0 ↔ (a : L) ∈ (algebraMap l L).range := by
  rw [cls_eq_zero_iff, mem_constUnits]

/-- If `N • v = [a]` with `N ≥ 1` and `v ≠ 0`, then `a` is not constant. -/
theorem not_mem_range_of_nsmul_eq_cls {v : V l L} (hv : v ≠ 0) {N : ℕ} (hN : 0 < N) {a : Lˣ}
    (h : N • v = cls (constUnits l L) (.ofMul a)) : (a : L) ∉ (algebraMap l L).range := by
  intro ha
  rw [← mem_constUnits] at ha
  rw [cls_eq_zero_of_mem ha, ← Nat.cast_smul_eq_nsmul ℚ, smul_eq_zero] at h
  rcases h with h | h
  · exact hN.ne' (by exact_mod_cast h)
  · exact hv h

/-- Blueprint (V2): every non-zero `v ∈ V l L` has a *representative*: a pair `(N, a)` with
`N ≥ 1` an integer and `a ∈ L \ l` such that `N • v = [a]`. -/
theorem exists_rep {v : V l L} (hv : v ≠ 0) :
    ∃ (N : ℕ) (a : Lˣ), 0 < N ∧ (a : L) ∉ (algebraMap l L).range ∧
      N • v = cls (constUnits l L) (.ofMul a) := by
  obtain ⟨N, a, hN, h⟩ := exists_nsmul_eq_cls v
  exact ⟨N, a, hN, not_mem_range_of_nsmul_eq_cls hv hN h, h⟩

/-- Blueprint (V2), perfect case: if `L` is perfect, every non-zero `v ∈ V l L` has a
representative `(N, a)` with `N` prime to the characteristic exponent of `L`. -/
theorem exists_rep_coprime [PerfectField L] {v : V l L} (hv : v ≠ 0) :
    ∃ (N : ℕ) (a : Lˣ), 0 < N ∧ N.Coprime (ringExpChar L) ∧ (a : L) ∉ (algebraMap l L).range ∧
      N • v = cls (constUnits l L) (.ofMul a) := by
  obtain ⟨n, b, hn, hb⟩ := exists_nsmul_eq_cls v
  rcases expChar_is_prime_or_one L (ringExpChar L) with hprime | hone
  · set p := ringExpChar L
    obtain ⟨j, m, hndvd, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hprime.one_lt.ne'
    have hm : 0 < m := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hn
    let c : Lˣ := Units.map ((iterateFrobeniusEquiv L p j).symm : L →* L) b
    have hc : c ^ (p ^ j) = b := by
      ext
      rw [Units.val_pow_eq_pow_val]
      change ((iterateFrobeniusEquiv L p j).symm b) ^ p ^ j = b
      rw [← iterateFrobenius_def, ← coe_iterateFrobeniusEquiv, RingEquiv.apply_symm_apply]
    have key : m • v = cls (constUnits l L) (.ofMul c) := by
      refine nsmul_left_cancel (pow_ne_zero j hprime.ne_zero) ?_
      rw [← cls_pow, hc, ← hb, smul_smul]
    refine ⟨m, c, hm, ?_, not_mem_range_of_nsmul_eq_cls hv hm key, key⟩
    exact Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hprime).2 hndvd)
  · refine ⟨n, b, hn, ?_, not_mem_range_of_nsmul_eq_cls hv hn hb, hb⟩
    rw [hone]
    exact Nat.coprime_one_right n

/-- Blueprint (V2): if `l` is relatively algebraically closed in `L` and `(N, a)`, `(N', a')`
are representatives of the same element (`N • v = [a]`, `N' • v = [a']`), then
`a ^ N' = c * a' ^ N` for some `c ∈ l`. -/
theorem rep_unique [IsRelAlgClosed l L] {v : V l L} {N N' : ℕ} {a a' : Lˣ}
    (h : N • v = cls (constUnits l L) (.ofMul a))
    (h' : N' • v = cls (constUnits l L) (.ofMul a')) :
    ∃ c : l, (a : L) ^ N' = algebraMap l L c * (a' : L) ^ N := by
  have key : cls (constUnits l L) (.ofMul (a ^ N' / a' ^ N)) = 0 := by
    rw [cls_div, cls_pow, cls_pow, ← h, ← h', smul_smul, smul_smul, mul_comm, sub_self]
  obtain ⟨c, hc⟩ := (cls_eq_zero_iff' _).1 key
  refine ⟨c, ?_⟩
  rw [hc, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val,
    div_mul_cancel₀ _ (pow_ne_zero _ a'.ne_zero)]

end V

end MilnorAlgDep
