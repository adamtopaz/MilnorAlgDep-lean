module

public import MilnorAlgDep.Foundations.Points
public import Mathlib.Algebra.Ring.Aut
public import Mathlib.FieldTheory.Perfect

/-!
# Integer powers of the Frobenius automorphism

Blueprint, Section 2.2 (`Γ = ℤ`) and the preamble of Section 3.

Let `L` be a perfect field of characteristic `p` (a prime). The blueprint writes `Frob^j`,
`j ∈ Γ = ℤ`, for the powers of the Frobenius automorphism `x ↦ x ^ p` of `L`; here this is
`MilnorAlgDep.frobZ L p j : L ≃+* L`, the `j`-th power of `frobeniusEquiv L p` in the group
`RingAut L`. For `n : ℕ`, `frobZ L p n x = x ^ p ^ n` (`frobZ_natCast_apply`).

If `l ⊆ L` is relatively algebraically closed and `L` is perfect, then `l` is perfect
(`IsRelAlgClosed.perfectField`, blueprint Section 3: "relatively algebraically closed (hence
perfect)"), has characteristic `p` (`IsRelAlgClosed.charP`), and every `frobZ L p j` maps `l` onto
itself (`frobZ_algebraMap_mem_range`).

## Conventions for Sections 3-5

The files `MilnorAlgDep/CharP/*.lean` formalizing Sections 3-5 work with
`{l L : Type*} [Field l] [Field L] [Algebra l L]` and, when the characteristic matters,
`(p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]`. Statements which do
not involve `p` assume `[PerfectField l]` instead when they need it; in the setting above this is
`IsRelAlgClosed.perfectField`.
-/

@[expose] public section

namespace MilnorAlgDep

section frobZ

variable (L : Type*) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L]

/-- Blueprint Section 2.2: `Frob^j` for `j ∈ Γ = ℤ`, the `j`-th power of the Frobenius
automorphism `x ↦ x ^ p` of the perfect field `L` of characteristic `p`. -/
noncomputable def frobZ (j : ℤ) : L ≃+* L :=
  frobeniusEquiv L p ^ j

variable {L}

theorem frobZ_zero_apply (x : L) : frobZ L p 0 x = x := by
  simp [frobZ]

theorem frobZ_add_apply (i j : ℤ) (x : L) : frobZ L p (i + j) x = frobZ L p i (frobZ L p j x) := by
  rw [frobZ, zpow_add, RingAut.mul_apply]
  rfl

theorem frobZ_natCast_apply (n : ℕ) (x : L) : frobZ L p n x = x ^ p ^ n := by
  rw [frobZ, zpow_natCast, ← iterateFrobeniusEquiv_eq_pow, iterateFrobeniusEquiv_def]

theorem frobZ_one_apply (x : L) : frobZ L p 1 x = x ^ p := by
  simpa using frobZ_natCast_apply p 1 x

@[simp]
theorem frobZ_neg_apply_frobZ (j : ℤ) (x : L) : frobZ L p (-j) (frobZ L p j x) = x := by
  rw [← frobZ_add_apply, neg_add_cancel, frobZ_zero_apply]

@[simp]
theorem frobZ_apply_frobZ_neg (j : ℤ) (x : L) : frobZ L p j (frobZ L p (-j) x) = x := by
  rw [← frobZ_add_apply, add_neg_cancel, frobZ_zero_apply]

/-- `Frob^{-n} x` is the `p ^ n`-th root of `x`. -/
theorem frobZ_neg_natCast_pow (n : ℕ) (x : L) : frobZ L p (-n) x ^ p ^ n = x := by
  rw [← frobZ_natCast_apply, frobZ_apply_frobZ_neg]

theorem frobZ_injective (j : ℤ) : Function.Injective (frobZ L p j) :=
  (frobZ L p j).injective

end frobZ

section perfect

variable (l L : Type*) [Field l] [Field L] [Algebra l L]

/-- A relatively algebraically closed subfield of a field of characteristic `p` has
characteristic `p`. -/
theorem IsRelAlgClosed.charP (p : ℕ) [CharP L p] : CharP l p :=
  (Algebra.charP_iff l L p).mpr inferInstance

/-- Blueprint Section 3: a relatively algebraically closed subfield `l` of a perfect field `L` is
perfect. -/
theorem IsRelAlgClosed.perfectField [PerfectField L] [IsRelAlgClosed l L] : PerfectField l := by
  obtain ⟨q, hq⟩ := ExpChar.exists l
  have hqL : ExpChar L q := expChar_of_injective_algebraMap (algebraMap l L).injective q
  have : PerfectRing l q := PerfectRing.ofSurjective l q fun c ↦ ?_
  · exact PerfectRing.toPerfectField l q
  set y := (frobeniusEquiv L q).symm (algebraMap l L c)
  have hy : y ^ q = algebraMap l L c := by
    rw [← frobenius_def, ← coe_frobeniusEquiv, RingEquiv.apply_symm_apply]
  have hq0 : 0 < q := (expChar_pos l q)
  have halg : IsAlgebraic l y := by
    refine IsAlgebraic.of_pow hq0 ?_
    rw [hy]
    exact isAlgebraic_algebraMap c
  obtain ⟨c', hc'⟩ := IsRelAlgClosed.mem_range halg
  refine ⟨c', (algebraMap l L).injective ?_⟩
  rw [frobenius_def, map_pow, hc', hy]

variable {l L} (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]

/-- Every `Frob^j` maps `l` into `l` (`l` is perfect). -/
theorem frobZ_algebraMap_mem_range (j : ℤ) (c : l) :
    frobZ L p j (algebraMap l L c) ∈ (algebraMap l L).range := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · rw [frobZ_natCast_apply]
    exact ⟨c ^ p ^ n, map_pow _ _ _⟩
  · refine IsRelAlgClosed.mem_range (IsAlgebraic.of_pow (pow_pos (Fact.out : p.Prime).pos n) ?_)
    rw [frobZ_neg_natCast_pow]
    exact isAlgebraic_algebraMap c

end perfect

section cls

/-! ### Frobenius on classes -/

open VOf

variable {L : Type*} [Field L]

/-- The Frobenius twist on classes: `[Frob^j y] = p ^ j • [y]`. -/
theorem cls_frobZ (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] (H : Subgroup Lˣ) (j : ℤ)
    (y : Lˣ) : cls H (.ofMul (Units.map ((frobZ L p j : L ≃+* L) : L →* L) y)) =
      ((p : ℚ) ^ j) • cls H (.ofMul y) := by
  have hnat : ∀ (n : ℕ) (z : Lˣ), Units.map ((frobZ L p n : L ≃+* L) : L →* L) z = z ^ p ^ n := by
    intro n z
    ext
    rw [Units.coe_map, Units.val_pow_eq_pow_val]
    exact frobZ_natCast_apply p n (z : L)
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · rw [hnat, cls_pow, zpow_natCast, ← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_pow]
  · set z := Units.map ((frobZ L p (-n) : L ≃+* L) : L →* L) y
    have hz : Units.map ((frobZ L p n : L ≃+* L) : L →* L) z = y := by
      ext
      simp only [z, Units.coe_map, MonoidHom.coe_ofClass, frobZ_apply_frobZ_neg]
    conv_rhs => rw [← hz, hnat, cls_pow]
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, zpow_neg, zpow_natCast, Nat.cast_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hp), one_smul]

end cls

end MilnorAlgDep
