module

public import MilnorAlgDep.Foundations.AlgIndep
public import MilnorAlgDep.Standard.Differentials.Independence

/-!
# The logarithmic derivative on `V_{L|l}` in characteristic zero

Blueprint Lemma 6.4 (`lem:W`) read with `Γ = 0` (so `L_A = L`, `Ω = Ω_{L|l}`, `W = V`), and the
first sentences of Section 1.3 ("The idea"): the logarithmic derivative is an injective
homomorphism `dlog : V_{L|l} → Ω_{L|l}`, and elements of `V_{L|l}` are algebraically independent
if and only if their logarithmic derivatives are linearly independent over `L`.

## Main definitions

* `MilnorAlgDep.dlogL l a = a⁻¹ • d a ∈ Ω[L⁄l]`, the logarithmic derivative of `a : L`.
* `MilnorAlgDep.dlog : V l L →+ Ω[L⁄l]`, with `dlog [a] = a⁻¹ • d a` (`dlog_cls`).

## Main statements

* `dlog_smul`: `dlog` is `ℚ`-linear, `dlog (q • v) = (q : L) • dlog v`.
* `dlog_of_nsmul_eq_cls`: `dlog v = N⁻¹ • dlogL a` for every representative `(N, a)` of `v`.
* `dlog_eq_zero_iff`, `dlog_injective`: Blueprint Lemma 6.4(c) for `Γ = 0`; uses (V1) and
  `d a = 0 ↔ a` algebraic over `l` (characteristic `0`).
* `vAlgIndep_iff_linearIndependent_dlog`: a family in `V l L` is algebraically independent if and
  only if its image under `dlog` is linearly independent over `L` (characteristic `0`).
-/

@[expose] public section

namespace MilnorAlgDep

open VOf KaehlerDifferential TensorProduct

variable {l L : Type*} [Field l] [Field L] [Algebra l L]

section dlogL

variable (l) in
/-- The logarithmic derivative `dlog a = a⁻¹ • d a` of an element `a : L`, in `Ω[L⁄l]`. -/
noncomputable def dlogL (a : L) : Ω[L⁄l] :=
  a⁻¹ • D l L a

theorem dlogL_def (a : L) : dlogL l a = a⁻¹ • D l L a := rfl

@[simp]
theorem dlogL_one : dlogL l (1 : L) = 0 := by
  simp [dlogL]

theorem dlogL_mul {a b : L} (ha : a ≠ 0) (hb : b ≠ 0) :
    dlogL l (a * b) = dlogL l a + dlogL l b := by
  rw [dlogL, dlogL, dlogL, Derivation.leibniz, smul_add, smul_smul, smul_smul, add_comm]
  congr 2 <;> field_simp

@[simp]
theorem dlogL_algebraMap (c : l) : dlogL l (algebraMap l L c) = 0 := by
  rw [dlogL, Derivation.map_algebraMap, smul_zero]

/-- `D a = a • dlog a` for `a ≠ 0`. -/
theorem D_eq_smul_dlogL {a : L} (ha : a ≠ 0) : D l L a = a • dlogL l a := by
  rw [dlogL, smul_smul, mul_inv_cancel₀ ha, one_smul]

theorem dlogL_eq_zero_iff {a : L} (ha : a ≠ 0) : dlogL l a = 0 ↔ D l L a = 0 := by
  rw [dlogL, smul_eq_zero, or_iff_right (inv_ne_zero ha)]

end dlogL

section dlog

/-- `a ↦ dlog a` as a homomorphism `Lˣ → Ω[L⁄l]` (written multiplicatively). -/
noncomputable def dlogMonoidHom : Lˣ →* Multiplicative Ω[L⁄l] where
  toFun a := Multiplicative.ofAdd (dlogL l (a : L))
  map_one' := by simp
  map_mul' a b := by
    rw [Units.val_mul, dlogL_mul a.ne_zero b.ne_zero, ofAdd_add]

theorem constUnits_le_ker_dlogMonoidHom :
    constUnits l L ≤ (dlogMonoidHom (l := l) (L := L)).ker := by
  rintro _ ⟨c, rfl⟩
  rw [MonoidHom.mem_ker]
  change Multiplicative.ofAdd (dlogL l (algebraMap l L c)) = 1
  rw [dlogL_algebraMap, ofAdd_zero]

/-- `dlog` on `Lˣ ⧸ lˣ`, as an additive homomorphism. -/
noncomputable def dlogQuot : Additive (Lˣ ⧸ constUnits l L) →+ Ω[L⁄l] :=
  MonoidHom.toAdditiveLeft (QuotientGroup.lift _ dlogMonoidHom constUnits_le_ker_dlogMonoidHom)

theorem dlogQuot_mk (a : Lˣ) :
    dlogQuot (Additive.ofMul (QuotientGroup.mk a : Lˣ ⧸ constUnits l L)) = dlogL l (a : L) :=
  rfl

variable [CharZero L]

/-- The `ℤ`-bilinear map `ℚ × (Lˣ ⧸ lˣ) → Ω[L⁄l]`, `(q, a) ↦ q • dlog a`. -/
noncomputable def dlogBilin :
    ℚ →ₗ[ℤ] Additive (Lˣ ⧸ constUnits l L) →ₗ[ℤ] Ω[L⁄l] :=
  LinearMap.mk₂ ℤ (fun (q : ℚ) m ↦ (q : L) • dlogQuot m)
    (fun q q' m ↦ by rw [Rat.cast_add, add_smul])
    (fun n q m ↦ by rw [zsmul_eq_mul, Rat.cast_mul, Rat.cast_intCast, mul_smul,
      Int.cast_smul_eq_zsmul])
    (fun q m m' ↦ by rw [map_add, smul_add])
    (fun n q m ↦ by rw [map_zsmul, smul_comm])

/-- `dlog` on `ℚ ⊗[ℤ] (Lˣ ⧸ lˣ)`, as a `ℤ`-linear map. -/
noncomputable def dlogTensor : ℚ ⊗[ℤ] Additive (Lˣ ⧸ constUnits l L) →ₗ[ℤ] Ω[L⁄l] :=
  TensorProduct.lift dlogBilin

theorem dlogTensor_tmul (q : ℚ) (m : Additive (Lˣ ⧸ constUnits l L)) :
    dlogTensor (q ⊗ₜ[ℤ] m) = (q : L) • dlogQuot m :=
  TensorProduct.lift.tmul _ _

theorem dlogTensor_smul (q : ℚ) (v : ℚ ⊗[ℤ] Additive (Lˣ ⧸ constUnits l L)) :
    dlogTensor (q • v) = (q : L) • dlogTensor (l := l) v := by
  induction v using TensorProduct.inductionOn with
  | tmul r m =>
    rw [TensorProduct.smul_tmul', dlogTensor_tmul, dlogTensor_tmul, smul_eq_mul, Rat.cast_mul,
      mul_smul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

variable (l L) in
/-- **Blueprint Lemma 6.4(a)** (`lem:W`), characteristic `0`: the logarithmic derivative
`dlog : V_{L|l} → Ω_{L|l}`, the additive homomorphism with `dlog [a] = a⁻¹ • d a`
(`dlog_cls`). It is `ℚ`-linear (`dlog_smul`) and, with `l` relatively algebraically closed,
injective (`dlog_injective`). -/
noncomputable def dlog : V l L →+ Ω[L⁄l] :=
  (dlogTensor (l := l) (L := L)).toAddMonoidHom

@[simp]
theorem dlog_cls (a : Lˣ) : dlog l L (cls (constUnits l L) (.ofMul a)) = dlogL l (a : L) := by
  have : dlog l L (cls (constUnits l L) (.ofMul a)) =
      dlogTensor ((1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul (QuotientGroup.mk a : Lˣ ⧸ constUnits l L)) :=
    rfl
  rw [this, dlogTensor_tmul, Rat.cast_one, one_smul, dlogQuot_mk]

/-- `dlog` is `ℚ`-linear. -/
theorem dlog_smul (q : ℚ) (v : V l L) : dlog l L (q • v) = (q : L) • dlog l L v :=
  dlogTensor_smul q v

theorem dlog_nsmul (n : ℕ) (v : V l L) : dlog l L (n • v) = (n : L) • dlog l L v := by
  rw [map_nsmul, Nat.cast_smul_eq_nsmul]

/-- `dlog v = N⁻¹ • dlog a` for every representative `(N, a)` of `v` (`N • v = [a]`). -/
theorem dlog_of_nsmul_eq_cls {v : V l L} {N : ℕ} {a : Lˣ} (hN : 0 < N)
    (h : N • v = cls (constUnits l L) (.ofMul a)) :
    dlog l L v = (N : L)⁻¹ • dlogL l (a : L) := by
  have hN' : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  rw [← dlog_cls, ← h, dlog_nsmul, inv_smul_smul₀ hN']

/-- In characteristic `0`, `dlog a = 0` if and only if `a` is algebraic over `l`. -/
theorem dlogL_eq_zero_iff_isAlgebraic {a : L} (ha : a ≠ 0) :
    dlogL l a = 0 ↔ IsAlgebraic l a := by
  have : CharZero l := (algebraMap l L).charZero
  rw [dlogL_eq_zero_iff ha, kaehler_D_eq_zero_iff_isAlgebraic]

/-- **Blueprint Lemma 6.4(c)** (`lem:W`) for `Γ = 0`: `dlog v = 0` only for `v = 0`, by (V1) and
`d a = 0 ↔ a` algebraic over `l`. -/
theorem dlog_eq_zero_iff [IsRelAlgClosed l L] {v : V l L} : dlog l L v = 0 ↔ v = 0 := by
  obtain ⟨N, a, hN, h⟩ := exists_nsmul_eq_cls v
  rw [dlog_of_nsmul_eq_cls hN h, smul_eq_zero,
    or_iff_right (inv_ne_zero (Nat.cast_ne_zero.2 hN.ne')),
    dlogL_eq_zero_iff_isAlgebraic a.ne_zero]
  constructor
  · intro halg
    have h0 : cls (constUnits l L) (.ofMul a) = 0 :=
      (V.cls_eq_zero_iff' a).2 (IsRelAlgClosed.mem_range halg)
    exact nsmul_left_cancel hN.ne' (by rw [h, h0, smul_zero])
  · rintro rfl
    rw [smul_zero] at h
    exact V.isAlgebraic_of_cls_eq_zero h.symm

/-- **Blueprint Lemma 6.4(c)** (`lem:W`) for `Γ = 0`: `dlog` is injective. -/
theorem dlog_injective [IsRelAlgClosed l L] : Function.Injective (dlog l L) :=
  (injective_iff_map_eq_zero (dlog l L)).2 fun _ hv ↦ dlog_eq_zero_iff.1 hv

/-- Characteristic `0`: a family `v` in `V l L` is algebraically independent over `l` if and
only if the family `dlog ∘ v` is linearly independent over `L` (blueprint Section 1.3 and the
remark on formalization; this combines (V3) with Lemma 2.3 (S2) and Lemma 4.6). -/
theorem vAlgIndep_iff_linearIndependent_dlog {ι : Type*} {v : ι → V l L} :
    VAlgIndep l v ↔ LinearIndependent L fun i ↦ dlog l L (v i) := by
  have : CharZero l := (algebraMap l L).charZero
  rw [VAlgIndep.iff_of_nsmul_eq_cls (fun i ↦ repNat_pos (v i)) (fun i ↦ repNat_nsmul (v i)),
    algebraicIndependent_iff_linearIndependent_kaehler_D (E := L)]
  have hN (i : ι) : (repNat (v i) : L) ≠ 0 := Nat.cast_ne_zero.2 (repNat_pos (v i)).ne'
  let w : ι → Lˣ := fun i ↦ Units.mk0 ((repNat (v i) : L)⁻¹ * ((repUnit (v i) : Lˣ) : L)⁻¹)
    (mul_ne_zero (inv_ne_zero (hN i)) (inv_ne_zero (repUnit (v i)).ne_zero))
  have hw : (fun i ↦ dlog l L (v i)) = w • fun i ↦ D l L ((repUnit (v i) : Lˣ) : L) := by
    ext i
    rw [dlog_of_nsmul_eq_cls (repNat_pos _) (repNat_nsmul _), dlogL, Pi.smul_apply',
      Units.smul_def, Units.val_mk0, mul_smul]
  rw [hw, LinearIndependent.units_smul_iff]

/-- Characteristic `0`: `v, w` are algebraically independent over `l` if and only if
`dlog v, dlog w` are linearly independent over `L`. -/
theorem vAlgIndep_pair_iff_linearIndependent_dlog {v w : V l L} :
    VAlgIndep l ![v, w] ↔ LinearIndependent L ![dlog l L v, dlog l L w] := by
  have : (fun i ↦ dlog l L (![v, w] i)) = ![dlog l L v, dlog l L w] := by
    ext i
    fin_cases i <;> rfl
  rw [vAlgIndep_iff_linearIndependent_dlog, this]

end dlog

end MilnorAlgDep
