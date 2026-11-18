module

public import MilnorAlgDep.Foundations.AlgIndep
public import MilnorAlgDep.Milnor.Basic
public import MilnorAlgDep.Standard.Differentials.Independence

/-!
# The logarithmic derivative in characteristic zero

Blueprint Lemma 6.3(c) (`lem:W`, with `L_A = L` and `Γ = 0`) and Lemma 2.3 (S2), in the form used
in case (iii) of the proof of Lemma 7.3 (`lem:kprime`).

For a field extension `L / l` of characteristic `0` with `l` relatively algebraically closed in
`L`, the logarithmic derivative `dlog : V_{L|l} → Ω[L⁄l]`, `[a] ↦ da / a`, is an injective
`ℚ`-linear map; algebraically independent elements of `V_{L|l}` have `L`-linearly independent
images, and algebraically dependent elements have proportional images.

## Main definitions

* `MilnorAlgDep.dlog l L : V l L →ₗ[ℚ] Ω[L⁄l]`.

## Main statements

* `dlog_cls`: `dlog [a] = a⁻¹ • d a`.
* `dlog_eq_zero_iff`: `dlog` is injective (Lemma 6.3(c) for `Γ = 0`).
* `linearIndependent_dlog`: algebraically independent elements have linearly independent images.
* `exists_dlog_eq_smul_of_not_vAlgIndep`: if `v ≠ 0` and `v, w` are algebraically dependent, then
  `dlog w ∈ L • dlog v`.

All of this duplicates the logarithmic derivative being built in `MilnorAlgDep/Char0/` (WP-A0).
-/

@[expose] public section

namespace MilnorAlgDep

open VOf KaehlerDifferential

section DLog

variable (l L : Type*) [Field l] [Field L] [Algebra l L]

/-- The logarithmic derivative on units, `a ↦ da / a`, as an additive homomorphism. -/
noncomputable def dlogUnits : Additive Lˣ →+ Ω[L⁄l] where
  toFun a := ((a.toMul : L))⁻¹ • D l L (a.toMul : L)
  map_zero' := by simp
  map_add' a b := by
    have ha := a.toMul.ne_zero
    have hb := b.toMul.ne_zero
    have h1 : ((a.toMul : L) * b.toMul)⁻¹ * a.toMul = (b.toMul : L)⁻¹ := by field_simp
    have h2 : ((a.toMul : L) * b.toMul)⁻¹ * b.toMul = (a.toMul : L)⁻¹ := by field_simp
    rw [toMul_add, Units.val_mul, Derivation.leibniz, smul_add, smul_smul, smul_smul, h1, h2,
      add_comm]

theorem dlogUnits_apply (a : Lˣ) :
    dlogUnits l L (.ofMul a) = ((a : L))⁻¹ • D l L (a : L) :=
  rfl

variable [CharZero L]

/-- Blueprint Lemma 6.3(a) with `L_A = L`: the logarithmic derivative
`dlog : V_{L|l} → Ω[L⁄l]`, `[a] ↦ da / a` (in characteristic `0`). -/
noncomputable def dlog : V l L →ₗ[ℚ] Ω[L⁄l] :=
  VOf.lift (dlogUnits l L) fun a ha ↦ by
    obtain ⟨c, hc⟩ := mem_constUnits.1 ha
    rw [dlogUnits_apply, ← hc, Derivation.map_algebraMap, smul_zero]

variable {l L}

@[simp]
theorem dlog_cls (a : Lˣ) :
    dlog l L (cls (constUnits l L) (.ofMul a)) = ((a : L))⁻¹ • D l L (a : L) :=
  lift_cls _ _ a

/-- If `(N, a)` is a representative of `v`, then `dlog v = (N a)⁻¹ • d a`. -/
theorem dlog_of_nsmul_eq_cls {v : V l L} {N : ℕ} (hN : 0 < N) {a : Lˣ}
    (h : N • v = cls (constUnits l L) (.ofMul a)) :
    dlog l L v = ((N : L) * a)⁻¹ • D l L (a : L) := by
  have hN' : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h' : (N : L) • dlog l L v = ((a : L))⁻¹ • D l L (a : L) := by
    rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, h, dlog_cls]
  rw [mul_inv, ← smul_smul, ← h', smul_smul, inv_mul_cancel₀ hN', one_smul]

theorem kaehler_D_eq_smul_dlog {v : V l L} {N : ℕ} (hN : 0 < N) {a : Lˣ}
    (h : N • v = cls (constUnits l L) (.ofMul a)) :
    D l L (a : L) = ((N : L) * a) • dlog l L v := by
  have hNa : (N : L) * a ≠ 0 := mul_ne_zero (Nat.cast_ne_zero.2 hN.ne') a.ne_zero
  rw [dlog_of_nsmul_eq_cls hN h, smul_smul, mul_inv_cancel₀ hNa, one_smul]

variable [IsRelAlgClosed l L]

/-- Blueprint Lemma 6.3(c) for `Γ = 0`: in characteristic `0`, `dlog : V_{L|l} → Ω[L⁄l]` is
injective, by (S3): `da = 0` implies that `a` is algebraic over `l`. -/
theorem dlog_eq_zero_iff {v : V l L} : dlog l L v = 0 ↔ v = 0 := by
  have := (algebraMap l L).charZero
  refine ⟨fun h0 ↦ ?_, fun h ↦ h ▸ map_zero _⟩
  obtain ⟨N, a, hN, h⟩ := exists_nsmul_eq_cls v
  have hD : D l L (a : L) = 0 := by rw [kaehler_D_eq_smul_dlog hN h, h0, smul_zero]
  have ha : cls (constUnits l L) (.ofMul a) = 0 :=
    (V.cls_eq_zero_iff' a).2 (IsRelAlgClosed.mem_range (kaehler_D_eq_zero_iff_isAlgebraic.1 hD))
  rw [ha, ← smul_zero N] at h
  exact nsmul_left_cancel hN.ne' h

theorem dlog_injective : Function.Injective (dlog l L) :=
  (injective_iff_map_eq_zero _).2 fun _ ↦ dlog_eq_zero_iff.1

omit [IsRelAlgClosed l L] in
/-- Blueprint (S2), characteristic `0`: algebraically independent elements of `V_{L|l}` have
`L`-linearly independent logarithmic derivatives. -/
theorem linearIndependent_dlog {ι : Type*} {v : ι → V l L} (hv : VAlgIndep l v) :
    LinearIndependent L fun i ↦ dlog l L (v i) := by
  have := (algebraMap l L).charZero
  obtain ⟨N, a, hN, ha, hind⟩ := hv
  have hli := linearIndependent_kaehler_D_of_algebraicIndependent hind
  have hw (i : ι) : ((N i : L) * a i)⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero (Nat.cast_ne_zero.2 (hN i).ne') (a i).ne_zero)
  convert hli.units_smul fun i ↦ Units.mk0 _ (hw i) with i
  rw [dlog_of_nsmul_eq_cls (hN i) (ha i), Pi.smul_apply', Units.smul_def, Units.val_mk0]

/-- Blueprint (S2), characteristic `0`: if `v ≠ 0` and `v, w` are algebraically dependent over `l`,
then `dlog w` is an `L`-multiple of `dlog v`. -/
theorem exists_dlog_eq_smul_of_not_vAlgIndep {v w : V l L} (h : ¬ VAlgIndep l ![v, w])
    (hv : v ≠ 0) : ∃ μ : L, dlog l L w = μ • dlog l L v := by
  have := (algebraMap l L).charZero
  obtain ⟨N, a, hN, ha⟩ := exists_nsmul_eq_cls v
  obtain ⟨M, b, hM, hb⟩ := exists_nsmul_eq_cls w
  have hdep : ¬ AlgebraicIndependent l ![(a : L), (b : L)] := by
    rw [VAlgIndep.iff_of_nsmul_eq_cls (N := ![N, M]) (a := ![a, b])
      (fun i ↦ by fin_cases i <;> assumption) (fun i ↦ by fin_cases i <;> assumption)] at h
    convert h using 2
    ext i
    fin_cases i <;> rfl
  rw [algebraicIndependent_iff_linearIndependent_kaehler_D] at hdep
  have hdep' : ¬ LinearIndependent L ![D l L (a : L), D l L (b : L)] := by
    convert hdep using 2
    ext i
    fin_cases i <;> rfl
  rw [LinearIndependent.pair_iff] at hdep'
  push Not at hdep'
  obtain ⟨s, t, hst, hne⟩ := hdep'
  have hDa : D l L (a : L) ≠ 0 := fun h0 ↦
    V.not_mem_range_of_nsmul_eq_cls hv hN ha
      (IsRelAlgClosed.mem_range (kaehler_D_eq_zero_iff_isAlgebraic.1 h0))
  have ht : t ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact hne (hst.resolve_right hDa) rfl
  have hDb : D l L (b : L) = (-(t⁻¹ * s)) • D l L (a : L) := by
    rw [neg_smul, ← smul_smul, ← smul_neg, eq_inv_smul_iff₀ ht, eq_neg_iff_add_eq_zero, add_comm,
      hst]
  refine ⟨((M : L) * b)⁻¹ * (-(t⁻¹ * s)) * ((N : L) * a), ?_⟩
  rw [dlog_of_nsmul_eq_cls hM hb, hDb, kaehler_D_eq_smul_dlog hN ha, smul_smul, smul_smul]

end DLog

end MilnorAlgDep
