module

public import MilnorAlgDep.Char0.PointDeriv
public import MilnorAlgDep.StepB.Abstract

/-!
# The homomorphism `Δ = dlog ∘ ψ` and the field embedding `τ` (characteristic zero)

Blueprint Section 6.3 (`ss:model`) read with `Γ = 0`: `F = L`, `Ω = Ω_{L|l}`, `W = V`, `K₀ = K`,
`Δ = dlog ∘ ψ`, and every `x ∈ K \ k` is primitive. We verify the hypotheses (H0)–(H3) of the
abstract Step B (`MilnorAlgDep.StepBData`, blueprint Lemma 6.5 `lem:K0`) and obtain the ring
homomorphism `τ : K →+* L` of Proposition 6.9 (`prop:tau`).

## Main definitions

* `MilnorAlgDep.Char0Hyp`: the hypotheses (A1)–(A3) of Theorem A, with the two elements of (A3)
  made explicit.
* `MilnorAlgDep.Char0Hyp.ψK`: `ψ` extended to `K` by `ψ 0 = 0`.
* `MilnorAlgDep.Char0Hyp.data`: the `StepBData` with `Δ = dlog ∘ ψ`.
* `MilnorAlgDep.Char0Hyp.τ`: the ring homomorphism `K →+* L` of Proposition 6.9.

## Main statements

* `Char0Hyp.data_Δ_eq_zero_iff`: Lemma 6.5(a) for `Γ = 0`: `x` is primitive iff `x ∉ k`.
* `Char0Hyp.μ_mem_pointV`: Lemma 6.5(b): `μ(x) ∈ Q_x`.
* `Char0Hyp.exists_Δhom_notMem_span`: Lemma 6.5(c), richness (H3), using `x₁ x₂ ^ n`.
* `Char0Hyp.charZero`: `K` has characteristic zero (it embeds into `L` via `τ`).
-/

@[expose] public section

namespace MilnorAlgDep

open VOf KaehlerDifferential Submodule

section LinearAlgebra

variable {F Ω : Type*} [Field F] [AddCommGroup Ω] [Module F Ω]

/-- If `e₁, e₂` are linearly independent, at most one of the vectors `e₁ + n • e₂` (`n ∈ ℕ`) lies
on a given line `F ∙ v` (characteristic `0`). -/
theorem subsingleton_setOf_add_smul_mem_span [CharZero F] {e₁ e₂ : Ω}
    (h : LinearIndependent F ![e₁, e₂]) (v : Ω) :
    {n : ℕ | e₁ + (n : F) • e₂ ∈ F ∙ v}.Subsingleton := by
  intro n hn m hm
  obtain ⟨α, hα⟩ := mem_span_singleton.1 hn
  obtain ⟨β, hβ⟩ := mem_span_singleton.1 hm
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_smul] at hα
    have := (LinearIndependent.pair_iff.1 h 1 n (by rw [one_smul]; exact hα.symm)).1
    exact one_ne_zero this
  have key : (β - α) • e₁ + (β * n - α * m) • e₂ = 0 := by
    have e : β • (α • v) = α • (β • v) := smul_comm β α v
    rw [hα, hβ, smul_add, smul_add, smul_smul, smul_smul] at e
    rw [sub_smul, sub_smul, sub_add_sub_comm, e, sub_self]
  obtain ⟨h₁, h₂⟩ := LinearIndependent.pair_iff.1 h _ _ key
  rw [sub_eq_zero] at h₁
  rw [h₁, ← mul_sub, mul_eq_zero, sub_eq_zero] at h₂
  exact_mod_cast h₂.resolve_left hα0

/-- Blueprint Lemma 6.5(c) (`lem:K0`), linear algebra part, characteristic `0`: if `e₁, e₂` are
linearly independent, then for any three vectors `vᵢ` some `e₁ + n • e₂` avoids the three lines
`F ∙ vᵢ`. -/
theorem exists_add_smul_notMem_span [CharZero F] {e₁ e₂ : Ω}
    (h : LinearIndependent F ![e₁, e₂]) (v₁ v₂ v₃ : Ω) :
    ∃ n : ℕ, e₁ + (n : F) • e₂ ∉ F ∙ v₁ ∧ e₁ + (n : F) • e₂ ∉ F ∙ v₂ ∧
      e₁ + (n : F) • e₂ ∉ F ∙ v₃ := by
  have hfin := ((subsingleton_setOf_add_smul_mem_span h v₁).finite.union
    (subsingleton_setOf_add_smul_mem_span h v₂).finite).union
    (subsingleton_setOf_add_smul_mem_span h v₃).finite
  obtain ⟨n, hn⟩ := hfin.exists_notMem
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hn
  exact ⟨n, hn.1.1, hn.1.2, hn.2⟩

end LinearAlgebra

/-- The hypotheses (A1)–(A3) of Theorem A in the characteristic `0` case, for `ψ : Kˣ → V l L`,
with the two elements `x₁, x₂` of (A3) made explicit. -/
structure Char0Hyp (K l L : Type*) [Field K] [Field l] [Field L] [Algebra l L] where
  /-- The subfield `k ⊆ K`. -/
  k : Subfield K
  /-- The homomorphism `ψ : Kˣ → V_{L|l}`. -/
  ψ : Additive Kˣ →+ V l L
  /-- (A1): `ker ψ = kˣ`. -/
  A1 : ∀ x : Kˣ, ψ (.ofMul x) = 0 ↔ (x : K) ∈ k
  /-- (A2): `ψ x`, `ψ (1 - x)` are algebraically dependent for `x ∉ k`. -/
  A2 : ∀ x y : Kˣ, (x : K) + y = 1 → (x : K) ∉ k → ¬ VAlgIndep l ![ψ (.ofMul x), ψ (.ofMul y)]
  /-- The first element of (A3). -/
  x₁ : Kˣ
  /-- The second element of (A3). -/
  x₂ : Kˣ
  /-- (A3) with `d = 2`: `ψ x₁, ψ x₂` are algebraically independent. -/
  A3 : VAlgIndep l ![ψ (.ofMul x₁), ψ (.ofMul x₂)]

namespace Char0Hyp

variable {K l L : Type*} [Field K] [Field l] [Field L] [Algebra l L] (H : Char0Hyp K l L)

/-! ### `ψ` on `K` -/

open Classical in
/-- `ψ` extended to `K` by `ψ 0 = 0`. -/
noncomputable def ψK (x : K) : V l L :=
  if hx : x = 0 then 0 else H.ψ (.ofMul (Units.mk0 x hx))

theorem ψK_zero : H.ψK 0 = 0 := by
  simp [ψK]

theorem ψK_of_ne_zero {x : K} (hx : x ≠ 0) : H.ψK x = H.ψ (.ofMul (Units.mk0 x hx)) := by
  simp [ψK, hx]

theorem ψK_units (x : Kˣ) : H.ψK x = H.ψ (.ofMul x) := by
  rw [H.ψK_of_ne_zero x.ne_zero, Units.mk0_val]

theorem ψK_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : H.ψK (x * y) = H.ψK x + H.ψK y := by
  rw [H.ψK_of_ne_zero hx, H.ψK_of_ne_zero hy, H.ψK_of_ne_zero (mul_ne_zero hx hy),
    Units.mk0_mul _ _ (mul_ne_zero hx hy), ofMul_mul, map_add]

theorem ψK_eq_zero_iff {x : K} : H.ψK x = 0 ↔ x ∈ H.k := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [ψK_zero, zero_mem]
  · rw [H.ψK_of_ne_zero hx, H.A1, Units.val_mk0]

theorem ψK_ne_zero {x : K} (hx : x ∉ H.k) : H.ψK x ≠ 0 :=
  fun h ↦ hx (H.ψK_eq_zero_iff.1 h)

theorem ne_zero_of_notMem {x : K} (hx : x ∉ H.k) : x ≠ 0 := by
  rintro rfl
  exact hx (zero_mem _)

theorem one_sub_notMem {x : K} (hx : x ∉ H.k) : 1 - x ∉ H.k := fun h ↦
  hx (by simpa using sub_mem (one_mem H.k) h)

theorem x₁_notMem : (H.x₁ : K) ∉ H.k := fun h ↦ H.A3.ne_zero 0 ((H.A1 _).2 h)

theorem x₂_notMem : (H.x₂ : K) ∉ H.k := fun h ↦ H.A3.ne_zero 1 ((H.A1 _).2 h)

/-- (A2) and (V3): for `x ∉ k`, `Q_{1 - x} = Q_x`. -/
theorem pointV_ψK_one_sub [IsRelAlgClosed l L] {x : K} (hx : x ∉ H.k) :
    pointV l (H.ψK (1 - x)) = pointV l (H.ψK x) := by
  have hx0 := H.ne_zero_of_notMem hx
  have h1x0 := H.ne_zero_of_notMem (H.one_sub_notMem hx)
  have hdep := H.A2 (Units.mk0 x hx0) (Units.mk0 (1 - x) h1x0) (by simp) hx
  rw [← H.ψK_of_ne_zero, ← H.ψK_of_ne_zero, vAlgIndep_pair_iff (H.ψK_ne_zero hx)
    (H.ψK_ne_zero (H.one_sub_notMem hx)), not_not] at hdep
  exact hdep.symm

/-! ### The homomorphism `Δ` and the hypotheses (H0)–(H3) -/

variable [CharZero L]

/-- `Δ = dlog ∘ ψ : Kˣ → Ω[L⁄l]` (blueprint Section 6.3 with `Γ = 0`). -/
noncomputable def Δhom : Additive Kˣ →+ Ω[L⁄l] :=
  (dlog l L).comp H.ψ

theorem Δhom_apply (x : Kˣ) : H.Δhom (.ofMul x) = dlog l L (H.ψ (.ofMul x)) :=
  rfl

variable [IsRelAlgClosed l L]

theorem Δhom_eq_zero_iff (x : Kˣ) : H.Δhom (.ofMul x) = 0 ↔ (x : K) ∈ H.k := by
  rw [Δhom_apply, dlog_eq_zero_iff, H.A1]

/-- (H0): `Δ (-1) = 0`. -/
theorem Δhom_neg_one : H.Δhom (.ofMul (-1)) = 0 :=
  (H.Δhom_eq_zero_iff _).2 (by simp)

/-- (H1): `x` is primitive iff `1 - x` is (both mean `∉ k`). -/
theorem Δhom_eq_zero_iff_one_sub (x : Kˣ) (hx : (1 : K) - x ≠ 0) :
    H.Δhom (.ofMul x) = 0 ↔ H.Δhom (.ofMul (Units.mk0 (1 - x) hx)) = 0 := by
  rw [Δhom_eq_zero_iff, Δhom_eq_zero_iff, Units.val_mk0]
  refine ⟨fun h ↦ sub_mem (one_mem _) h, fun h ↦ ?_⟩
  by_contra h'
  exact H.one_sub_notMem h' h

/-- (H2), Blueprint Lemma 6.5(b): `Δ (1 - x) ∈ L ∙ Δ x` for primitive `x`; this is (A2) via
`vAlgIndep_pair_iff_linearIndependent_dlog`. -/
theorem Δhom_one_sub_mem_span (x : Kˣ) (hx : (1 : K) - x ≠ 0) (h : H.Δhom (.ofMul x) ≠ 0) :
    H.Δhom (.ofMul (Units.mk0 (1 - x) hx)) ∈ L ∙ H.Δhom (.ofMul x) := by
  have hxk : (x : K) ∉ H.k := fun hk ↦ h ((H.Δhom_eq_zero_iff x).2 hk)
  have hdep := H.A2 x (Units.mk0 (1 - x) hx) (by simp) hxk
  rw [vAlgIndep_pair_iff_linearIndependent_dlog, ← Δhom_apply, ← Δhom_apply,
    LinearIndependent.pair_iff' h] at hdep
  push Not at hdep
  obtain ⟨c, hc⟩ := hdep
  exact mem_span_singleton.2 ⟨c, hc⟩

omit [IsRelAlgClosed l L] in
/-- Blueprint Lemma 6.5(c): `Δ x₁, Δ x₂` are linearly independent. -/
theorem linearIndependent_Δhom_x :
    LinearIndependent L ![H.Δhom (.ofMul H.x₁), H.Δhom (.ofMul H.x₂)] :=
  vAlgIndep_pair_iff_linearIndependent_dlog.1 H.A3

omit [IsRelAlgClosed l L] in
/-- (H3), Blueprint Lemma 6.5(c) for `Γ = 0`: for any three lines there is `z` (of the form
`x₁ x₂ ^ n`) with `L ∙ Δ z` none of them. -/
theorem exists_Δhom_notMem_span (v₁ v₂ v₃ : Ω[L⁄l]) : ∃ z : Kˣ,
    H.Δhom (.ofMul z) ∉ L ∙ v₁ ∧ H.Δhom (.ofMul z) ∉ L ∙ v₂ ∧ H.Δhom (.ofMul z) ∉ L ∙ v₃ := by
  obtain ⟨n, hn⟩ := exists_add_smul_notMem_span H.linearIndependent_Δhom_x v₁ v₂ v₃
  refine ⟨H.x₁ * H.x₂ ^ n, ?_⟩
  rw [ofMul_mul, ofMul_pow, map_add, map_nsmul, ← Nat.cast_smul_eq_nsmul L]
  exact hn

/-- The data of the abstract Step B for `Δ = dlog ∘ ψ`, with `F = L` and `Ω = Ω[L⁄l]`. -/
noncomputable def data : StepBData K L Ω[L⁄l] :=
  StepBData.ofAddMonoidHom H.Δhom H.Δhom_neg_one H.Δhom_eq_zero_iff_one_sub
    H.Δhom_one_sub_mem_span H.exists_Δhom_notMem_span

theorem data_Δ (x : K) : H.data.Δ x = dlog l L (H.ψK x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [H.data.Δ_zero, ψK_zero, map_zero]
  · rw [data, StepBData.ofAddMonoidHom_Δ_of_ne_zero _ _ _ _ _ hx, Δhom_apply,
      H.ψK_of_ne_zero hx]

/-- Blueprint Lemma 6.5(a) for `Γ = 0`: `x` is primitive if and only if `x ∉ k`. -/
theorem data_Δ_eq_zero_iff {x : K} : H.data.Δ x = 0 ↔ x ∈ H.k := by
  rw [data_Δ, dlog_eq_zero_iff, ψK_eq_zero_iff]

theorem data_Δ_ne_zero {x : K} (hx : x ∉ H.k) : H.data.Δ x ≠ 0 :=
  fun h ↦ hx (H.data_Δ_eq_zero_iff.1 h)

theorem notMem_of_data_Δ_ne_zero {x : K} (hx : H.data.Δ x ≠ 0) : x ∉ H.k :=
  fun h ↦ hx (H.data_Δ_eq_zero_iff.2 h)

/-- `x₁, x₂` are transverse. -/
theorem transverse_x : H.data.Transverse H.x₁ H.x₂ := by
  rw [StepBData.Transverse, data_Δ, data_Δ, ψK_units, ψK_units]
  exact H.linearIndependent_Δhom_x

/-- **Blueprint Lemma 6.5(b)** (`lem:K0`), characteristic `0`: for `x ∉ k`, the scalar `μ(x)`
with `Δ(1 - x) = μ(x) Δ(x)` lies in the point `Q_x`. -/
theorem μ_mem_pointV {x : K} (hx : x ∉ H.k) : H.data.μ x ∈ pointV l (H.ψK x) := by
  obtain ⟨c, hc, he⟩ := exists_mem_pointV_dlog_eq_smul (H.ψK_ne_zero hx) (H.pointV_ψK_one_sub hx)
  rw [H.data.μ_eq_of_Δ_one_sub (H.data_Δ_ne_zero hx) (c := c) (by rw [data_Δ, data_Δ, he])]
  exact hc

/-- **Blueprint Proposition 6.9** (`prop:tau`), characteristic `0`: the ring homomorphism
`τ : K →+* L` with `τ x = μ x / (μ x - 1)` for `x ∉ k`. -/
noncomputable def τ : K →+* L :=
  H.data.τ

/-- `τ x = μ x / (μ x - 1)` for `x ∉ k`. -/
theorem τ_eq_μ_div {x : K} (hx : x ∉ H.k) : H.τ x = H.data.μ x / (H.data.μ x - 1) :=
  H.data.τ_eq_μ_div (H.data_Δ_ne_zero hx)

/-- `μ x = τ x / (τ x - 1)` for `x ∉ k`. -/
theorem μ_eq_τ_div {x : K} (hx : x ∉ H.k) : H.data.μ x = H.τ x / (H.τ x - 1) :=
  H.data.μ_eq_τ_div (H.data_Δ_ne_zero hx)

theorem τ_ne_zero {x : K} (hx : x ≠ 0) : H.τ x ≠ 0 :=
  (map_ne_zero H.τ).2 hx

include H in
/-- `K` has characteristic zero, as it embeds into `L` (end of Proposition 6.9). -/
theorem charZero : CharZero K :=
  RingHom.charZero H.τ

end Char0Hyp

end MilnorAlgDep
