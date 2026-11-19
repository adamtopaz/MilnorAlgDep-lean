module

public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Abstract Step B: the functions `μ` and `t`

This file formalizes the first half of Step B of the blueprint
(`blueprint/milnor-k-fields.tex`, Section 6.4, "Step B: the functions `μ` and `t`") in an
abstract setting.

In the blueprint, Step B is carried out for the specific homomorphism
`Δ = dlog_A ∘ ψ : K₀ˣ → Ω` of Section 6.3. The argument only uses the following properties of
`Δ`, which we take as hypotheses (structure `MilnorAlgDep.StepBData`):

* `Δ` is a homomorphism from the multiplicative group of a field `K` to an `F`-vector space `Ω`;
* (H0) `Δ (-1) = 0`;
* (H1) for `x ≠ 0, 1`: `Δ x = 0 ↔ Δ (1 - x) = 0`;
* (H2) for `x ≠ 0, 1` with `Δ x ≠ 0`: `Δ (1 - x) ∈ F ∙ Δ x`;
* (H3) for any `v₁ v₂ v₃ : Ω` there is `z` with `Δ z ∉ F ∙ vᵢ` for `i = 1, 2, 3`.

In the blueprint, (H1) and (H2) are Lemma 6.5(b) (`lem:K0`) together with `Δ = 0` on `kˣ`,
(H3) is Lemma 6.5(c), and (H0) holds because `ψ (-1) = 0`.

## Main definitions and results

* `MilnorAlgDep.StepBData`: the hypotheses.
* `MilnorAlgDep.StepBData.μ`: the function with `Δ (1 - x) = μ x • Δ x` for primitive `x`.
* `MilnorAlgDep.StepBData.t`: `t x = μ x / (μ x - 1)`.
* `MilnorAlgDep.StepBData.Transverse`: `Δ x, Δ y` are linearly independent.
* Blueprint Lemma 6.6 (`lem:onevar`): `μ_one_sub`, `μ_inv`, `μ_ne_one`, `t_one_sub`, `t_inv`.
* Blueprint Lemma 6.7 (`lem:twovar`): `Transverse.t_mul`.

The field embedding (Lemma 6.8, Proposition 6.9) is in `MilnorAlgDep.StepB.Abstract`.

## Implementation notes

`Δ` is a total function `K → Ω` which is multiplicative-to-additive on non-zero elements and
satisfies `Δ 0 = 0`. This avoids coercions between `Kˣ` and `K` in an argument that constantly
passes between `x`, `1 - x` and `x + y`. The normalisation `Δ 0 = 0` makes "`x` is primitive"
simply `Δ x ≠ 0`, which then implies `x ≠ 0` and `x ≠ 1`. A constructor from a bundled
`Additive Kˣ →+ Ω` is `MilnorAlgDep.StepBData.ofAddMonoidHom`.
-/

@[expose] public section

namespace MilnorAlgDep

open Submodule

/-- The hypotheses of the abstract Step B (blueprint Sections 6.3–6.5).

`Δ : K → Ω` is a homomorphism from `Kˣ` to the `F`-vector space `Ω`, extended by `Δ 0 = 0`.
An element `x` is *primitive* if `Δ x ≠ 0`. The fields `Δ_neg_one`, `Δ_eq_zero_iff_one_sub`,
`Δ_one_sub_mem_span` and `exists_Δ_notMem_span` are the hypotheses (H0)–(H3) of the module
docstring; in the blueprint they come from Lemma 6.5 (`lem:K0`). -/
structure StepBData (K F Ω : Type*) [Field K] [Field F] [AddCommGroup Ω] [Module F Ω] where
  /-- The homomorphism `Δ`, extended to `K` by `Δ 0 = 0`. -/
  Δ : K → Ω
  /-- Normalisation of the irrelevant value at `0`. -/
  Δ_zero : Δ 0 = 0
  /-- `Δ` is a homomorphism `Kˣ → Ω`. -/
  Δ_mul : ∀ x y, x ≠ 0 → y ≠ 0 → Δ (x * y) = Δ x + Δ y
  /-- (H0): `Δ (-1) = 0`. -/
  Δ_neg_one : Δ (-1) = 0
  /-- (H1): `x` is primitive if and only if `1 - x` is. -/
  Δ_eq_zero_iff_one_sub : ∀ x, x ≠ 0 → x ≠ 1 → (Δ x = 0 ↔ Δ (1 - x) = 0)
  /-- (H2): `Δ (1 - x)` is proportional to `Δ x` for primitive `x`. -/
  Δ_one_sub_mem_span : ∀ x, x ≠ 0 → x ≠ 1 → Δ x ≠ 0 → Δ (1 - x) ∈ F ∙ Δ x
  /-- (H3): for any three vectors `vᵢ` there is `z` with `Δ z ∉ F ∙ vᵢ`. In particular `z` is
  primitive, and `F ∙ Δ z` is different from any of the `F ∙ vᵢ` which are lines. -/
  exists_Δ_notMem_span : ∀ v₁ v₂ v₃ : Ω, ∃ z, Δ z ∉ F ∙ v₁ ∧ Δ z ∉ F ∙ v₂ ∧ Δ z ∉ F ∙ v₃

namespace StepBData

variable {K F Ω : Type*} [Field K] [Field F] [AddCommGroup Ω] [Module F Ω]
variable (D : StepBData K F Ω) {x y z : K}

/-! ### Elementary properties of `Δ` -/

@[simp]
lemma Δ_one : D.Δ 1 = 0 := by
  simpa using D.Δ_mul 1 1 one_ne_zero one_ne_zero

lemma ne_zero_of_Δ_ne_zero (h : D.Δ x ≠ 0) : x ≠ 0 := by
  rintro rfl
  exact h D.Δ_zero

lemma ne_one_of_Δ_ne_zero (h : D.Δ x ≠ 0) : x ≠ 1 := by
  rintro rfl
  exact h D.Δ_one

lemma one_sub_ne_zero_of_Δ_ne_zero (h : D.Δ x ≠ 0) : 1 - x ≠ 0 :=
  sub_ne_zero.2 (D.ne_one_of_Δ_ne_zero h).symm

lemma Δ_inv (hx : x ≠ 0) : D.Δ x⁻¹ = -D.Δ x := by
  have := D.Δ_mul x x⁻¹ hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, Δ_one] at this
  exact eq_neg_of_add_eq_zero_right this.symm

lemma Δ_div (hx : x ≠ 0) (hy : y ≠ 0) : D.Δ (x / y) = D.Δ x - D.Δ y := by
  rw [div_eq_mul_inv, D.Δ_mul _ _ hx (inv_ne_zero hy), D.Δ_inv hy, sub_eq_add_neg]

@[simp]
lemma Δ_neg (x : K) : D.Δ (-x) = D.Δ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [neg_eq_neg_one_mul, D.Δ_mul _ _ (neg_ne_zero.2 one_ne_zero) hx, D.Δ_neg_one, zero_add]

lemma Δ_mul_of_Δ_eq_zero (hx0 : x ≠ 0) (hx : D.Δ x = 0) (hz0 : z ≠ 0) :
    D.Δ (x * z) = D.Δ z := by
  rw [D.Δ_mul _ _ hx0 hz0, hx, zero_add]

/-- (H1) for primitive elements: if `x` is primitive, so is `1 - x`. -/
lemma Δ_one_sub_ne_zero (h : D.Δ x ≠ 0) : D.Δ (1 - x) ≠ 0 := fun h' ↦
  h ((D.Δ_eq_zero_iff_one_sub x (D.ne_zero_of_Δ_ne_zero h) (D.ne_one_of_Δ_ne_zero h)).2 h')

/-! ### The function `μ` -/

lemma exists_smul_eq_Δ_one_sub (h : D.Δ x ≠ 0) : ∃ c : F, c • D.Δ x = D.Δ (1 - x) :=
  mem_span_singleton.1 <|
    D.Δ_one_sub_mem_span x (D.ne_zero_of_Δ_ne_zero h) (D.ne_one_of_Δ_ne_zero h) h

open Classical in
/-- The function `μ` of blueprint Lemma 6.5(b): for primitive `x`, `μ x` is the unique scalar
with `Δ (1 - x) = μ x • Δ x`. (Its value at non-primitive `x` is `0` and is irrelevant.) -/
noncomputable def μ (x : K) : F :=
  if h : D.Δ x = 0 then 0 else (D.exists_smul_eq_Δ_one_sub h).choose

lemma μ_of_Δ_eq_zero (h : D.Δ x = 0) : D.μ x = 0 := by
  simp [μ, h]

lemma Δ_one_sub (h : D.Δ x ≠ 0) : D.Δ (1 - x) = D.μ x • D.Δ x := by
  classical
  simp only [μ, h, dite_false]
  exact (D.exists_smul_eq_Δ_one_sub h).choose_spec.symm

lemma μ_eq_of_Δ_one_sub (h : D.Δ x ≠ 0) {c : F} (hc : D.Δ (1 - x) = c • D.Δ x) : D.μ x = c :=
  (smul_left_inj h).1 ((D.Δ_one_sub h).symm.trans hc)

lemma μ_ne_zero (h : D.Δ x ≠ 0) : D.μ x ≠ 0 := by
  intro h0
  apply D.Δ_one_sub_ne_zero h
  rw [D.Δ_one_sub h, h0, zero_smul]

/-- Blueprint Lemma 6.6 (`lem:onevar`), first formula: `μ (1 - x) = μ x⁻¹`. -/
lemma μ_one_sub (h : D.Δ x ≠ 0) : D.μ (1 - x) = (D.μ x)⁻¹ := by
  have h' := D.Δ_one_sub_ne_zero h
  have key : D.Δ x = (D.μ (1 - x) * D.μ x) • D.Δ x := by
    conv_lhs => rw [← sub_sub_cancel 1 x]
    rw [D.Δ_one_sub h', D.Δ_one_sub h, smul_smul]
  have : D.μ (1 - x) * D.μ x = 1 := ((smul_left_inj h).1 (key.symm.trans (one_smul F _).symm))
  exact eq_inv_of_mul_eq_one_left this

/-- Blueprint Lemma 6.6 (`lem:onevar`), second formula: `μ (1 / x) = 1 - μ x`. -/
lemma μ_inv (h : D.Δ x ≠ 0) : D.μ x⁻¹ = 1 - D.μ x := by
  have hx0 := D.ne_zero_of_Δ_ne_zero h
  have h1x := D.one_sub_ne_zero_of_Δ_ne_zero h
  have hinv : D.Δ x⁻¹ ≠ 0 := by rwa [D.Δ_inv hx0, neg_ne_zero]
  have e : 1 - x⁻¹ = -((1 - x) / x) := by field_simp; ring
  have key : (-D.μ x⁻¹) • D.Δ x = (D.μ x - 1) • D.Δ x := by
    rw [neg_smul, ← smul_neg, ← D.Δ_inv hx0, ← D.Δ_one_sub hinv, e, Δ_neg, D.Δ_div h1x hx0,
      D.Δ_one_sub h, sub_smul, one_smul]
  have := (smul_left_inj h).1 key
  linear_combination -this

/-- Blueprint Lemma 6.6 (`lem:onevar`): `μ x ≠ 1` for primitive `x`. -/
lemma μ_ne_one (h : D.Δ x ≠ 0) : D.μ x ≠ 1 := by
  have hinv : D.Δ x⁻¹ ≠ 0 := by rwa [D.Δ_inv (D.ne_zero_of_Δ_ne_zero h), neg_ne_zero]
  intro h1
  apply D.μ_ne_zero hinv
  rw [D.μ_inv h, h1, sub_self]

lemma μ_sub_one_ne_zero (h : D.Δ x ≠ 0) : D.μ x - 1 ≠ 0 :=
  sub_ne_zero.2 (D.μ_ne_one h)

/-! ### The function `t` -/

/-- The function `t x = μ x / (μ x - 1)` of blueprint Lemma 6.6 (`lem:onevar`). -/
noncomputable def t (x : K) : F := D.μ x / (D.μ x - 1)

lemma t_of_Δ_eq_zero (h : D.Δ x = 0) : D.t x = 0 := by
  rw [t, D.μ_of_Δ_eq_zero h, zero_div]

lemma t_ne_zero (h : D.Δ x ≠ 0) : D.t x ≠ 0 :=
  div_ne_zero (D.μ_ne_zero h) (D.μ_sub_one_ne_zero h)

lemma t_ne_one (h : D.Δ x ≠ 0) : D.t x ≠ 1 := by
  rw [t, Ne, div_eq_one_iff_eq (D.μ_sub_one_ne_zero h)]
  intro e
  simpa using congrArg (· - D.μ x) e

lemma t_sub_one_ne_zero (h : D.Δ x ≠ 0) : D.t x - 1 ≠ 0 :=
  sub_ne_zero.2 (D.t_ne_one h)

/-- `μ` can be recovered from `t`: `μ x = t x / (t x - 1)`. -/
lemma μ_eq_t_div (h : D.Δ x ≠ 0) : D.μ x = D.t x / (D.t x - 1) := by
  have h1 := D.μ_sub_one_ne_zero h
  rw [t, eq_div_iff (by simpa [t] using D.t_sub_one_ne_zero h)]
  field_simp
  ring

/-- Blueprint Lemma 6.6 (`lem:onevar`): `t (1 - x) = 1 - t x`. -/
lemma t_one_sub (h : D.Δ x ≠ 0) : D.t (1 - x) = 1 - D.t x := by
  have h0 := D.μ_ne_zero h
  have h1 := D.μ_sub_one_ne_zero h
  have h1' : 1 - D.μ x ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 h1
  rw [t, t, D.μ_one_sub h]
  field_simp
  ring

/-- Blueprint Lemma 6.6 (`lem:onevar`): `t (1 / x) = 1 / t x`. -/
lemma t_inv (h : D.Δ x ≠ 0) : D.t x⁻¹ = (D.t x)⁻¹ := by
  rw [t, t, D.μ_inv h, inv_div, show 1 - D.μ x - 1 = -D.μ x by ring, div_neg, ← neg_div,
    neg_sub]

/-! ### Transverse pairs -/

/-- Two elements `x, y` are *transverse* if `Δ x, Δ y` are linearly independent
(blueprint Section 6.3). -/
def Transverse (x y : K) : Prop := LinearIndependent F ![D.Δ x, D.Δ y]

variable {D}

lemma Transverse.smul_add_smul_eq_zero (h : D.Transverse x y) {a b : F}
    (hab : a • D.Δ x + b • D.Δ y = 0) : a = 0 ∧ b = 0 :=
  LinearIndependent.pair_iff.1 h a b hab

lemma Transverse.smul_add_smul_inj (h : D.Transverse x y) {a b c d : F}
    (he : a • D.Δ x + b • D.Δ y = c • D.Δ x + d • D.Δ y) : a = c ∧ b = d := by
  have := h.smul_add_smul_eq_zero (a := a - c) (b := b - d) (by
    rw [sub_smul, sub_smul, ← sub_eq_zero.2 he]
    abel)
  exact ⟨sub_eq_zero.1 this.1, sub_eq_zero.1 this.2⟩

lemma Transverse.smul_add_smul_ne_zero (h : D.Transverse x y) {a b : F} (hab : a ≠ 0 ∨ b ≠ 0) :
    a • D.Δ x + b • D.Δ y ≠ 0 := fun e ↦ by
  have := h.smul_add_smul_eq_zero e
  tauto

lemma Transverse.symm (h : D.Transverse x y) : D.Transverse y x :=
  LinearIndependent.pair_symm_iff.1 h

lemma Transverse.Δ_ne_zero_left (h : D.Transverse x y) : D.Δ x ≠ 0 :=
  h.ne_zero 0

lemma Transverse.Δ_ne_zero_right (h : D.Transverse x y) : D.Δ y ≠ 0 :=
  h.symm.Δ_ne_zero_left

variable (D) in
lemma transverse_iff : D.Transverse x y ↔ D.Δ x ≠ 0 ∧ D.Δ y ∉ F ∙ D.Δ x := by
  refine ⟨fun h ↦ ⟨h.Δ_ne_zero_left, ?_⟩, fun ⟨hx, hy⟩ ↦ ?_⟩
  · rw [mem_span_singleton]
    exact not_exists.2 ((LinearIndependent.pair_iff' h.Δ_ne_zero_left).1 h)
  · rw [mem_span_singleton, not_exists] at hy
    exact (LinearIndependent.pair_iff' hx).2 hy

/-- Change of basis: if `x, y` are transverse and `Δ x', Δ y'` are obtained from `Δ x, Δ y` by an
invertible matrix, then `x', y'` are transverse. -/
lemma Transverse.of_eq {x' y' : K} (h : D.Transverse x y) {a b c d : F}
    (hx' : D.Δ x' = a • D.Δ x + b • D.Δ y) (hy' : D.Δ y' = c • D.Δ x + d • D.Δ y)
    (hdet : a * d - b * c ≠ 0) : D.Transverse x' y' := by
  rw [Transverse, LinearIndependent.pair_iff]
  intro s t hst
  rw [hx', hy'] at hst
  obtain ⟨h₁, h₂⟩ := h.smul_add_smul_eq_zero (a := s * a + t * c) (b := s * b + t * d) (by
    rw [← hst]
    simp only [add_smul, mul_smul, smul_add]
    abel)
  have hs : s * (a * d - b * c) = 0 := by linear_combination d * h₁ - c * h₂
  have ht : t * (a * d - b * c) = 0 := by linear_combination a * h₂ - b * h₁
  exact ⟨(mul_eq_zero.1 hs).resolve_right hdet, (mul_eq_zero.1 ht).resolve_right hdet⟩

/-- If `Δ x' = Δ x` and `x, y` are transverse, then so are `x', y`. -/
lemma Transverse.of_Δ_eq_left {x' : K} (h : D.Transverse x y) (hx' : D.Δ x' = D.Δ x) :
    D.Transverse x' y :=
  h.of_eq (a := 1) (b := 0) (c := 0) (d := 1) (by simp [hx']) (by simp) (by simp)

/-! ### Consequences of (H3) -/

variable (D)

/-- There is a primitive element (from (H3) with three zero vectors). -/
lemma exists_Δ_ne_zero : ∃ z, D.Δ z ≠ 0 := by
  obtain ⟨z, hz, -, -⟩ := D.exists_Δ_notMem_span 0 0 0
  exact ⟨z, fun h ↦ hz (by rw [h]; exact zero_mem _)⟩

/-- Any two primitive elements are transverse to a common third one
(blueprint, after Lemma 6.5). -/
lemma exists_transverse_transverse (hy : D.Δ y ≠ 0) (hz : D.Δ z ≠ 0) :
    ∃ w, D.Transverse y w ∧ D.Transverse z w := by
  obtain ⟨w, hwy, hwz, -⟩ := D.exists_Δ_notMem_span (D.Δ y) (D.Δ z) 0
  exact ⟨w, (D.transverse_iff).2 ⟨hy, hwy⟩, (D.transverse_iff).2 ⟨hz, hwz⟩⟩

/-- There is a transverse pair. -/
lemma exists_transverse : ∃ x y, D.Transverse x y := by
  obtain ⟨x, hx⟩ := D.exists_Δ_ne_zero
  obtain ⟨y, hy, -⟩ := D.exists_transverse_transverse hx hx
  exact ⟨x, y, hy⟩

/-! ### Two variables -/

variable {D}

lemma Transverse.Δ_mul (h : D.Transverse x y) : D.Δ (x * y) = D.Δ x + D.Δ y :=
  D.Δ_mul _ _ (D.ne_zero_of_Δ_ne_zero h.Δ_ne_zero_left)
    (D.ne_zero_of_Δ_ne_zero h.Δ_ne_zero_right)

/-- Blueprint Lemma 6.7 (`lem:twovar`): if `x, y` are transverse then `x * y` is primitive. -/
lemma Transverse.Δ_mul_ne_zero (h : D.Transverse x y) : D.Δ (x * y) ≠ 0 := by
  rw [h.Δ_mul]
  simpa using h.smul_add_smul_ne_zero (a := 1) (b := 1) (Or.inl one_ne_zero)

/-- `x, x * y` are transverse if `x, y` are. -/
lemma Transverse.mul_right (h : D.Transverse x y) : D.Transverse x (x * y) :=
  h.of_eq (a := 1) (b := 0) (c := 1) (d := 1) (by simp) (by simp [h.Δ_mul]) (by simp)

/-- Blueprint Lemma 6.7 (`lem:twovar`, Two variables): if `x, y` are transverse then
`t (x * y) = t x * t y`.

The proof uses `1 - x y = (1 - x) (1 - u)` with `u = x (1 - y) / (x - 1)`. -/
theorem Transverse.t_mul (h : D.Transverse x y) : D.t (x * y) = D.t x * D.t y := by
  have hx := h.Δ_ne_zero_left
  have hy := h.Δ_ne_zero_right
  have hxy := h.Δ_mul_ne_zero
  have hx0 := D.ne_zero_of_Δ_ne_zero hx
  have hx1 : x - 1 ≠ 0 := sub_ne_zero.2 (D.ne_one_of_Δ_ne_zero hx)
  have h1x := D.one_sub_ne_zero_of_Δ_ne_zero hx
  have h1y := D.one_sub_ne_zero_of_Δ_ne_zero hy
  set u := x * (1 - y) / (x - 1) with hu_def
  -- `Δ u = (1 - μ x) Δ x + μ y Δ y`, so `u` is primitive
  have hΔu : D.Δ u = (1 - D.μ x) • D.Δ x + D.μ y • D.Δ y := by
    have e : x - 1 = -(1 - x) := (neg_sub _ _).symm
    rw [hu_def, D.Δ_div (mul_ne_zero hx0 h1y) hx1, D.Δ_mul _ _ hx0 h1y, e, Δ_neg,
      D.Δ_one_sub hx, D.Δ_one_sub hy, sub_smul, one_smul]
    abel
  have hu : D.Δ u ≠ 0 := by
    rw [hΔu]
    exact h.smul_add_smul_ne_zero (Or.inr (D.μ_ne_zero hy))
  have h1u := D.one_sub_ne_zero_of_Δ_ne_zero hu
  -- the identity `1 - x y = (1 - x) (1 - u)`
  have key : 1 - x * y = (1 - x) * (1 - u) := by
    rw [hu_def]
    field_simp
    ring
  have hΔ : D.μ (x * y) • D.Δ x + D.μ (x * y) • D.Δ y =
      (D.μ x + D.μ u * (1 - D.μ x)) • D.Δ x + (D.μ u * D.μ y) • D.Δ y := by
    rw [← smul_add, ← h.Δ_mul, ← D.Δ_one_sub hxy, key, D.Δ_mul _ _ h1x h1u, D.Δ_one_sub hx,
      D.Δ_one_sub hu, hΔu]
    simp only [add_smul, mul_smul, smul_add]
    abel
  obtain ⟨e₁, e₂⟩ := h.smul_add_smul_inj hΔ
  have hμx := D.μ_sub_one_ne_zero hx
  have hμy := D.μ_sub_one_ne_zero hy
  have hμxy := D.μ_sub_one_ne_zero hxy
  rw [t, t, t, div_mul_div_comm, div_eq_div_iff hμxy (mul_ne_zero hμx hμy)]
  linear_combination (-D.μ y) * e₁ + (1 - D.μ x) * e₂

end StepBData

section LinearAlgebra

variable {K F Ω : Type*} [Field K] [Field F] [AddCommGroup Ω] [Module F Ω]

/-- If `x, y` are transverse and `Δ x = c • u`, `Δ y = c' • v`, then `u, v` are linearly
independent. -/
theorem StepBData.Transverse.linearIndependent_of_eq_smul {D : StepBData K F Ω} {x y : K}
    (h : D.Transverse x y) {u v : Ω} {c c' : F} (hc : D.Δ x = c • u) (hc' : D.Δ y = c' • v) :
    LinearIndependent F ![u, v] := by
  have hc0 : c ≠ 0 := fun h0 ↦ h.Δ_ne_zero_left (by rw [hc, h0, zero_smul])
  have hc'0 : c' ≠ 0 := fun h0 ↦ h.Δ_ne_zero_right (by rw [hc', h0, zero_smul])
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have := h.smul_add_smul_eq_zero (a := s / c) (b := t / c') (by
    rw [hc, hc', smul_smul, smul_smul, div_mul_cancel₀ s hc0, div_mul_cancel₀ t hc'0, hst])
  exact ⟨(div_eq_zero_iff.1 this.1).resolve_right hc0,
    (div_eq_zero_iff.1 this.2).resolve_right hc'0⟩

/-- Comparing coefficients: if `u, v` are linearly independent and
`c'' • (u + v) = c • u + c' • v`, then `c'' = c` and `c'' = c'`. -/
theorem eq_of_linearIndependent_pair {u v : Ω} (hli : LinearIndependent F ![u, v])
    {c c' c'' : F} (h : c'' • (u + v) = c • u + c' • v) : c'' = c ∧ c'' = c' := by
  obtain ⟨h₁, h₂⟩ := LinearIndependent.pair_iff.1 hli (c'' - c) (c'' - c') (by
    rw [sub_smul, sub_smul, sub_add_sub_comm, ← smul_add, h, sub_self])
  exact ⟨sub_eq_zero.1 h₁, sub_eq_zero.1 h₂⟩

end LinearAlgebra

end MilnorAlgDep
