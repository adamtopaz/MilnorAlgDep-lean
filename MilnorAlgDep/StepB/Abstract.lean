module

public import MilnorAlgDep.StepB.Basic
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Abstract Step B: the field embedding

This file formalizes blueprint Section 6.5 ("The field embedding": Lemma 6.8 `lem:tconst`,
equation (P3) `eq:P3`, Proposition 6.9 `prop:tau`) in the abstract setting of
`MilnorAlgDep.StepBData` (see `MilnorAlgDep.StepB.Basic`).

## Main results

* `MilnorAlgDep.StepBData.τ`: the ring homomorphism `K →+* F` of Proposition 6.9.
* `MilnorAlgDep.StepBData.exists_ringHom`: the main theorem: there is a ring homomorphism
  `τ : K →+* F` with `(τ x - 1) • Δ (1 - x) = τ x • Δ x` for every primitive `x`.
* `MilnorAlgDep.StepBData.eq_τ`, `MilnorAlgDep.StepBData.existsUnique_ringHom`: such a `τ` is
  unique.
* `MilnorAlgDep.StepBData.τ_eq_μ_div`, `MilnorAlgDep.StepBData.μ_eq_τ_div`: `τ x = t x` and
  `μ x = τ x / (τ x - 1)` for primitive `x`.
* `MilnorAlgDep.StepBData.ofAddMonoidHom`, `MilnorAlgDep.exists_ringHom_of_addMonoidHom`: the
  same for a bundled homomorphism `Additive Kˣ →+ Ω`.

## Implementation notes

The blueprint defines `τ` on `𝒩 = {x ≠ 0 | Δ x = 0}` as the common value of `t (x z) / t z`
over primitive `z`. We fix one primitive element `z₀` and put `τ₀ x = t (x z₀) / t z₀`; the
independence of the choice is `t_mul_of_Δ_eq_zero`. The blueprint's case distinction in step (1)
of Proposition 6.9 (transverse or not) is replaced by: `Δ y ∉ F ∙ Δ x` (then (P3) applies
directly) or `Δ y ∈ F ∙ Δ x` (then the blueprint's auxiliary `z` is used); this avoids an
appeal to symmetry.
-/

@[expose] public section

namespace MilnorAlgDep

open Submodule

namespace StepBData

variable {K F Ω : Type*} [Field K] [Field F] [AddCommGroup Ω] [Module F Ω]
variable (D : StepBData K F Ω) {x y z s : K}

/-! ### The homomorphism `τ` on `𝒩` (Lemma 6.8(a)) -/

/-- A fixed primitive element, used to define `τ` on `𝒩 = {x ≠ 0 | Δ x = 0}`. -/
noncomputable def z₀ : K := D.exists_Δ_ne_zero.choose

lemma Δ_z₀ : D.Δ D.z₀ ≠ 0 := D.exists_Δ_ne_zero.choose_spec

/-- The map `τ` of blueprint Lemma 6.8(a) (`lem:tconst`) on `𝒩 = {x ≠ 0 | Δ x = 0}`, normalised
using the fixed primitive element `z₀`. Its values outside `𝒩` are irrelevant. -/
noncomputable def τ₀ (x : K) : F := D.t (x * D.z₀) / D.t D.z₀

lemma t_mul_mul_t_eq_of_Δ_eq_zero (hx0 : x ≠ 0) (hx : D.Δ x = 0) (h : D.Transverse y z) :
    D.t (x * y) * D.t z = D.t (x * z) * D.t y := by
  have hy0 := D.ne_zero_of_Δ_ne_zero h.Δ_ne_zero_left
  have hz0 := D.ne_zero_of_Δ_ne_zero h.Δ_ne_zero_right
  have h₁ : D.Transverse (x * y) z := h.of_Δ_eq_left (D.Δ_mul_of_Δ_eq_zero hx0 hx hy0)
  have h₂ : D.Transverse (x * z) y := h.symm.of_Δ_eq_left (D.Δ_mul_of_Δ_eq_zero hx0 hx hz0)
  rw [← h₁.t_mul, ← h₂.t_mul, mul_right_comm]

/-- Blueprint Lemma 6.8(a) (`lem:tconst`): for `x ∈ 𝒩` and primitive `z`,
`t (x z) = τ₀ x * t z`. -/
theorem t_mul_of_Δ_eq_zero (hx0 : x ≠ 0) (hx : D.Δ x = 0) (hz : D.Δ z ≠ 0) :
    D.t (x * z) = D.τ₀ x * D.t z := by
  obtain ⟨w, hzw, hz₀w⟩ := D.exists_transverse_transverse hz D.Δ_z₀
  have e₁ := D.t_mul_mul_t_eq_of_Δ_eq_zero hx0 hx hzw
  have e₂ := D.t_mul_mul_t_eq_of_Δ_eq_zero hx0 hx hz₀w
  rw [τ₀, div_mul_eq_mul_div, eq_div_iff (D.t_ne_zero D.Δ_z₀)]
  apply mul_right_cancel₀ (D.t_ne_zero hzw.Δ_ne_zero_right)
  linear_combination D.t D.z₀ * e₁ - D.t z * e₂

/-! ### Sums of transverse elements (Lemma 6.8(b)) -/

variable {D}

lemma Transverse.Δ_neg_div (h : D.Transverse x y) : D.Δ (-x / y) = D.Δ x - D.Δ y := by
  rw [D.Δ_div (neg_ne_zero.2 (D.ne_zero_of_Δ_ne_zero h.Δ_ne_zero_left))
    (D.ne_zero_of_Δ_ne_zero h.Δ_ne_zero_right), Δ_neg]

lemma Transverse.Δ_neg_div_ne_zero (h : D.Transverse x y) : D.Δ (-x / y) ≠ 0 := by
  rw [h.Δ_neg_div]
  simpa [sub_eq_add_neg] using h.smul_add_smul_ne_zero (a := 1) (b := -1) (Or.inl one_ne_zero)

lemma Transverse.add_eq_mul (h : D.Transverse x y) : x + y = y * (1 - -x / y) := by
  have hy0 := D.ne_zero_of_Δ_ne_zero h.Δ_ne_zero_right
  field_simp
  ring

/-- `Δ (x + y) = μ (-x / y) Δ x + (1 - μ (-x / y)) Δ y` for transverse `x, y`. -/
lemma Transverse.Δ_add (h : D.Transverse x y) :
    D.Δ (x + y) = D.μ (-x / y) • D.Δ x + (1 - D.μ (-x / y)) • D.Δ y := by
  have hs := h.Δ_neg_div_ne_zero
  rw [h.add_eq_mul, D.Δ_mul _ _ (D.ne_zero_of_Δ_ne_zero h.Δ_ne_zero_right)
    (D.one_sub_ne_zero_of_Δ_ne_zero hs), D.Δ_one_sub hs, h.Δ_neg_div]
  simp only [smul_sub, sub_smul, one_smul]
  abel

/-- Blueprint Lemma 6.8(b) (`lem:tconst`): if `x, y` are transverse, then `x + y, x` are
transverse. -/
lemma Transverse.add_left (h : D.Transverse x y) : D.Transverse (x + y) x :=
  h.of_eq (c := 1) (d := 0) h.Δ_add (by simp) <| by
    simpa using D.μ_sub_one_ne_zero h.Δ_neg_div_ne_zero

/-- Blueprint Lemma 6.8(b) (`lem:tconst`): if `x, y` are transverse, then `x + y, y` are
transverse. -/
lemma Transverse.add_right (h : D.Transverse x y) : D.Transverse (x + y) y :=
  h.of_eq (c := 0) (d := 1) h.Δ_add (by simp) <| by
    simpa using D.μ_ne_zero h.Δ_neg_div_ne_zero

/-- Blueprint Lemma 6.8(b) (`lem:tconst`): if `x, y` are transverse, then `x + y` is
primitive. -/
lemma Transverse.Δ_add_ne_zero (h : D.Transverse x y) : D.Δ (x + y) ≠ 0 :=
  h.add_left.Δ_ne_zero_left

lemma Transverse.t_add_eq (h : D.Transverse x y) :
    D.t (x + y) = D.t y - D.τ₀ (-1) * D.t x := by
  have hx := h.Δ_ne_zero_left
  have hy := h.Δ_ne_zero_right
  have hs := h.Δ_neg_div_ne_zero
  -- `y` and `1 + x / y` are transverse
  have h₁ : D.Transverse y (1 - -x / y) :=
    h.of_eq (a := 0) (b := 1) (c := D.μ (-x / y)) (d := -D.μ (-x / y)) (by simp)
      (by rw [D.Δ_one_sub hs, h.Δ_neg_div, smul_sub, sub_eq_add_neg, neg_smul])
      (by simpa using D.μ_ne_zero hs)
  -- `-x` and `1 / y` are transverse
  have h₂ : D.Transverse (-x) y⁻¹ :=
    h.of_eq (a := 1) (b := 0) (c := 0) (d := -1) (by simp)
      (by simp [D.Δ_inv (D.ne_zero_of_Δ_ne_zero hy)]) (by simp)
  have ht : D.t (-x) = D.τ₀ (-1) * D.t x := by
    rw [neg_eq_neg_one_mul]
    exact D.t_mul_of_Δ_eq_zero (neg_ne_zero.2 one_ne_zero) D.Δ_neg_one hx
  rw [h.add_eq_mul, h₁.t_mul, D.t_one_sub hs, div_eq_mul_inv, h₂.t_mul, D.t_inv hy, ht]
  field_simp [D.t_ne_zero hy]

variable (D) in
/-- Blueprint Lemma 6.8(b) (`lem:tconst`): `τ (-1) = -1`. -/
theorem τ₀_neg_one : D.τ₀ (-1) = -1 := by
  obtain ⟨x, y, h⟩ := D.exists_transverse
  have hx := h.Δ_ne_zero_left
  have e₁ := h.t_add_eq
  have e₂ : D.t (x + y) = D.t x - D.τ₀ (-1) * D.t y := by
    rw [add_comm]; exact h.symm.t_add_eq
  have e₃ := h.mul_right.t_add_eq
  have e₄ : D.t (x + x * y) = D.t x - D.τ₀ (-1) * D.t (x * y) := by
    rw [add_comm]; exact h.mul_right.symm.t_add_eq
  by_contra hne
  have hc : 1 + D.τ₀ (-1) ≠ 0 := fun h0 ↦ hne (by linear_combination h0)
  -- `t y = t x` and `t (x y) = t x`, hence `t x = t x * t x`
  have h₁ : D.t y = D.t x := mul_left_cancel₀ hc (by linear_combination e₂ - e₁)
  have h₂ : D.t (x * y) = D.t x := mul_left_cancel₀ hc (by linear_combination e₄ - e₃)
  rw [h.t_mul, h₁] at h₂
  exact D.t_ne_one hx (mul_left_cancel₀ (D.t_ne_zero hx) (by linear_combination h₂))

/-- Blueprint Lemma 6.8(b) (`lem:tconst`): `t (x + y) = t x + t y` for transverse `x, y`. -/
theorem Transverse.t_add (h : D.Transverse x y) : D.t (x + y) = D.t x + D.t y := by
  rw [h.t_add_eq, D.τ₀_neg_one]
  ring

/-! ### The map `τ` and equation (P3) -/

variable (D)

open Classical in
/-- The map `τ : K → F` of blueprint Section 6.5: `τ x = t x` for primitive `x` and `τ x` is
given by Lemma 6.8(a) for `x ∈ 𝒩`; `τ 0 = 0`. Bundled as a ring homomorphism in `τ`. -/
noncomputable def τFun (x : K) : F := if D.Δ x = 0 then D.τ₀ x else D.t x

lemma τFun_of_Δ_eq_zero (h : D.Δ x = 0) : D.τFun x = D.τ₀ x := by
  simp [τFun, h]

lemma τFun_of_Δ_ne_zero (h : D.Δ x ≠ 0) : D.τFun x = D.t x := by
  simp [τFun, h]

lemma τFun_zero : D.τFun 0 = 0 := by
  rw [τFun_of_Δ_eq_zero _ D.Δ_zero, τ₀, zero_mul, D.t_of_Δ_eq_zero D.Δ_zero, zero_div]

lemma τFun_one : D.τFun 1 = 1 := by
  rw [τFun_of_Δ_eq_zero _ D.Δ_one, τ₀, one_mul, div_self (D.t_ne_zero D.Δ_z₀)]

lemma τFun_neg_one : D.τFun (-1) = -1 := by
  rw [τFun_of_Δ_eq_zero _ D.Δ_neg_one, τ₀_neg_one]

lemma Δ_ne_zero_of_notMem_span (hz : D.Δ z ∉ F ∙ D.Δ x) : D.Δ z ≠ 0 := fun h ↦
  hz (by rw [h]; exact zero_mem _)

lemma Δ_mul_ne_zero_of_notMem_span (hx : x ≠ 0) (hz : D.Δ z ∉ F ∙ D.Δ x) :
    D.Δ (x * z) ≠ 0 := by
  rw [D.Δ_mul _ _ hx (D.ne_zero_of_Δ_ne_zero (D.Δ_ne_zero_of_notMem_span hz))]
  intro h
  apply hz
  rw [eq_neg_of_add_eq_zero_right h]
  exact neg_mem (mem_span_singleton_self _)

/-- Blueprint equation (P3) (`eq:P3`): `t (x z) = τ x * t z` for `x ≠ 0` and primitive `z` with
`F Δ z ≠ F Δ x`. (In this situation `x z` is primitive: `Δ_mul_ne_zero_of_notMem_span`.) -/
theorem t_mul_of_notMem_span (hx : x ≠ 0) (hz : D.Δ z ∉ F ∙ D.Δ x) :
    D.t (x * z) = D.τFun x * D.t z := by
  by_cases hΔx : D.Δ x = 0
  · rw [τFun_of_Δ_eq_zero _ hΔx]
    exact D.t_mul_of_Δ_eq_zero hx hΔx (D.Δ_ne_zero_of_notMem_span hz)
  · rw [τFun_of_Δ_ne_zero _ hΔx]
    exact ((D.transverse_iff).2 ⟨hΔx, hz⟩).t_mul

/-! ### Proposition 6.9 -/

/-- Blueprint Proposition 6.9 (`prop:tau`), step (1): `τ` is multiplicative. -/
theorem τFun_mul (x y : K) : D.τFun (x * y) = D.τFun x * D.τFun y := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [τFun_zero]
  rcases eq_or_ne y 0 with rfl | hy0
  · simp [τFun_zero]
  by_cases hy : D.Δ y ∈ F ∙ D.Δ x
  · -- choose `z` with `F Δ z` different from `F Δ x`, `F Δ (x y)`, `F Δ y`
    obtain ⟨z, hzx, hzxy, hzy⟩ := D.exists_Δ_notMem_span (D.Δ x) (D.Δ (x * y)) (D.Δ y)
    have hz := D.Δ_ne_zero_of_notMem_span hzx
    have hyz : D.Δ (y * z) ∉ F ∙ D.Δ x := by
      rw [D.Δ_mul _ _ hy0 (D.ne_zero_of_Δ_ne_zero hz)]
      intro h
      exact hzx (by simpa using sub_mem h hy)
    have e₁ := D.t_mul_of_notMem_span (mul_ne_zero hx0 hy0) hzxy
    have e₂ := D.t_mul_of_notMem_span hy0 hzy
    have e₃ := D.t_mul_of_notMem_span hx0 hyz
    rw [← mul_assoc, e₁, e₂] at e₃
    exact mul_right_cancel₀ (D.t_ne_zero hz) (e₃.trans (mul_assoc _ _ _).symm)
  · rw [τFun_of_Δ_ne_zero _ (D.Δ_mul_ne_zero_of_notMem_span hx0 hy),
      τFun_of_Δ_ne_zero _ (D.Δ_ne_zero_of_notMem_span hy), D.t_mul_of_notMem_span hx0 hy]

/-- Blueprint Proposition 6.9 (`prop:tau`), step (2): `τ (1 - s) = 1 - τ s` for `s ≠ 0, 1`. -/
theorem τFun_one_sub (hs0 : s ≠ 0) (hs1 : s ≠ 1) : D.τFun (1 - s) = 1 - D.τFun s := by
  by_cases hs : D.Δ s = 0
  swap
  · rw [τFun_of_Δ_ne_zero _ (D.Δ_one_sub_ne_zero hs), τFun_of_Δ_ne_zero _ hs, D.t_one_sub hs]
  have h1s : D.Δ (1 - s) = 0 := (D.Δ_eq_zero_iff_one_sub s hs0 hs1).1 hs
  have h1s0 : 1 - s ≠ 0 := sub_ne_zero.2 hs1.symm
  rw [τFun_of_Δ_eq_zero _ h1s, τFun_of_Δ_eq_zero _ hs]
  obtain ⟨x, y, h⟩ := D.exists_transverse
  have hx := h.Δ_ne_zero_left
  have hx0 := D.ne_zero_of_Δ_ne_zero hx
  -- `t ((1 - s) x + y) = τ (1 - s) t x + t y`
  have e₁ := (h.of_Δ_eq_left (D.Δ_mul_of_Δ_eq_zero h1s0 h1s hx0)).t_add
  rw [D.t_mul_of_Δ_eq_zero h1s0 h1s hx] at e₁
  -- `t ((x + y) + (-s x)) = t x + t y - τ s t x`
  have hsx : D.Δ (s * x) = D.Δ x := D.Δ_mul_of_Δ_eq_zero hs0 hs hx0
  have h₂ : D.Transverse (x + y) (-s * x) :=
    (h.add_left.symm.of_Δ_eq_left (by rw [neg_mul, Δ_neg, hsx])).symm
  have e₂ := h₂.t_add
  have e₃ : D.t (-s * x) = -1 * (D.τ₀ s * D.t x) := by
    rw [show -s * x = -1 * (s * x) by ring,
      D.t_mul_of_Δ_eq_zero (neg_ne_zero.2 one_ne_zero) D.Δ_neg_one (by rwa [hsx]),
      D.τ₀_neg_one, D.t_mul_of_Δ_eq_zero hs0 hs hx]
  rw [e₃, h.t_add, show x + y + -s * x = (1 - s) * x + y by ring, e₁] at e₂
  exact mul_right_cancel₀ (D.t_ne_zero hx) (by linear_combination e₂)

/-- Blueprint Proposition 6.9 (`prop:tau`), step (3): `τ` is additive. -/
theorem τFun_add (x y : K) : D.τFun (x + y) = D.τFun x + D.τFun y := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp [τFun_zero]
  rcases eq_or_ne y 0 with rfl | hy0
  · simp [τFun_zero]
  have hneg (w : K) : D.τFun (-w) = -D.τFun w := by
    rw [neg_eq_neg_one_mul, τFun_mul, τFun_neg_one, neg_one_mul]
  rcases eq_or_ne (x + y) 0 with hxy | hxy
  · rw [hxy, τFun_zero, eq_neg_of_add_eq_zero_right hxy, hneg, add_neg_cancel]
  have hs0 : -x / y ≠ 0 := div_ne_zero (neg_ne_zero.2 hx0) hy0
  have hs1 : -x / y ≠ 1 := by
    rw [Ne, div_eq_one_iff_eq hy0]
    intro h
    exact hxy (by rw [← h]; ring)
  have e : x + y = y * (1 - -x / y) := by
    field_simp
    ring
  have hinv : D.τFun y * D.τFun y⁻¹ = 1 := by
    rw [← τFun_mul, mul_inv_cancel₀ hy0, τFun_one]
  rw [e, τFun_mul, τFun_one_sub _ hs0 hs1, div_eq_mul_inv, τFun_mul, hneg]
  linear_combination D.τFun x * hinv

/-- Blueprint Proposition 6.9 (`prop:tau`): the map `τ` is a ring homomorphism `K →+* F`
(hence a field embedding). For primitive `x` it is given by `τ x = μ x / (μ x - 1)`
(`τ_eq_μ_div`). -/
noncomputable def τ : K →+* F where
  toFun := D.τFun
  map_one' := D.τFun_one
  map_mul' := D.τFun_mul
  map_zero' := D.τFun_zero
  map_add' := D.τFun_add

lemma τ_apply (x : K) : D.τ x = D.τFun x := rfl

/-- `τ x = t x` for primitive `x`. -/
lemma τ_eq_t (h : D.Δ x ≠ 0) : D.τ x = D.t x :=
  D.τFun_of_Δ_ne_zero h

/-- `τ x = μ x / (μ x - 1)` for primitive `x`. -/
theorem τ_eq_μ_div (h : D.Δ x ≠ 0) : D.τ x = D.μ x / (D.μ x - 1) :=
  D.τ_eq_t h

/-- `μ x = τ x / (τ x - 1)` for primitive `x`. -/
theorem μ_eq_τ_div (h : D.Δ x ≠ 0) : D.μ x = D.τ x / (D.τ x - 1) := by
  rw [D.τ_eq_t h, D.μ_eq_t_div h]

/-- `τ x ≠ 1` for primitive `x`. -/
theorem τ_ne_one (h : D.Δ x ≠ 0) : D.τ x ≠ 1 := by
  rw [D.τ_eq_t h]
  exact D.t_ne_one h

/-- The defining identity of `τ`: `(τ x - 1) • Δ (1 - x) = τ x • Δ x` for primitive `x`. -/
theorem τ_sub_one_smul_Δ_one_sub (h : D.Δ x ≠ 0) :
    (D.τ x - 1) • D.Δ (1 - x) = D.τ x • D.Δ x := by
  rw [D.Δ_one_sub h, smul_smul, D.τ_eq_μ_div h]
  congr 1
  have := D.μ_sub_one_ne_zero h
  field_simp
  ring

/-- The identity `(τ x - 1) • Δ (1 - x) = τ x • Δ x` holds for all `x` (both sides vanish when
`x` is not primitive). -/
theorem τ_sub_one_smul_Δ_one_sub' (x : K) : (D.τ x - 1) • D.Δ (1 - x) = D.τ x • D.Δ x := by
  by_cases h : D.Δ x = 0
  · rcases eq_or_ne x 0 with rfl | hx0
    · simp
    rcases eq_or_ne x 1 with rfl | hx1
    · simp
    rw [h, (D.Δ_eq_zero_iff_one_sub x hx0 hx1).1 h, smul_zero, smul_zero]
  · exact D.τ_sub_one_smul_Δ_one_sub h

/-- **Abstract Step B** (blueprint Lemmas 6.6–6.8 and Proposition 6.9, `prop:tau`):
there is a ring homomorphism `τ : K →+* F` such that `(τ x - 1) • Δ (1 - x) = τ x • Δ x` for
every primitive `x`, i.e. `τ x = t x = μ x / (μ x - 1)`. It is `MilnorAlgDep.StepBData.τ`. -/
theorem exists_ringHom :
    ∃ τ : K →+* F, ∀ x, D.Δ x ≠ 0 → (τ x - 1) • D.Δ (1 - x) = τ x • D.Δ x :=
  ⟨D.τ, fun _ ↦ D.τ_sub_one_smul_Δ_one_sub⟩

/-- Uniqueness in abstract Step B: a ring homomorphism `τ'` with
`(τ' x - 1) • Δ (1 - x) = τ' x • Δ x` for every primitive `x` is equal to `τ`. -/
theorem eq_τ (τ' : K →+* F)
    (h : ∀ x, D.Δ x ≠ 0 → (τ' x - 1) • D.Δ (1 - x) = τ' x • D.Δ x) : τ' = D.τ := by
  have hprim (x : K) (hx : D.Δ x ≠ 0) : τ' x = D.τ x := by
    have e := h x hx
    rw [D.Δ_one_sub hx, smul_smul, smul_left_inj hx] at e
    rw [D.τ_eq_μ_div hx, eq_div_iff (D.μ_sub_one_ne_zero hx)]
    linear_combination e
  ext x
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  by_cases hx : D.Δ x = 0
  · have hz₀0 := D.ne_zero_of_Δ_ne_zero D.Δ_z₀
    have hxz : D.Δ (x * D.z₀) ≠ 0 := by
      rw [D.Δ_mul_of_Δ_eq_zero hx0 hx hz₀0]
      exact D.Δ_z₀
    have e := hprim _ hxz
    rw [map_mul, map_mul, hprim _ D.Δ_z₀] at e
    exact mul_right_cancel₀ ((map_ne_zero D.τ).2 hz₀0) e
  · exact hprim x hx

/-- Abstract Step B with uniqueness. -/
theorem existsUnique_ringHom :
    ∃! τ : K →+* F, ∀ x, D.Δ x ≠ 0 → (τ x - 1) • D.Δ (1 - x) = τ x • D.Δ x :=
  ⟨D.τ, fun _ ↦ D.τ_sub_one_smul_Δ_one_sub, D.eq_τ⟩

/-! ### Bundled homomorphisms out of `Kˣ` -/

section Units

variable (f : Additive Kˣ →+ Ω)
  (h0 : f (.ofMul (-1)) = 0)
  (h1 : ∀ (x : Kˣ) (hx : (1 : K) - x ≠ 0),
    f (.ofMul x) = 0 ↔ f (.ofMul (Units.mk0 (1 - x) hx)) = 0)
  (h2 : ∀ (x : Kˣ) (hx : (1 : K) - x ≠ 0),
    f (.ofMul x) ≠ 0 → f (.ofMul (Units.mk0 (1 - x) hx)) ∈ F ∙ f (.ofMul x))
  (h3 : ∀ v₁ v₂ v₃ : Ω, ∃ z : Kˣ,
    f (.ofMul z) ∉ F ∙ v₁ ∧ f (.ofMul z) ∉ F ∙ v₂ ∧ f (.ofMul z) ∉ F ∙ v₃)

open Classical in
/-- The data of abstract Step B for a bundled homomorphism `f : Additive Kˣ →+ Ω`:
`Δ x = f x` for `x ≠ 0` and `Δ 0 = 0`. The hypotheses `h0`–`h3` are (H0)–(H3). -/
noncomputable def ofAddMonoidHom : StepBData K F Ω where
  Δ x := if hx : x = 0 then 0 else f (.ofMul (Units.mk0 x hx))
  Δ_zero := by simp
  Δ_mul x y hx hy := by
    simp only [mul_ne_zero hx hy, hx, hy, dite_false, ← map_add, ← ofMul_mul, Units.mk0_mul]
  Δ_neg_one := by
    simp only [neg_eq_zero, one_ne_zero, dite_false]
    convert h0
    ext
    simp
  Δ_eq_zero_iff_one_sub x hx0 hx1 := by
    have h1x : 1 - x ≠ 0 := sub_ne_zero.2 hx1.symm
    simp only [hx0, h1x, dite_false]
    exact h1 (Units.mk0 x hx0) h1x
  Δ_one_sub_mem_span x hx0 hx1 hx := by
    have h1x : 1 - x ≠ 0 := sub_ne_zero.2 hx1.symm
    simp only [hx0, h1x, dite_false] at hx ⊢
    exact h2 (Units.mk0 x hx0) h1x hx
  exists_Δ_notMem_span v₁ v₂ v₃ := by
    obtain ⟨z, hz⟩ := h3 v₁ v₂ v₃
    refine ⟨z, ?_⟩
    simpa [Units.ne_zero] using hz

lemma ofAddMonoidHom_Δ (x : Kˣ) : (ofAddMonoidHom f h0 h1 h2 h3).Δ x = f (.ofMul x) := by
  simp [ofAddMonoidHom, Units.ne_zero]

lemma ofAddMonoidHom_Δ_of_ne_zero {x : K} (hx : x ≠ 0) :
    (ofAddMonoidHom f h0 h1 h2 h3).Δ x = f (.ofMul (Units.mk0 x hx)) := by
  simp [ofAddMonoidHom, hx]

end Units

end StepBData

open StepBData in
/-- **Abstract Step B** for a bundled homomorphism `f : Additive Kˣ →+ Ω`
(blueprint Lemmas 6.6–6.8 and Proposition 6.9, `prop:tau`, with `Δ = f`).
Hypotheses: (H0) `f (-1) = 0`; (H1) `f x = 0 ↔ f (1 - x) = 0`; (H2) `f (1 - x) ∈ F ∙ f x` if
`f x ≠ 0`; (H3) for any `v₁ v₂ v₃` some `f z` avoids the lines `F ∙ vᵢ`. Conclusion: a ring
homomorphism `τ : K →+* F` with `(τ x - 1) • f (1 - x) = τ x • f x` whenever `f x ≠ 0`.
The homomorphism is `(StepBData.ofAddMonoidHom f h0 h1 h2 h3).τ`, which gives access to the
API of `MilnorAlgDep.StepBData`. -/
theorem exists_ringHom_of_addMonoidHom {K F Ω : Type*} [Field K] [Field F] [AddCommGroup Ω]
    [Module F Ω] (f : Additive Kˣ →+ Ω)
    (h0 : f (.ofMul (-1)) = 0)
    (h1 : ∀ (x : Kˣ) (hx : (1 : K) - x ≠ 0),
      f (.ofMul x) = 0 ↔ f (.ofMul (Units.mk0 (1 - x) hx)) = 0)
    (h2 : ∀ (x : Kˣ) (hx : (1 : K) - x ≠ 0),
      f (.ofMul x) ≠ 0 → f (.ofMul (Units.mk0 (1 - x) hx)) ∈ F ∙ f (.ofMul x))
    (h3 : ∀ v₁ v₂ v₃ : Ω, ∃ z : Kˣ,
      f (.ofMul z) ∉ F ∙ v₁ ∧ f (.ofMul z) ∉ F ∙ v₂ ∧ f (.ofMul z) ∉ F ∙ v₃) :
    ∃ τ : K →+* F, ∀ (x : Kˣ) (hx : (1 : K) - x ≠ 0), f (.ofMul x) ≠ 0 →
      (τ x - 1) • f (.ofMul (Units.mk0 (1 - x) hx)) = τ x • f (.ofMul x) := by
  set D := ofAddMonoidHom f h0 h1 h2 h3
  refine ⟨D.τ, fun x hx hfx ↦ ?_⟩
  have e := D.τ_sub_one_smul_Δ_one_sub (x := x) (by rwa [ofAddMonoidHom_Δ])
  rwa [ofAddMonoidHom_Δ, ofAddMonoidHom_Δ_of_ne_zero f h0 h1 h2 h3 hx] at e

end MilnorAlgDep
