module

public import MilnorAlgDep.Milnor.KPrime
public import MilnorAlgDep.Milnor.Tame

/-!
# The last step of the proof of Theorem C

Blueprint Section 7.3, last paragraph: the identity `φ₁[x] = r[τ(x)]`, known in `V_{L|l₀}`, holds
in `L^×_ℚ`.

Let `C_L ⊆ L^×_ℚ` be the kernel of the projection `L^×_ℚ → V_{L|l₀}`; its elements are the
`(1/N)[c]` with `c ∈ l₀` (`TheoremC.isAlgebraic_of_proj_eq_zero`). Put
`χ(x) = φ₁[x] - r[τ(x)] ∈ C_L`.

* If `char L > 0`, then `C_L = 0`, because every non-zero element of `l₀` is a root of unity
  (`TheoremC.proj_injective_of_ringChar_ne_zero`).
* If `char L = 0`, the tame symbol `T_v` of a valuation `v` trivial on `l₀` with `v(τ x) > 0`
  shows `χ(1 - x) = 0` for `x ∉ k₀` (`TheoremC.eq_zero_of_tameSymbol`), hence `χ = 0`.

## Remarks on the blueprint

In the expansion of `0 = T_v {r[s] + χ(x), r[1 - s] + χ(1 - x)}` with
`T_v(ι α ι β) = v(α) ⊗ 𝔲(β) - v(β) ⊗ 𝔲(α)`: `v` vanishes on `C_L` (its elements are algebraic over
`l₀`) and on `[1 - s]`, and `𝔲[1 - s] = 0` (`1 - s` is a principal unit), so only
`r v(s) ⊗ 𝔲(χ(1 - x))` survives; `v(s) ≠ 0` and `𝔲` is injective on `C_L` (the relative algebraic
closure of `l₀`, i.e. `l₀` itself, embeds in the residue field, so `𝔲 [c] = 0` only for roots of
unity `c`). The argument does not use the characteristic: it applies whenever `C_L` is the image of
`l₀^×`, and in characteristic `p` it is not needed.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf MilnorKQ Tame

variable {K L : Type*} [Field K] [Field L]

namespace TheoremC

variable {l₀ : Subfield L} (hl₀ : ∀ x : L, x ∈ l₀ ↔ IsAlgebraic (⊥ : Subfield L) x)
include hl₀

/-- In characteristic `p > 0` the projection `L^×_ℚ → V_{L|l₀}` is injective (`C_L = 0`): the
non-zero elements of `l₀` are roots of unity. -/
theorem proj_injective_of_ringChar_ne_zero (hL : ringChar L ≠ 0) {w : VOf (⊥ : Subgroup Lˣ)}
    (hw : VOf.proj (bot_le : ⊥ ≤ constUnits l₀ L) w = 0) : w = 0 := by
  obtain ⟨N, c, hN, hc⟩ := exists_nsmul_eq_cls w
  obtain ⟨m, hm, hcm⟩ := exists_pow_eq_one_of_isAlgebraic_bot hL c.ne_zero
    (isAlgebraic_of_proj_eq_zero hl₀ hw hc)
  have hc0 : cls (⊥ : Subgroup Lˣ) (.ofMul c) = 0 :=
    (VOf.cls_eq_zero_iff c).2 ⟨m, hm, Subgroup.mem_bot.2 (Units.ext (by simpa using hcm))⟩
  rw [hc0, ← smul_zero N] at hc
  exact nsmul_left_cancel hN.ne' hc

/-- An element of `C_L` is `(1/N)[c]` with `c` algebraic over `l₀`. -/
theorem isAlgebraic_l₀_of_proj_eq_zero {w : VOf (⊥ : Subgroup Lˣ)}
    (hw : VOf.proj (bot_le : ⊥ ≤ constUnits l₀ L) w = 0) {N : ℕ} {c : Lˣ}
    (hc : N • w = cls ⊥ (.ofMul c)) : IsAlgebraic l₀ (c : L) :=
  isAlgebraic_algebraMap (⟨c, (hl₀ c).2 (isAlgebraic_of_proj_eq_zero hl₀ hw hc)⟩ : l₀)

/-- Blueprint 7.3, last step (characteristic `0`): let `s, t ∈ L^×` with `s + t = 1` and `s ∉ l₀`,
let `r ≠ 0`, and let `χ₁, χ₂ ∈ C_L`. If `{r[s] + χ₁, r[t] + χ₂} = 0` in `𝒦_2(L)`, then `χ₂ = 0`.
The proof applies the tame symbol of a valuation trivial on `l₀` and positive on `s`. -/
theorem eq_zero_of_tameSymbol {s t : Lˣ} (hst : (s : L) + t = 1) (hs : (s : L) ∉ l₀) {r : ℚ}
    (hr : r ≠ 0) {χ₁ χ₂ : VOf (⊥ : Subgroup Lˣ)}
    (h₁ : VOf.proj (bot_le : ⊥ ≤ constUnits l₀ L) χ₁ = 0)
    (h₂ : VOf.proj (bot_le : ⊥ ≤ constUnits l₀ L) χ₂ = 0)
    (h : ι ⊥ (r • cls ⊥ (.ofMul s) + χ₁) * ι ⊥ (r • cls ⊥ (.ofMul t) + χ₂) = 0) : χ₂ = 0 := by
  have hs' : Transcendental l₀ (s : L) := fun halg ↦
    hs (isRelAlgClosed_of_forall_mem_iff hl₀ _ halg)
  obtain ⟨A, hA, -, hv⟩ := exists_valuationSubring_of_transcendental hs'
  -- `v` vanishes on `C_L`
  have hval {w : VOf (⊥ : Subgroup Lˣ)} (hw : VOf.proj (bot_le : ⊥ ≤ constUnits l₀ L) w = 0) :
      val A w = 0 := by
    obtain ⟨N, c, hN, hc⟩ := exists_nsmul_eq_cls w
    apply nsmul_left_cancel hN.ne'
    rw [← map_nsmul, hc, smul_zero]
    exact val_cls_of_isAlgebraic A hA (isAlgebraic_l₀_of_proj_eq_zero hl₀ hw hc)
  obtain ⟨hvt, hut⟩ := val_unitPart_cls_one_sub A hv (eq_sub_of_add_eq' hst)
  have hvs := val_cls_ne_zero_of_valuation_lt_one A hv
  have hT := congrArg (tameSymbol A) h
  rw [tameSymbol_ι_mul_ι, map_zero] at hT
  simp only [map_add, map_smul, hval h₁, hval h₂, hvt, hut, smul_zero, add_zero, zero_add,
    TensorProduct.zero_tmul, sub_zero] at hT
  have hu : unitPart A χ₂ = 0 :=
    (tmul_eq_zero_iff.1 hT).resolve_left (smul_ne_zero hr hvs)
  -- `𝔲` is injective on `C_L`
  obtain ⟨N, c, hN, hc⟩ := exists_nsmul_eq_cls χ₂
  have hc0 : cls (⊥ : Subgroup Lˣ) (.ofMul c) = 0 := by
    rw [← unitPart_cls_eq_zero_iff_of_isAlgebraic' A hA
      (isAlgebraic_l₀_of_proj_eq_zero hl₀ h₂ hc), ← hc, map_nsmul, hu, smul_zero]
  rw [hc0, ← smul_zero N] at hc
  exact nsmul_left_cancel hN.ne' hc

variable {φ : MilnorKQ (⊥ : Subgroup Kˣ) →ₐ[ℚ] MilnorKQ (⊥ : Subgroup Lˣ)} (hφ : IsGraded φ)
include hφ

/-- Blueprint 7.3, last step: if `φ₁[x] = r[τ(x)]` holds in `V_{L|l₀}` for all `x`, it holds in
`L^×_ℚ`. -/
theorem degOne_cls_eq_of_proj (hK : ∃ x : K, Transcendental (⊥ : Subfield K) x) (τ : K →+* L)
    {r : ℚ} (hr : r ≠ 0)
    (hψ : ∀ x : Kˣ, VOf.proj (bot_le : ⊥ ≤ constUnits l₀ L) (degOne φ 〚x〛) =
      r • cls (constUnits l₀ L) (.ofMul (Units.map (τ : K →* L) x))) (x : Kˣ) :
    degOne φ 〚x〛 = r • cls ⊥ (.ofMul (Units.map (τ : K →* L) x)) := by
  -- `χ(x) = φ₁[x] - r[τ x] ∈ C_L`
  let χ : Additive Kˣ →+ VOf (⊥ : Subgroup Lˣ) :=
    ((degOne φ - r • VOf.mapRingHom τ bot_le).toAddMonoidHom).comp (cls ⊥)
  have hχ (x : Kˣ) : χ (.ofMul x) = degOne φ 〚x〛 - r • cls ⊥ (.ofMul (Units.map (τ : K →* L) x)) :=
    by simp [χ]
  have hχC (x : Kˣ) : VOf.proj (bot_le : ⊥ ≤ constUnits l₀ L) (χ (.ofMul x)) = 0 := by
    rw [hχ, map_sub, map_smul, proj_cls, hψ, sub_self]
  suffices hall : ∀ x : Kˣ, χ (.ofMul x) = 0 by
    rw [← sub_eq_zero, ← hχ]
    exact hall x
  by_cases hL : ringChar L ≠ 0
  · exact fun x ↦ proj_injective_of_ringChar_ne_zero hl₀ hL (hχC x)
  push Not at hL
  -- Step 1: `χ(y) = 0` if `x + y = 1` with `x ∉ k₀`
  have step1 (x y : Kˣ) (hxy : (x : K) + y = 1) (hx : ¬ IsAlgebraic (⊥ : Subfield K) (x : K)) :
      χ (.ofMul y) = 0 := by
    have hs : ((Units.map (τ : K →* L) x : Lˣ) : L) ∉ l₀ := by
      rw [hl₀, Units.coe_map, MonoidHom.coe_ofClass, isAlgebraic_bot_map_iff]
      exact hx
    have hst : ((Units.map (τ : K →* L) x : Lˣ) : L) + (Units.map (τ : K →* L) y : Lˣ) = 1 := by
      simp only [Units.coe_map, MonoidHom.coe_ofClass, ← map_add, hxy, map_one]
    refine eq_zero_of_tameSymbol hl₀ hst hs hr (hχC x) (hχC y) ?_
    rw [← sub_eq_iff_eq_add'.1 (hχ x).symm, ← sub_eq_iff_eq_add'.1 (hχ y).symm,
      ← hφ.apply_ι, ← hφ.apply_ι, ← map_mul, ι_mul_ι_eq_zero _ hxy, map_zero]
  -- Step 2: `χ(y) = 0` for `y ∉ k₀`
  have step2 (y : Kˣ) (hy : ¬ IsAlgebraic (⊥ : Subfield K) (y : K)) : χ (.ofMul y) = 0 := by
    have hx0 : (1 : K) - y ≠ 0 := fun h ↦ hy (by rw [← sub_eq_zero.1 h]; exact isAlgebraic_one)
    refine step1 (Units.mk0 _ hx0) y (by simp) fun h ↦ hy ?_
    rw [show (y : K) = 1 - (1 - y) by ring]
    exact isAlgebraic_one.sub h
  -- Step 3: `χ(y) = 0` for all `y`
  intro y
  by_cases hy : IsAlgebraic (⊥ : Subfield K) (y : K)
  · obtain ⟨z₀, hz₀⟩ := hK
    have hz₀0 : z₀ ≠ 0 := fun h ↦ hz₀ (h ▸ isAlgebraic_zero)
    let u₀ := Units.mk0 z₀ hz₀0
    have hyu : ¬ IsAlgebraic (⊥ : Subfield K) ((y * u₀ : Kˣ) : K) := fun h ↦ hz₀ (by
      have : z₀ = ((y * u₀ : Kˣ) : K) * (y : K)⁻¹ := by
        rw [Units.val_mul, Units.val_mk0, mul_comm (y : K), mul_assoc, mul_inv_cancel₀ y.ne_zero,
          mul_one]
      rw [this]
      exact h.mul (IsAlgebraic.inv_iff.2 hy))
    have := step2 _ hyu
    rw [ofMul_mul, map_add, step2 u₀ hz₀, add_zero] at this
    exact this
  · exact step2 y hy

end TheoremC

end MilnorAlgDep
