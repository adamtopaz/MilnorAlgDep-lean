module

public import MilnorAlgDep.Milnor.Defs
public import MilnorAlgDep.TheoremA

/-!
# Theorem C (absolute version)

Blueprint, Theorem C (Section 1.2), proved in Section 7.3.

Let `K, L` be perfect fields, and let `k_0, l_0` be the algebraic closures of the prime fields in
`K` and `L`. Assume that `K ≠ k_0`. Let `φ : 𝒦_*(K) → 𝒦_*(L)` be a homomorphism of graded
`ℚ`-algebras such that `φ_1` is injective, the composition `K^× → 𝒦_1(L) → V_{L|l_0}` satisfies
(A3), and (A4) holds. Then there are a field embedding `τ : K → L` and `r ∈ ℚ^×` such that
`φ = r^deg ∘ τ_*`, and `τ⁻¹(l_0) = k_0`. The pair `(τ, r)` is unique up to
`(Frob^j ∘ τ, p^{-j} r)`.

## Encoding

* `𝒦_*(K)` is `MilnorKQ (⊥ : Subgroup Kˣ)`, the tensor algebra of `VOf ⊥ = K^× ⊗ ℚ` modulo the
  Steinberg relations (see `MilnorAlgDep.Milnor.Defs`).
* `k₀ : Subfield K` is characterized by `hk₀ : ∀ x, x ∈ k₀ ↔ IsAlgebraic (⊥ : Subfield K) x`,
  where `⊥ : Subfield K` is the prime field; similarly `l₀`.
* "`K ≠ k_0`" is `∃ x : K, Transcendental (⊥ : Subfield K) x`.
* "Homomorphism of graded `ℚ`-algebras" is an algebra homomorphism with `MilnorKQ.IsGraded φ`,
  `φ_1 = MilnorKQ.degOne φ`.
* The composition `K^× → 𝒦_1(L) → V_{L|l_0}` is `x ↦ VOf.proj _ (φ_1 [x])`, where
  `VOf.proj _ : VOf ⊥ → V l₀ L` is the projection `L^× ⊗ ℚ → (L^×/l_0^×) ⊗ ℚ`; (A3) and (A4) are
  encoded as in `theoremA_perfect`.
* `τ_* = MilnorKQ.map τ bot_le` and `r^deg = MilnorKQ.degScale _ r`.
* Uniqueness is `theoremC_unique`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf MilnorKQ

variable {K L : Type*} [Field K] [Field L]

/-- **Blueprint Theorem C** (absolute version). Let `K, L` be perfect fields, `k₀ ⊆ K` and
`l₀ ⊆ L` the relative algebraic closures of the prime fields, and assume `K ≠ k₀`. Let
`φ : 𝒦_*(K) → 𝒦_*(L)` be a homomorphism of graded `ℚ`-algebras such that `φ_1` is injective, the
composition `K^× → 𝒦_1(L) → V_{L|l₀}` satisfies (A3), and (A4) holds. Then there are a field
embedding `τ : K → L` and `r ∈ ℚ`, `r ≠ 0`, with `τ⁻¹(l₀) = k₀` and `φ = r^deg ∘ τ_*`. -/
theorem theoremC [PerfectField K] [PerfectField L]
    (k₀ : Subfield K) (hk₀ : ∀ x : K, x ∈ k₀ ↔ IsAlgebraic (⊥ : Subfield K) x)
    (l₀ : Subfield L) (hl₀ : ∀ x : L, x ∈ l₀ ↔ IsAlgebraic (⊥ : Subfield L) x)
    (hK : ∃ x : K, Transcendental (⊥ : Subfield K) x)
    (φ : MilnorKQ (⊥ : Subgroup Kˣ) →ₐ[ℚ] MilnorKQ (⊥ : Subgroup Lˣ)) (hφ : IsGraded φ)
    (hφ₁ : Function.Injective (degOne φ))
    (A3 : ∃ x : Fin (if ringChar L = 0 then 2 else 3) → Kˣ,
      VAlgIndep l₀ fun i ↦ VOf.proj (bot_le : ⊥ ≤ constUnits l₀ L) (degOne φ 〚x i〛))
    (A4 : ringChar L ≠ 0 → ringChar K ≠ 0) :
    ∃ (τ : K →+* L) (r : ℚ), r ≠ 0 ∧ (∀ x : K, τ x ∈ l₀ ↔ x ∈ k₀) ∧
      φ = (degScale (⊥ : Subgroup Lˣ) r).comp (map τ bot_le) := by
  sorry

/-- **Blueprint Theorem C, uniqueness.** If `r^deg ∘ τ_* = r'^deg ∘ τ'_*` as maps
`𝒦_*(K) → 𝒦_*(L)` for field embeddings `τ, τ' : K → L` and `r, r' ≠ 0`, and `K` contains an
element transcendental over the prime field, then `τ' = Frob^j ∘ τ` and `r' = p^{-j} r` for some
`j ∈ ℤ`, where `p = ringExpChar L` and `Frob = frobeniusEquiv L p` (so `τ' = τ`, `r' = r` in
characteristic `0`). Only `L` needs to be perfect. -/
theorem theoremC_unique [PerfectField L] (hK : ∃ x : K, Transcendental (⊥ : Subfield K) x)
    (τ τ' : K →+* L) (r r' : ℚ) (hr : r ≠ 0) (hr' : r' ≠ 0)
    (h : (degScale (⊥ : Subgroup Lˣ) r).comp (map τ bot_le) =
      (degScale (⊥ : Subgroup Lˣ) r').comp (map τ' bot_le)) :
    ∃ j : ℤ, τ' = ((frobeniusEquiv L (ringExpChar L) ^ j : L ≃+* L) : L →+* L).comp τ ∧
      r' = (ringExpChar L : ℚ) ^ (-j) * r := by
  sorry

end MilnorAlgDep
