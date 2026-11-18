module

public import MilnorAlgDep.Milnor.Defs
public import MilnorAlgDep.TheoremA

/-!
# Theorem B (relative version)

Blueprint, Theorem B (Section 1.2), proved in Section 7.2.

Let `K, L` be perfect fields with relatively algebraically closed subfields `k, l`, and let
`φ : 𝒦_*(K|k) → 𝒦_*(L|l)` be a homomorphism of graded `ℚ`-algebras. Assume that `φ_1` is
injective, that `ψ = φ_1 ∘ [·]` satisfies (A3), and that (A4) holds. Then there are a field
embedding `τ : K → L` with `τ⁻¹(l) = k` and `r ∈ ℚ^×` such that `φ = r^deg ∘ τ_*`. The pair
`(τ, r)` is unique up to `(Frob^j ∘ τ, p^{-j} r)`.

## Encoding

* `𝒦_*(K|k)` is `MilnorKQ (constUnits k K)` (see `MilnorAlgDep.Milnor.Defs`): the tensor algebra
  of `V_{K|k}` modulo the Steinberg relations.
* "Homomorphism of graded `ℚ`-algebras" is a `ℚ`-algebra homomorphism `φ` with
  `MilnorKQ.IsGraded φ` (it maps degree `n` into degree `n`).
* `φ_1 = MilnorKQ.degOne φ = π₁ ∘ φ ∘ ι : V_{K|k} → V_{L|l}`, and `ψ(x) = φ_1 [x]`.
* (A3) and (A4) are encoded as in `theoremA_perfect` (`d = if ringChar L = 0 then 2 else 3`).
* `τ_* = MilnorKQ.map τ _`, which needs `τ(kˣ) ⊆ lˣ`; this is obtained from `τ⁻¹(l) = k`
  (`hτ`) by `constUnits_le_comap`. `r^deg = MilnorKQ.degScale _ r`.
* Uniqueness is `theoremB_unique`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf MilnorKQ

variable {K L : Type*} [Field K] [Field L]

/-- **Blueprint Theorem B** (relative version). Let `K, L` be perfect fields, `k ⊆ K`, `l ⊆ L`
relatively algebraically closed subfields, and `φ : 𝒦_*(K|k) → 𝒦_*(L|l)` a homomorphism of graded
`ℚ`-algebras such that `φ_1` is injective, `ψ = φ_1 ∘ [·]` satisfies (A3), and (A4) holds. Then
there are a field embedding `τ : K → L` with `τ⁻¹(l) = k` and `r ∈ ℚ`, `r ≠ 0`, with
`φ = r^deg ∘ τ_*`. -/
theorem theoremB [PerfectField K] [PerfectField L] (k : Subfield K) (l : Subfield L)
    (hk : ∀ x : K, IsAlgebraic k x → x ∈ k) (hl : ∀ x : L, IsAlgebraic l x → x ∈ l)
    (φ : MilnorKQ (constUnits k K) →ₐ[ℚ] MilnorKQ (constUnits l L)) (hφ : IsGraded φ)
    (hφ₁ : Function.Injective (degOne φ))
    (A3 : ∃ x : Fin (if ringChar L = 0 then 2 else 3) → Kˣ,
      VAlgIndep l fun i ↦ degOne φ 〚x i〛)
    (A4 : ringChar L ≠ 0 → ringChar K ≠ 0) :
    ∃ (τ : K →+* L) (hτ : ∀ x : K, τ x ∈ l ↔ x ∈ k) (r : ℚ), r ≠ 0 ∧
      φ = (degScale (constUnits l L) r).comp
        (map τ (constUnits_le_comap fun x hx ↦ (hτ x).2 hx)) := by
  sorry

/-- **Blueprint Theorem B, uniqueness.** If `r^deg ∘ τ_* = r'^deg ∘ τ'_*` for field embeddings
`τ, τ' : K → L` with `τ⁻¹(l) = τ'⁻¹(l) = k ≠ K` and `r, r' ≠ 0`, then `τ' = Frob^j ∘ τ` and
`r' = p^{-j} r` for some `j ∈ ℤ`, where `p = ringExpChar L` and `Frob = frobeniusEquiv L p`
(so `τ' = τ`, `r' = r` in characteristic `0`). Only `L` needs to be perfect. -/
theorem theoremB_unique [PerfectField L] (k : Subfield K) (l : Subfield L)
    (hl : ∀ x : L, IsAlgebraic l x → x ∈ l) (hkK : ∃ x : K, x ∉ k)
    (τ τ' : K →+* L) (hτ : ∀ x : K, τ x ∈ l ↔ x ∈ k) (hτ' : ∀ x : K, τ' x ∈ l ↔ x ∈ k)
    (r r' : ℚ) (hr : r ≠ 0) (hr' : r' ≠ 0)
    (h : (degScale (constUnits l L) r).comp (map τ (constUnits_le_comap fun x hx ↦ (hτ x).2 hx)) =
      (degScale (constUnits l L) r').comp (map τ' (constUnits_le_comap fun x hx ↦ (hτ' x).2 hx))) :
    ∃ j : ℤ, τ' = ((frobeniusEquiv L (ringExpChar L) ^ j : L ≃+* L) : L →+* L).comp τ ∧
      r' = (ringExpChar L : ℚ) ^ (-j) * r := by
  sorry

end MilnorAlgDep
