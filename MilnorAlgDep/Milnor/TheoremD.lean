module

public import MilnorAlgDep.Milnor.Defs
public import MilnorAlgDep.TheoremA

/-!
# Theorem D (isomorphisms)

Blueprint, Theorem D (Section 1.2), proved in Section 7.4.

Let `K` and `L` be fields each of which contains three elements that are algebraically
independent over the prime field; if one of them has characteristic `0`, two such elements
suffice. Then every isomorphism of graded `ℚ`-algebras `φ : 𝒦_*(K) → 𝒦_*(L)` is of the form
`r^deg ∘ τ_*` for an isomorphism of fields `τ : K^i → L^i` and some `r ∈ ℚ^×`. In particular
`K^i ≅ L^i`.

## Encoding

* The fields are arbitrary (not assumed perfect). The hypothesis on transcendence degrees is: with
  `d = 2` if `ringChar K = 0` or `ringChar L = 0`, and `d = 3` otherwise, both `K` and `L` contain
  a family `Fin d → _` algebraically independent over the prime field `⊥ : Subfield _`.
* `𝒦_*(K) = MilnorKQ (⊥ : Subgroup Kˣ)` (see `MilnorAlgDep.Milnor.Defs`). "Isomorphism of graded
  `ℚ`-algebras" is a `ℚ`-algebra isomorphism `φ` such that both `φ` and `φ⁻¹` are graded
  (`MilnorKQ.IsGraded`).
* `K^i` is any perfect closure of `K` in the sense of Mathlib: a perfect field `Ki` with
  `[Algebra K Ki]` and `IsPerfectClosure (algebraMap K Ki) pK`, where `pK` is the exponential
  characteristic of `K` (pinned down by `[ExpChar K pK]`); similarly `L^i`, with its own `pL`
  (that `pK = pL` is part of the conclusion, since `K^i ≅ L^i`).
* Since `φ` is a map `𝒦_*(K) → 𝒦_*(L)`, "`φ = r^deg ∘ τ_*`" is read through the maps
  `𝒦_*(K) → 𝒦_*(K^i)` and `𝒦_*(L) → 𝒦_*(L^i)` induced by the inclusions (both are isomorphisms,
  as `𝒦_*` does not change under purely inseparable extensions): the square
  `𝒦_*(K) → 𝒦_*(L) → 𝒦_*(L^i)` equals `𝒦_*(K) → 𝒦_*(K^i) → 𝒦_*(L^i)`, the last map being
  `r^deg ∘ τ_*`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf MilnorKQ

variable {K L : Type*} [Field K] [Field L]

/-- **Blueprint Theorem D** (isomorphisms). Let `K` and `L` be fields each containing `d`
elements algebraically independent over the prime field, where `d = 2` if one of them has
characteristic `0` and `d = 3` otherwise. Let `φ : 𝒦_*(K) ≅ 𝒦_*(L)` be an isomorphism of graded
`ℚ`-algebras, and let `K^i`, `L^i` be perfect closures. Then there are a field isomorphism
`τ : K^i ≅ L^i` and `r ∈ ℚ`, `r ≠ 0`, such that `φ` corresponds to `r^deg ∘ τ_*` under the maps
`𝒦_*(K) → 𝒦_*(K^i)` and `𝒦_*(L) → 𝒦_*(L^i)` induced by the inclusions. -/
theorem theoremD
    (hK : ∃ x : Fin (if ringChar K = 0 ∨ ringChar L = 0 then 2 else 3) → K,
      AlgebraicIndependent (⊥ : Subfield K) x)
    (hL : ∃ x : Fin (if ringChar K = 0 ∨ ringChar L = 0 then 2 else 3) → L,
      AlgebraicIndependent (⊥ : Subfield L) x)
    (φ : MilnorKQ (⊥ : Subgroup Kˣ) ≃ₐ[ℚ] MilnorKQ (⊥ : Subgroup Lˣ))
    (hφ : IsGraded φ.toAlgHom) (hφsymm : IsGraded φ.symm.toAlgHom)
    (pK : ℕ) [ExpChar K pK] (Ki : Type*) [Field Ki] [Algebra K Ki] [ExpChar Ki pK]
    [PerfectRing Ki pK] [IsPerfectClosure (algebraMap K Ki) pK]
    (pL : ℕ) [ExpChar L pL] (Li : Type*) [Field Li] [Algebra L Li] [ExpChar Li pL]
    [PerfectRing Li pL] [IsPerfectClosure (algebraMap L Li) pL] :
    ∃ (τ : Ki ≃+* Li) (r : ℚ), r ≠ 0 ∧
      (map (algebraMap L Li) bot_le).comp φ.toAlgHom =
        ((degScale (⊥ : Subgroup Liˣ) r).comp (map (τ : Ki →+* Li) bot_le)).comp
          (map (algebraMap K Ki) bot_le) := by
  sorry

end MilnorAlgDep
