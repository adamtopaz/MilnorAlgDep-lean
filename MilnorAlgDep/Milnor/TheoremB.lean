module

public import MilnorAlgDep.Milnor.DegOne
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
  have : IsRelAlgClosed k K := IsRelAlgClosed.of_subfield hk
  have : IsRelAlgClosed l L := IsRelAlgClosed.of_subfield hl
  -- `ψ = φ₁ ∘ [·] : Kˣ → V_{L|l}`
  let ψ : Additive Kˣ →+ V l L := (degOne φ).toAddMonoidHom.comp (cls _)
  have hψ (x : Kˣ) : ψ (.ofMul x) = degOne φ 〚x〛 := rfl
  -- (A1), from the injectivity of `φ₁` and (V1)
  have A1 (x : Kˣ) : ψ (.ofMul x) = 0 ↔ (x : K) ∈ k := by
    rw [hψ, ← map_zero (degOne φ), hφ₁.eq_iff, V.cls_eq_zero_iff, mem_constUnits_subfield]
  -- (A2), from `φ {x, 1 - x} = 0` and Lemma 7.2(a)
  have A2 (x y : Kˣ) (hxy : (x : K) + y = 1) (_ : (x : K) ∉ k) :
      ¬ VAlgIndep l ![ψ (.ofMul x), ψ (.ofMul y)] :=
    not_vAlgIndep_of_isGraded hφ hxy
  obtain ⟨-, -, τ, r, hr, hτ, hψτ⟩ := theoremA_perfect k l hl ψ A1 A2 A3 A4
  exact ⟨τ, hτ, r, hr, eq_degScale_comp_map hφ τ _ r hψτ⟩

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
  -- The hypothesis `r' ≠ 0` is not needed (it follows from the others).
  have _ := hr'
  have : IsRelAlgClosed l L := IsRelAlgClosed.of_subfield hl
  set F := (degScale (constUnits l L) r).comp (map τ (constUnits_le_comap fun x hx ↦ (hτ x).2 hx))
  let ψ : Additive Kˣ →+ V l L := (degOne F).toAddMonoidHom.comp (cls _)
  have h₁ (x : Kˣ) : ψ (.ofMul x) = r • 〚Units.map (τ : K →* L) x〛 := by
    change degOne F _ = _
    rw [degOne_degScale_comp_map, LinearMap.smul_apply, mapRingHom_cls]
  have h₂ (x : Kˣ) : ψ (.ofMul x) = r' • 〚Units.map (τ' : K →* L) x〛 := by
    change degOne F _ = _
    rw [h, degOne_degScale_comp_map, LinearMap.smul_apply, mapRingHom_cls]
  have hψ : ψ ≠ 0 := by
    obtain ⟨x, hx⟩ := hkK
    have hx0 : x ≠ 0 := fun h0 ↦ hx (h0 ▸ k.zero_mem)
    intro h0
    have h0x := DFunLike.congr_fun h0 (.ofMul (Units.mk0 x hx0))
    rw [h₁, AddMonoidHom.zero_apply, smul_eq_zero, V.cls_eq_zero_iff,
      mem_constUnits_subfield] at h0x
    exact h0x.elim hr fun h ↦ hx ((hτ x).1 h)
  exact theoremA_perfect_unique l hl ψ hψ τ τ' r r' h₁ h₂

end MilnorAlgDep
