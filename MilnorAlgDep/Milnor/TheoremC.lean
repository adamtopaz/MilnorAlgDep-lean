module

public import MilnorAlgDep.Milnor.LiftC
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
* The blueprint assumes `K` and `L` perfect; only `L` is assumed perfect here (`theoremA_perfect`
  allows any `K`).
* Uniqueness is `theoremC_unique`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf MilnorKQ

variable {K L : Type*} [Field K] [Field L]

/-- **Blueprint Theorem C** (absolute version). Let `K` be a field, `L` a perfect field (the
blueprint also assumes `K` perfect; this is not needed), `k₀ ⊆ K` and `l₀ ⊆ L` the relative
algebraic closures of the prime fields, and assume `K ≠ k₀`. Let
`φ : 𝒦_*(K) → 𝒦_*(L)` be a homomorphism of graded `ℚ`-algebras such that `φ_1` is injective, the
composition `K^× → 𝒦_1(L) → V_{L|l₀}` satisfies (A3), and (A4) holds. Then there are a field
embedding `τ : K → L` and `r ∈ ℚ`, `r ≠ 0`, with `τ⁻¹(l₀) = k₀` and `φ = r^deg ∘ τ_*`. -/
theorem theoremC [PerfectField L]
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
  have hrel := isRelAlgClosed_of_forall_mem_iff hl₀
  -- `ψ : Kˣ → V_{L|l₀}`, `k' = {0} ∪ ker ψ` (a subfield by Lemma 7.3)
  let ψ := TheoremC.psi l₀ φ
  have hkey (z y : Kˣ) (hzy : (z : K) + y = 1) (hz : ψ (.ofMul z) = 0) : ψ (.ofMul y) = 0 :=
    TheoremC.psi_eq_zero_of_add_eq_one hl₀ hφ hφ₁ A3 A4 hK hzy hz
  let k' := subfieldOfKer ψ hkey
  -- (A1) and (A2) for `ψ` and `k'`; (A2) is (`eq:dep`)
  have A1 (x : Kˣ) : ψ (.ofMul x) = 0 ↔ (x : K) ∈ k' := (mem_subfieldOfKer ψ hkey).symm
  have A2 (x y : Kˣ) (hxy : (x : K) + y = 1) (_ : (x : K) ∉ k') :
      ¬ VAlgIndep l₀ ![ψ (.ofMul x), ψ (.ofMul y)] :=
    TheoremC.not_vAlgIndep_psi hl₀ hφ hxy
  obtain ⟨-, -, τ, r, hr, -, hψτ⟩ := theoremA_perfect k' l₀ hrel ψ A1 A2 A3 A4
  -- `τ⁻¹(l₀) = k₀` (so `k' = k₀`), since `τ` preserves and reflects algebraicity over the prime
  -- field
  have hτ₀ (x : K) : τ x ∈ l₀ ↔ x ∈ k₀ := by rw [hl₀, hk₀, isAlgebraic_bot_map_iff]
  -- lift `φ₁ [x] = r [τ x]` from `V_{L|l₀}` to `L^×_ℚ` and conclude as in Theorem B
  exact ⟨τ, r, hr, hτ₀, eq_degScale_comp_map hφ τ bot_le r
    (TheoremC.degOne_cls_eq_of_proj hl₀ hφ hK τ hr hψτ)⟩

/-- **Blueprint Theorem C, uniqueness.** If `r^deg ∘ τ_* = r'^deg ∘ τ'_*` as maps
`𝒦_*(K) → 𝒦_*(L)` for field embeddings `τ, τ' : K → L` and `r ≠ 0`, and `K` contains an
element transcendental over the prime field, then `τ' = Frob^j ∘ τ` and `r' = p^{-j} r` for some
`j ∈ ℤ`, where `p = ringExpChar L` and `Frob = frobeniusEquiv L p` (so `τ' = τ`, `r' = r` in
characteristic `0`). Only `L` needs to be perfect, and `r' ≠ 0` is not assumed (it follows from
`r' = p^{-j} r`). -/
theorem theoremC_unique [PerfectField L] (hK : ∃ x : K, Transcendental (⊥ : Subfield K) x)
    (τ τ' : K →+* L) (r r' : ℚ) (hr : r ≠ 0)
    (h : (degScale (⊥ : Subgroup Lˣ) r).comp (map τ bot_le) =
      (degScale (⊥ : Subgroup Lˣ) r').comp (map τ' bot_le)) :
    ∃ j : ℤ, τ' = ((frobeniusEquiv L (ringExpChar L) ^ j : L ≃+* L) : L →+* L).comp τ ∧
      r' = (ringExpChar L : ℚ) ^ (-j) * r := by
  -- Apply the uniqueness in Theorem A to `ψ : Kˣ → V_{L|l₀}`, `l₀ = primeAlgClosure L`.
  have : IsRelAlgClosed (primeAlgClosure L) L :=
    IsRelAlgClosed.of_subfield isRelAlgClosed_primeAlgClosure
  set F := (degScale (⊥ : Subgroup Lˣ) r).comp (map τ bot_le)
  let ψ : Additive Kˣ →+ V (primeAlgClosure L) L :=
    (VOf.proj bot_le ∘ₗ degOne F).toAddMonoidHom.comp (cls ⊥)
  have h₁ (x : Kˣ) : ψ (.ofMul x) = r • 〚Units.map (τ : K →* L) x〛 := by
    change VOf.proj _ (degOne F _) = _
    rw [degOne_degScale_comp_map, LinearMap.smul_apply, mapRingHom_cls, map_smul, proj_cls]
  have h₂ (x : Kˣ) : ψ (.ofMul x) = r' • 〚Units.map (τ' : K →* L) x〛 := by
    change VOf.proj _ (degOne F _) = _
    rw [h, degOne_degScale_comp_map, LinearMap.smul_apply, mapRingHom_cls, map_smul, proj_cls]
  have hψ : ψ ≠ 0 := by
    obtain ⟨x, hx⟩ := hK
    have hx0 : x ≠ 0 := fun h0 ↦ hx (h0 ▸ isAlgebraic_zero)
    intro h0
    have h0x := DFunLike.congr_fun h0 (.ofMul (Units.mk0 x hx0))
    rw [h₁, AddMonoidHom.zero_apply, smul_eq_zero, V.cls_eq_zero_iff, mem_constUnits_subfield,
      Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0, mem_primeAlgClosure,
      isAlgebraic_bot_map_iff] at h0x
    exact h0x.elim hr hx
  exact theoremA_perfect_unique _ isRelAlgClosed_primeAlgClosure ψ hψ τ τ' r r' h₁ h₂

end MilnorAlgDep
