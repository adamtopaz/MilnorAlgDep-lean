module

public import MilnorAlgDep.Milnor.Basic
public import MilnorAlgDep.Milnor.Symbols

/-!
# Degree one parts of graded homomorphisms

Auxiliary material for Sections 7.2-7.4 of the blueprint.

## Main statements

* `not_vAlgIndep_of_ι_mul_ι_eq_zero`: the reformulation of Lemma 7.2(a) stated after its proof in
  the blueprint: if `{v, w} = 0` in `𝒦_2(L|l)`, then `v, w ∈ V_{L|l}` are algebraically dependent
  (or one of them is `0`).
* `MilnorKQ.not_vAlgIndep_of_isGraded`: for a graded `φ : 𝒦_*(K|k) → 𝒦_*(L|l)` and `x + y = 1`,
  the elements `φ₁ [x]`, `φ₁ [y]` are algebraically dependent (the argument for (A2) in the proof
  of Theorem B).
* `MilnorKQ.degOne_bijective`: a graded algebra isomorphism has a bijective degree one part.
* `MilnorKQ.eq_degScale_comp_map`: a graded homomorphism with `φ₁ [x] = r [τ x]` is
  `r^deg ∘ τ_*`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf MilnorKQ

/-- Blueprint, remark after Lemma 7.2: if `v, w ∈ V_{L|l}` satisfy `{v, w} = 0` in `𝒦_2(L|l)`,
then `v, w` are algebraically dependent over `l` (or one of them is `0`, which is included, as
algebraically independent elements are non-zero). -/
theorem not_vAlgIndep_of_ι_mul_ι_eq_zero {l L : Type*} [Field l] [Field L] [Algebra l L]
    {v w : V l L}
    (h : ι (constUnits l L) v * ι (constUnits l L) w = 0) : ¬ VAlgIndep l ![v, w] := by
  rintro ⟨N, a, -, ha, hind⟩
  have hind' : AlgebraicIndependent l ![(a 0 : L), (a 1 : L)] := by
    convert hind using 1
    ext i
    fin_cases i <;> rfl
  refine symbol_ne_zero_of_algebraicIndependent hind' ?_
  have h0 := ha 0
  have h1 := ha 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [symbol, ← h0, ← h1, map_nsmul, map_nsmul, smul_mul_smul_comm, h, smul_zero]

namespace MilnorKQ

variable {K L : Type*} [Field K] [Field L]

/-- Two algebra homomorphisms out of `MilnorKQ H` agreeing on all `ι [a]` are equal. -/
theorem algHom_ext_cls {H : Subgroup Lˣ} {A : Type*} [Ring A] [Algebra ℚ A]
    {f g : MilnorKQ H →ₐ[ℚ] A}
    (h : ∀ a : Lˣ, f (ι H (cls H (.ofMul a))) = g (ι H (cls H (.ofMul a)))) : f = g :=
  algHom_ext (VOf.linearMap_ext h)

section map

variable {H₀ : Subgroup Kˣ} {H : Subgroup Lˣ}

theorem degScale_comp_map_ι (τ : K →+* L) (h : H₀ ≤ H.comap (Units.map (τ : K →* L))) (r : ℚ)
    (v : VOf H₀) :
    (degScale H r).comp (map τ h) (ι H₀ v) = ι H (r • VOf.mapRingHom τ h v) := by
  rw [AlgHom.comp_apply, map_ι, degScale_ι, map_smul]

theorem isGraded_degScale_comp_map (τ : K →+* L) (h : H₀ ≤ H.comap (Units.map (τ : K →* L)))
    (r : ℚ) : IsGraded ((degScale H r).comp (map τ h)) :=
  (isGraded_degScale r).comp (isGraded_map τ h)

/-- Blueprint 7.2 (end of the proof of Theorem B): a graded homomorphism `φ` with
`φ₁ [x] = r [τ x]` for all `x` is `r^deg ∘ τ_*`, since both are algebra homomorphisms generated in
degree one. -/
theorem eq_degScale_comp_map {φ : MilnorKQ H₀ →ₐ[ℚ] MilnorKQ H} (hφ : IsGraded φ) (τ : K →+* L)
    (h : H₀ ≤ H.comap (Units.map (τ : K →* L))) (r : ℚ)
    (hφ₁ : ∀ x : Kˣ, degOne φ (cls H₀ (.ofMul x)) = r • cls H (.ofMul (Units.map (τ : K →* L) x))) :
    φ = (degScale H r).comp (map τ h) := by
  refine algHom_ext_cls fun a ↦ ?_
  rw [hφ.apply_ι, degScale_comp_map_ι, mapRingHom_cls, hφ₁]

end map

/-- Blueprint 7.2, proof of Theorem B, (A2): for a graded `φ : 𝒦_*(K|k) → 𝒦_*(L|l)` and units
`x, y` with `x + y = 1`, the elements `φ₁ [x]` and `φ₁ [y]` of `V_{L|l}` are algebraically
dependent (or one of them is `0`), because `{φ₁ [x], φ₁ [y]} = φ {x, y} = 0`. -/
theorem not_vAlgIndep_of_isGraded {H : Subgroup Kˣ} {l : Type*} [Field l] [Algebra l L]
    {φ : MilnorKQ H →ₐ[ℚ] MilnorKQ (constUnits l L)} (hφ : IsGraded φ)
    {x y : Kˣ} (hxy : (x : K) + y = 1) :
    ¬ VAlgIndep l ![degOne φ (cls H (.ofMul x)), degOne φ (cls H (.ofMul y))] := by
  apply not_vAlgIndep_of_ι_mul_ι_eq_zero
  rw [← hφ.apply_ι, ← hφ.apply_ι, ← map_mul, ι_mul_ι_eq_zero _ hxy, map_zero]

/-- A graded algebra isomorphism has a bijective degree one part (its inverse is graded by
`MilnorKQ.IsGraded.symm`). -/
theorem degOne_bijective {H : Subgroup Lˣ} {H' : Subgroup Kˣ}
    (φ : MilnorKQ H ≃ₐ[ℚ] MilnorKQ H') (hφ : IsGraded φ.toAlgHom) :
    Function.Bijective (degOne φ.toAlgHom) := by
  have hφsymm : IsGraded φ.symm.toAlgHom := hφ.symm
  have h1 : degOne φ.symm.toAlgHom ∘ₗ degOne φ.toAlgHom = LinearMap.id := by
    rw [← degOne_comp _ hφ]
    convert degOne_id (H := H)
    ext v
    simp
  have h2 : degOne φ.toAlgHom ∘ₗ degOne φ.symm.toAlgHom = LinearMap.id := by
    rw [← degOne_comp _ hφsymm]
    convert degOne_id (H := H')
    ext v
    simp
  refine ⟨Function.LeftInverse.injective (g := degOne φ.symm.toAlgHom) fun v ↦ ?_,
    Function.RightInverse.surjective (g := degOne φ.symm.toAlgHom) fun v ↦ ?_⟩
  · exact LinearMap.congr_fun h1 v
  · exact LinearMap.congr_fun h2 v

end MilnorKQ

end MilnorAlgDep
