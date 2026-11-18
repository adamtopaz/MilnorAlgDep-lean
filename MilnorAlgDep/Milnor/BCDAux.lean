module

public import MilnorAlgDep.Milnor.Defs

/-!
# Basic facts on rational Milnor K-rings used in Theorems B, C, D

Auxiliary material for Section 7 of the blueprint: graded homomorphisms are determined by their
degree one part, `φ ∘ ι = ι ∘ φ₁` for graded `φ`, and the degree one parts of `τ_*`, `r^deg` and
of compositions.

All of this duplicates (part of) the work package WP-K12 (`MilnorAlgDep/Milnor/Basic.lean`) and
should be replaced by it once it has landed.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

variable {K L M : Type*} [Field K] [Field L] [Field M]

namespace MilnorKQ

-- TODO(move): everything in this file belongs to `MilnorAlgDep/Milnor/Basic.lean` (WP-K12).

variable {H : Subgroup Lˣ} {H' : Subgroup Kˣ} {H'' : Subgroup Mˣ}

variable (H) in
theorem grade_one : grade H 1 = LinearMap.range (ι H) :=
  pow_one _

/-- Two algebra homomorphisms out of `MilnorKQ H` agreeing on all `ι [a]` are equal. -/
theorem algHom_ext_cls {A : Type*} [Ring A] [Algebra ℚ A] {f g : MilnorKQ H →ₐ[ℚ] A}
    (h : ∀ a : Lˣ, f (ι H (cls H (.ofMul a))) = g (ι H (cls H (.ofMul a)))) : f = g :=
  algHom_ext (VOf.linearMap_ext h)

/-- A graded homomorphism satisfies `φ ∘ ι = ι ∘ φ₁`. -/
theorem IsGraded.map_ι {φ : MilnorKQ H →ₐ[ℚ] MilnorKQ H'} (hφ : IsGraded φ) (v : VOf H) :
    φ (ι H v) = ι H' (degOne φ v) := by
  have hmem : φ (ι H v) ∈ grade H' 1 := hφ 1 ⟨ι H v, ι_mem_grade_one H v, rfl⟩
  rw [grade_one] at hmem
  obtain ⟨w, hw⟩ := hmem
  simp only [degOne, LinearMap.comp_apply, AlgHom.toLinearMap_apply, ← hw, π₁_ι]

/-- An algebra homomorphism mapping degree one into degree one is graded. -/
theorem isGraded_of_forall_mem_range {φ : MilnorKQ H →ₐ[ℚ] MilnorKQ H'}
    (h : ∀ v, φ (ι H v) ∈ LinearMap.range (ι H')) : IsGraded φ := by
  intro n
  rw [grade, grade, Submodule.map_pow]
  refine pow_le_pow_left' ?_ n
  rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
  exact h v

/-- An algebra homomorphism with `φ ∘ ι = ι ∘ f` is graded, with degree one part `f`. -/
theorem degOne_eq_of_map_ι {φ : MilnorKQ H →ₐ[ℚ] MilnorKQ H'} {f : VOf H →ₗ[ℚ] VOf H'}
    (h : ∀ v, φ (ι H v) = ι H' (f v)) : degOne φ = f := by
  ext v
  simp only [degOne, LinearMap.comp_apply, AlgHom.toLinearMap_apply, h, π₁_ι]

theorem isGraded_of_map_ι {φ : MilnorKQ H →ₐ[ℚ] MilnorKQ H'} {f : VOf H →ₗ[ℚ] VOf H'}
    (h : ∀ v, φ (ι H v) = ι H' (f v)) : IsGraded φ :=
  isGraded_of_forall_mem_range fun v ↦ ⟨f v, (h v).symm⟩

theorem IsGraded.comp {φ : MilnorKQ H →ₐ[ℚ] MilnorKQ H'} {ψ : MilnorKQ H' →ₐ[ℚ] MilnorKQ H''}
    (hψ : IsGraded ψ) (hφ : IsGraded φ) : IsGraded (ψ.comp φ) :=
  isGraded_of_map_ι (f := degOne ψ ∘ₗ degOne φ) fun v ↦ by
    rw [AlgHom.comp_apply, hφ.map_ι, hψ.map_ι, LinearMap.comp_apply]

/-- `φ₁` is functorial for graded homomorphisms (only `φ` needs to be graded). -/
theorem degOne_comp {φ : MilnorKQ H →ₐ[ℚ] MilnorKQ H'} {ψ : MilnorKQ H' →ₐ[ℚ] MilnorKQ H''}
    (hφ : IsGraded φ) : degOne (ψ.comp φ) = degOne ψ ∘ₗ degOne φ := by
  ext v
  change π₁ H'' (ψ (φ (ι H v))) = π₁ H'' (ψ (ι H' (degOne φ v)))
  rw [hφ.map_ι]

@[simp]
theorem degOne_id : degOne (AlgHom.id ℚ (MilnorKQ H)) = LinearMap.id :=
  degOne_eq_of_map_ι fun _ ↦ rfl

theorem isGraded_id : IsGraded (AlgHom.id ℚ (MilnorKQ H)) :=
  isGraded_of_map_ι (f := LinearMap.id) fun _ ↦ rfl

section map

variable {H₀ : Subgroup Kˣ}

theorem degOne_map (τ : K →+* L) (h : H₀ ≤ H.comap (Units.map (τ : K →* L))) :
    degOne (map τ h) = VOf.mapRingHom τ h :=
  degOne_eq_of_map_ι (map_ι τ h)

theorem isGraded_map (τ : K →+* L) (h : H₀ ≤ H.comap (Units.map (τ : K →* L))) :
    IsGraded (map τ h) :=
  isGraded_of_map_ι (map_ι τ h)

variable (H) in
theorem degOne_degScale (r : ℚ) : degOne (degScale H r) = r • LinearMap.id :=
  degOne_eq_of_map_ι fun v ↦ by
    rw [degScale_ι, LinearMap.smul_apply, LinearMap.id_apply, map_smul]

variable (H) in
theorem isGraded_degScale (r : ℚ) : IsGraded (degScale H r) :=
  isGraded_of_map_ι (f := r • LinearMap.id) fun v ↦ by
    rw [degScale_ι, LinearMap.smul_apply, LinearMap.id_apply, map_smul]

theorem degScale_comp_map_ι (τ : K →+* L) (h : H₀ ≤ H.comap (Units.map (τ : K →* L))) (r : ℚ)
    (v : VOf H₀) :
    (degScale H r).comp (map τ h) (ι H₀ v) = ι H (r • VOf.mapRingHom τ h v) := by
  rw [AlgHom.comp_apply, map_ι, degScale_ι, map_smul]

theorem degOne_degScale_comp_map (τ : K →+* L) (h : H₀ ≤ H.comap (Units.map (τ : K →* L)))
    (r : ℚ) : degOne ((degScale H r).comp (map τ h)) = r • VOf.mapRingHom τ h :=
  degOne_eq_of_map_ι fun v ↦ by rw [degScale_comp_map_ι, LinearMap.smul_apply]

theorem isGraded_degScale_comp_map (τ : K →+* L) (h : H₀ ≤ H.comap (Units.map (τ : K →* L)))
    (r : ℚ) : IsGraded ((degScale H r).comp (map τ h)) :=
  (isGraded_degScale H r).comp (isGraded_map τ h)

/-- Blueprint 7.2 (end of the proof of Theorem B): a graded homomorphism `φ` with
`φ₁ [x] = r [τ x]` for all `x` is `r^deg ∘ τ_*`, since both are algebra homomorphisms generated in
degree one. -/
theorem eq_degScale_comp_map {φ : MilnorKQ H₀ →ₐ[ℚ] MilnorKQ H} (hφ : IsGraded φ) (τ : K →+* L)
    (h : H₀ ≤ H.comap (Units.map (τ : K →* L))) (r : ℚ)
    (hφ₁ : ∀ x : Kˣ, degOne φ (cls H₀ (.ofMul x)) = r • cls H (.ofMul (Units.map (τ : K →* L) x))) :
    φ = (degScale H r).comp (map τ h) := by
  refine algHom_ext_cls fun a ↦ ?_
  rw [hφ.map_ι, degScale_comp_map_ι, mapRingHom_cls, hφ₁]

end map

end MilnorKQ

end MilnorAlgDep
