module

public import MilnorAlgDep.Milnor.Basic
public import Mathlib.FieldTheory.IsPerfectClosure

/-!
# `𝒦_*` does not change under purely inseparable extensions

Blueprint Section 1.2 ("this is harmless, because `𝒦_*` does not change under purely inseparable
extensions") and Section 7.4 ("We may replace `K, L` by their perfect closures").

Let `M / K` be a field extension of exponential characteristic `p` which is `p`-radical (for
instance `M` a perfect closure of `K`: Mathlib's `IsPerfectClosure (algebraMap K M) p`). Then the
map `K^×_ℚ → M^×_ℚ` induced by the inclusion is bijective (`ℚ ⊗ -` kills `p`-power torsion and
cotorsion), and the induced homomorphism `𝒦_*(K) → 𝒦_*(M)` is an isomorphism of graded
`ℚ`-algebras: its inverse sends `ι v` to `ι (e⁻¹ v)`, which respects the Steinberg relations since
`a + b = 1` in `M` implies `a^{p^m} + b^{p^m} = 1` with `a^{p^m}, b^{p^m} ∈ K`.

## Main definitions

* `MilnorKQ.perfectClosureEquiv K M p : 𝒦_*(K) ≃ₐ[ℚ] 𝒦_*(M)`, whose underlying homomorphism is
  `MilnorKQ.map (algebraMap K M) bot_le` (`perfectClosureEquiv_toAlgHom`).

## Main statements

* `VOf.mapRingHom_algebraMap_bijective`: `K^×_ℚ → M^×_ℚ` is bijective.
* `MilnorKQ.isGraded_perfectClosureEquiv`, `MilnorKQ.isGraded_perfectClosureEquiv_symm`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf MilnorKQ

variable (K M : Type*) [Field K] [Field M] [Algebra K M] (p : ℕ) [ExpChar M p]
  [IsPRadical (algebraMap K M) p]

omit [ExpChar M p] in
/-- Every element of `M` has a `p ^ m`-th power in `K`, and so do all its `p ^ m'`-th powers for
`m' ≥ m`. -/
theorem exists_pow_eq_algebraMap_of_le (a : M) : ∃ m₀ : ℕ, ∀ m, m₀ ≤ m →
    ∃ x : K, algebraMap K M x = a ^ p ^ m := by
  obtain ⟨m₀, x, hx⟩ := IsPRadical.pow_mem (algebraMap K M) p a
  refine ⟨m₀, fun m hm ↦ ⟨x ^ p ^ (m - m₀), ?_⟩⟩
  rw [map_pow, hx, ← pow_mul, ← pow_add, Nat.add_sub_cancel' hm]

namespace VOf

include p in
/-- The map `K^×_ℚ → M^×_ℚ` induced by the inclusion is bijective if `M / K` is `p`-radical. -/
theorem mapRingHom_algebraMap_bijective :
    Function.Bijective (VOf.mapRingHom (algebraMap K M) bot_le :
      VOf (⊥ : Subgroup Kˣ) →ₗ[ℚ] VOf (⊥ : Subgroup Mˣ)) := by
  set f : VOf (⊥ : Subgroup Kˣ) →ₗ[ℚ] VOf (⊥ : Subgroup Mˣ) :=
    VOf.mapRingHom (algebraMap K M) bot_le with hf
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
    obtain ⟨n, a, hn, ha⟩ := exists_nsmul_eq_cls v
    have h0 : f (n • v) = 0 := by
      rw [map_nsmul, hv, smul_zero]
    rw [ha, hf, mapRingHom_cls, VOf.cls_eq_zero_iff] at h0
    obtain ⟨k, hk, hmem⟩ := h0
    have hak : a ^ k = 1 := by
      rw [Subgroup.mem_bot, ← map_pow] at hmem
      exact Units.map_injective (algebraMap K M).injective (hmem.trans (map_one _).symm)
    have hcls : cls (⊥ : Subgroup Kˣ) (.ofMul a) = 0 :=
      (VOf.cls_eq_zero_iff a).2 ⟨k, hk, Subgroup.mem_bot.2 hak⟩
    rw [hcls, ← smul_zero n] at ha
    exact nsmul_left_cancel hn.ne' ha
  · intro w
    obtain ⟨n, b, hn, hb⟩ := exists_nsmul_eq_cls w
    obtain ⟨m, x, hx⟩ := IsPRadical.pow_mem (algebraMap K M) p (b : M)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact pow_ne_zero _ b.ne_zero hx.symm
    have hu : Units.map (algebraMap K M : K →* M) (Units.mk0 x hx0) = b ^ (p ^ m) :=
      Units.ext (by simp [hx])
    have hne : ((p ^ m * n : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ (expChar_ne_zero M p)) hn.ne')
    refine ⟨((p ^ m * n : ℕ) : ℚ)⁻¹ • cls ⊥ (.ofMul (Units.mk0 x hx0)), ?_⟩
    rw [map_smul, hf, mapRingHom_cls, hu, cls_pow, ← hb, smul_smul, ← Nat.cast_smul_eq_nsmul ℚ,
      smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- The isomorphism `K^×_ℚ ≅ M^×_ℚ` for a `p`-radical extension `M / K`. -/
noncomputable def perfectClosureLinearEquiv :
    VOf (⊥ : Subgroup Kˣ) ≃ₗ[ℚ] VOf (⊥ : Subgroup Mˣ) :=
  LinearEquiv.ofBijective _ (mapRingHom_algebraMap_bijective K M p)

@[simp]
theorem perfectClosureLinearEquiv_apply (v : VOf (⊥ : Subgroup Kˣ)) :
    perfectClosureLinearEquiv K M p v = VOf.mapRingHom (algebraMap K M) bot_le v :=
  rfl

end VOf

namespace MilnorKQ

/-- The Steinberg relation for `e⁻¹ : M^×_ℚ → K^×_ℚ`: if `a + b = 1` in `M`, then
`ι (e⁻¹ [a]) * ι (e⁻¹ [b]) = 0` in `𝒦_*(K)`. -/
theorem ι_perfectClosureEquiv_symm_mul_eq_zero (a b : Mˣ) (hab : (a : M) + b = 1) :
    ι ⊥ ((VOf.perfectClosureLinearEquiv K M p).symm (cls ⊥ (.ofMul a))) *
      ι ⊥ ((VOf.perfectClosureLinearEquiv K M p).symm (cls ⊥ (.ofMul b))) = 0 := by
  obtain ⟨ma, hma⟩ := exists_pow_eq_algebraMap_of_le K M p (a : M)
  obtain ⟨mb, hmb⟩ := exists_pow_eq_algebraMap_of_le K M p (b : M)
  obtain ⟨x, hx⟩ := hma (ma + mb) le_self_add
  obtain ⟨y, hy⟩ := hmb (ma + mb) le_add_self
  set m := ma + mb
  have hx0 : x ≠ 0 := fun h ↦ pow_ne_zero _ a.ne_zero (by rw [← hx, h, map_zero])
  have hy0 : y ≠ 0 := fun h ↦ pow_ne_zero _ b.ne_zero (by rw [← hy, h, map_zero])
  have hxy : x + y = 1 := (algebraMap K M).injective (by
    rw [map_add, hx, hy, ← add_pow_expChar_pow, hab, one_pow, map_one])
  have hpm : ((p ^ m : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (pow_ne_zero _ (expChar_ne_zero M p))
  have key (c : Mˣ) (z : K) (hz0 : z ≠ 0) (hz : algebraMap K M z = (c : M) ^ p ^ m) :
      (VOf.perfectClosureLinearEquiv K M p).symm (cls ⊥ (.ofMul c)) =
        ((p ^ m : ℕ) : ℚ)⁻¹ • cls ⊥ (.ofMul (Units.mk0 z hz0)) := by
    rw [LinearEquiv.symm_apply_eq, map_smul, VOf.perfectClosureLinearEquiv_apply, mapRingHom_cls,
      show Units.map (algebraMap K M : K →* M) (Units.mk0 z hz0) = c ^ p ^ m from
        Units.ext (by simp [hz]),
      cls_pow, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hpm, one_smul]
  rw [key a x hx0 hx, key b y hy0 hy, map_smul, map_smul, smul_mul_smul_comm,
    ι_mul_ι_eq_zero _ (by simpa using hxy), smul_zero]

/-- The inverse `𝒦_*(M) → 𝒦_*(K)` of the map induced by the inclusion. -/
noncomputable def ofPerfectClosure :
    MilnorKQ (⊥ : Subgroup Mˣ) →ₐ[ℚ] MilnorKQ (⊥ : Subgroup Kˣ) :=
  lift (ι ⊥ ∘ₗ (VOf.perfectClosureLinearEquiv K M p).symm.toLinearMap)
    (ι_perfectClosureEquiv_symm_mul_eq_zero K M p)

theorem ofPerfectClosure_ι (w : VOf (⊥ : Subgroup Mˣ)) :
    ofPerfectClosure K M p (ι ⊥ w) = ι ⊥ ((VOf.perfectClosureLinearEquiv K M p).symm w) := by
  simp [ofPerfectClosure]

/-- Blueprint 1.2 / 7.4: `𝒦_*(K) ≅ 𝒦_*(M)` for a `p`-radical extension `M / K` (for instance a
perfect closure), induced by the inclusion. -/
noncomputable def perfectClosureEquiv :
    MilnorKQ (⊥ : Subgroup Kˣ) ≃ₐ[ℚ] MilnorKQ (⊥ : Subgroup Mˣ) :=
  AlgEquiv.ofAlgHom (map (algebraMap K M) bot_le) (ofPerfectClosure K M p)
    (algHom_ext <| LinearMap.ext fun w ↦ by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        ofPerfectClosure_ι, map_ι, AlgHom.id_apply]
      rw [← VOf.perfectClosureLinearEquiv_apply K M p, LinearEquiv.apply_symm_apply])
    (algHom_ext <| LinearMap.ext fun v ↦ by
      simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
        ofPerfectClosure_ι, map_ι, AlgHom.id_apply]
      rw [← VOf.perfectClosureLinearEquiv_apply K M p, LinearEquiv.symm_apply_apply])

theorem perfectClosureEquiv_toAlgHom :
    (perfectClosureEquiv K M p).toAlgHom = map (algebraMap K M) bot_le :=
  rfl

theorem perfectClosureEquiv_symm_toAlgHom :
    (perfectClosureEquiv K M p).symm.toAlgHom = ofPerfectClosure K M p :=
  rfl

theorem isGraded_perfectClosureEquiv : IsGraded (perfectClosureEquiv K M p).toAlgHom :=
  isGraded_map _ _

theorem isGraded_perfectClosureEquiv_symm : IsGraded (perfectClosureEquiv K M p).symm.toAlgHom :=
  isGraded_of_apply_ι (ofPerfectClosure_ι K M p)

end MilnorKQ

end MilnorAlgDep
