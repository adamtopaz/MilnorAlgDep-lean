module

public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Lift
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The rational multiplicative group of a field modulo a subgroup

Blueprint, Section 1.1 and Section 2.3 (the group `V_{L|l}`), and the start of Section 7
(the group `L^×_ℚ = L^× ⊗ ℚ`).

For a field `L` and a subgroup `H` of `Lˣ` we put
`VOf H = ℚ ⊗[ℤ] Additive (Lˣ ⧸ H)`,
a `ℚ`-vector space which we write additively. The class of a unit `a : Lˣ` is
`VOf.cls H (Additive.ofMul a)`, written `〚a〛` (scoped notation in `MilnorAlgDep`, with `H` inferred
from the expected type). Special cases:

* `V l L = VOf (constUnits l L)` is the blueprint's `V_{L|l} = (L^×/l^×) ⊗ ℚ`
  (see `MilnorAlgDep.Foundations.V`);
* `VOf (⊥ : Subgroup Lˣ)` is the blueprint's `L^×_ℚ = L^× ⊗ ℚ = 𝒦_1(L)`.

## Main definitions

* `MilnorAlgDep.VOf H`: the `ℚ`-vector space `ℚ ⊗[ℤ] Additive (Lˣ ⧸ H)`.
* `MilnorAlgDep.VOf.cls H : Additive Lˣ →+ VOf H`: the class map `a ↦ [a]`.
* `MilnorAlgDep.VOf.map f h : VOf H →ₗ[ℚ] VOf H'`: functoriality in a group homomorphism
  `f : Kˣ →* Lˣ` with `H ≤ H'.comap f`; special cases `VOf.proj` (for `H ≤ H'` in the same field)
  and `VOf.mapRingHom` (induced by a ring homomorphism).
* `MilnorAlgDep.VOf.lift f hf : VOf H →ₗ[ℚ] W`: the `ℚ`-linear map induced by an additive map
  `f : Lˣ → W` into a `ℚ`-vector space vanishing on `H`.

## Main statements

* `VOf.exists_nsmul_eq_cls`: every element is `(1/n) • [a]` for some `n ≥ 1` and `a : Lˣ`.
* `VOf.cls_eq_zero_iff`: `[a] = 0 ↔ ∃ n > 0, a ^ n ∈ H`.

Both follow from the fact that `ℚ ⊗[ℤ] M` is the localization of `M` at the non-zero integers.
-/

@[expose] public section

namespace MilnorAlgDep

open TensorProduct

variable {K L : Type*} [Field K] [Field L]

section RatTensor

variable (M : Type*) [AddCommGroup M]

/-- `ℚ ⊗[ℤ] M` is the localization of `M` at the non-zero integers. -/
theorem ratTensor_isLocalizedModule :
    IsLocalizedModule (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1) :=
  inferInstance

variable {M}

/-- Every element of `ℚ ⊗[ℤ] M` is `(1/n) ⊗ m` for some `n ≥ 1`. -/
theorem ratTensor_exists_nsmul_eq_tmul (v : ℚ ⊗[ℤ] M) :
    ∃ (n : ℕ) (m : M), 0 < n ∧ n • v = (1 : ℚ) ⊗ₜ[ℤ] m := by
  obtain ⟨⟨m, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) (TensorProduct.mk ℤ ℚ M 1) v
  dsimp only at hs
  rw [Submonoid.smul_def, TensorProduct.mk_apply] at hs
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  rcases Int.natAbs_eq (s : ℤ) with h | h
  · refine ⟨(s : ℤ).natAbs, m, Int.natAbs_pos.2 hs0, ?_⟩
    rw [← natCast_zsmul, ← h, hs]
  · refine ⟨(s : ℤ).natAbs, -m, Int.natAbs_pos.2 hs0, ?_⟩
    have h' : ((s : ℤ).natAbs : ℤ) = -(s : ℤ) := by omega
    rw [TensorProduct.tmul_neg, ← hs, ← natCast_zsmul, h', neg_smul]

/-- `1 ⊗ m = 0` in `ℚ ⊗[ℤ] M` if and only if `m` is torsion. -/
theorem ratTensor_tmul_eq_zero_iff (m : M) :
    (1 : ℚ) ⊗ₜ[ℤ] m = 0 ↔ ∃ n : ℕ, 0 < n ∧ n • m = 0 := by
  change TensorProduct.mk ℤ ℚ M 1 m = 0 ↔ _
  rw [IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ)]
  constructor
  · rintro ⟨s, hs⟩
    rw [Submonoid.smul_def] at hs
    have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
    refine ⟨(s : ℤ).natAbs, Int.natAbs_pos.2 hs0, ?_⟩
    rcases Int.natAbs_eq (s : ℤ) with h | h
    · rw [← natCast_zsmul, ← h, hs]
    · have h' : ((s : ℤ).natAbs : ℤ) = -(s : ℤ) := by omega
      rw [← natCast_zsmul, h', neg_smul, hs, neg_zero]
  · rintro ⟨n, hn, h⟩
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hn.ne')⟩, ?_⟩
    rw [Submonoid.smul_def]
    change (n : ℤ) • m = 0
    rw [natCast_zsmul, h]

end RatTensor

/-- The rational multiplicative group of `L` modulo the subgroup `H`:
`VOf H = ℚ ⊗[ℤ] Additive (Lˣ ⧸ H)`, a `ℚ`-vector space written additively.

`V l L = VOf (constUnits l L)` is the blueprint's `V_{L|l}` (Section 1.1), and `VOf ⊥` is the
blueprint's `L^×_ℚ = L^× ⊗ ℚ` (Section 7). -/
def VOf (H : Subgroup Lˣ) : Type _ := ℚ ⊗[ℤ] Additive (Lˣ ⧸ H)

namespace VOf

variable (H : Subgroup Lˣ)

instance : AddCommGroup (VOf H) :=
  inferInstanceAs (AddCommGroup (ℚ ⊗[ℤ] Additive (Lˣ ⧸ H)))

instance : Module ℚ (VOf H) :=
  inferInstanceAs (Module ℚ (ℚ ⊗[ℤ] Additive (Lˣ ⧸ H)))

/-- The class map `Lˣ → VOf H`, `a ↦ [a] = 1 ⊗ (a mod H)`, as an additive homomorphism
`Additive Lˣ →+ VOf H`. We write `〚a〛` for `cls _ (Additive.ofMul a)`. -/
noncomputable def cls : Additive Lˣ →+ VOf H :=
  (TensorProduct.mk ℤ ℚ (Additive (Lˣ ⧸ H)) 1).toAddMonoidHom.comp
    (QuotientGroup.mk' H).toAdditive

/-- `〚a〛` is the class `[a]` of the unit `a : Lˣ` in `VOf H`, the subgroup `H` being inferred
from the expected type (for instance from `V l L = VOf (constUnits l L)`). -/
scoped notation "〚" a "〛" => VOf.cls _ (Additive.ofMul a)

variable {H}

theorem cls_apply (a : Lˣ) :
    cls H (.ofMul a) = (1 : ℚ) ⊗ₜ[ℤ] (Additive.ofMul (QuotientGroup.mk a : Lˣ ⧸ H)) :=
  rfl

@[simp]
theorem cls_one : cls H (.ofMul 1) = 0 := by
  rw [ofMul_one, map_zero]

@[simp]
theorem cls_mul (a b : Lˣ) : cls H (.ofMul (a * b)) = cls H (.ofMul a) + cls H (.ofMul b) := by
  rw [ofMul_mul, map_add]

@[simp]
theorem cls_inv (a : Lˣ) : cls H (.ofMul a⁻¹) = -cls H (.ofMul a) := by
  rw [ofMul_inv, map_neg]

@[simp]
theorem cls_div (a b : Lˣ) : cls H (.ofMul (a / b)) = cls H (.ofMul a) - cls H (.ofMul b) := by
  rw [ofMul_div, map_sub]

@[simp]
theorem cls_pow (a : Lˣ) (n : ℕ) : cls H (.ofMul (a ^ n)) = n • cls H (.ofMul a) := by
  rw [ofMul_pow, map_nsmul]

@[simp]
theorem cls_zpow (a : Lˣ) (n : ℤ) : cls H (.ofMul (a ^ n)) = n • cls H (.ofMul a) := by
  rw [ofMul_zpow, map_zsmul]

/-- Every element of `VOf H` is of the form `(1/n) • [a]`: there are `n ≥ 1` and `a : Lˣ` with
`n • v = [a]`. -/
theorem exists_nsmul_eq_cls (v : VOf H) :
    ∃ (n : ℕ) (a : Lˣ), 0 < n ∧ n • v = cls H (.ofMul a) := by
  obtain ⟨n, m, hn, h⟩ := ratTensor_exists_nsmul_eq_tmul (M := Additive (Lˣ ⧸ H)) v
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul m)
  refine ⟨n, a, hn, ?_⟩
  rw [cls_apply, ha]
  exact h

/-- Every element of `VOf H` is `(1/n) • [a]` for some `n ≥ 1` and `a : Lˣ`. -/
theorem exists_eq_inv_smul_cls (v : VOf H) :
    ∃ (n : ℕ) (a : Lˣ), 0 < n ∧ v = (n : ℚ)⁻¹ • cls H (.ofMul a) := by
  obtain ⟨n, a, hn, h⟩ := exists_nsmul_eq_cls v
  refine ⟨n, a, hn, ?_⟩
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← h, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hn', one_smul]

/-- `[a] = 0` in `VOf H` if and only if some positive power of `a` lies in `H`. -/
theorem cls_eq_zero_iff (a : Lˣ) :
    cls H (.ofMul a) = 0 ↔ ∃ n : ℕ, 0 < n ∧ a ^ n ∈ H := by
  rw [cls_apply]
  refine (ratTensor_tmul_eq_zero_iff _).trans ?_
  refine exists_congr fun n ↦ and_congr_right fun _ ↦ ?_
  rw [← ofMul_pow, ← QuotientGroup.mk_pow, ofMul_eq_zero, QuotientGroup.eq_one_iff]

/-- A choice of denominator: `repNat v ≥ 1` with `repNat v • v = [repUnit v]`. -/
noncomputable def repNat (v : VOf H) : ℕ :=
  (exists_nsmul_eq_cls v).choose

/-- A choice of numerator: `repNat v • v = [repUnit v]`. -/
noncomputable def repUnit (v : VOf H) : Lˣ :=
  (exists_nsmul_eq_cls v).choose_spec.choose

theorem repNat_pos (v : VOf H) : 0 < repNat v :=
  (exists_nsmul_eq_cls v).choose_spec.choose_spec.1

theorem repNat_nsmul (v : VOf H) : repNat v • v = cls H (.ofMul (repUnit v)) :=
  (exists_nsmul_eq_cls v).choose_spec.choose_spec.2

theorem cls_eq_zero_of_mem {a : Lˣ} (ha : a ∈ H) : cls H (.ofMul a) = 0 :=
  (cls_eq_zero_iff a).2 ⟨1, one_pos, by rwa [pow_one]⟩

/-- `VOf H` is uniquely divisible: multiplication by a positive integer is injective. -/
theorem nsmul_left_cancel {n : ℕ} (hn : n ≠ 0) {v w : VOf H} (h : n • v = n • w) : v = w := by
  rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ] at h
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [← inv_smul_smul₀ hn' v, h, inv_smul_smul₀ hn']

/-- If `N • v = [a]`, then `(q.den * N) • (q • v) = [a ^ q.num]` for every `q : ℚ`. -/
theorem nsmul_smul_eq_cls {v : VOf H} {N : ℕ} {a : Lˣ} (h : N • v = cls H (.ofMul a)) (q : ℚ) :
    (q.den * N) • (q • v) = cls H (.ofMul (a ^ q.num)) := by
  rw [cls_zpow, ← h, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ,
    ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul, Nat.cast_mul, mul_comm (q.den : ℚ),
    mul_assoc, Rat.den_mul_eq_num, mul_comm]

/-- Two `ℚ`-linear maps out of `VOf H` agreeing on all classes `[a]` are equal. -/
theorem linearMap_ext {W : Type*} [AddCommGroup W] [Module ℚ W] {f g : VOf H →ₗ[ℚ] W}
    (h : ∀ a : Lˣ, f (cls H (.ofMul a)) = g (cls H (.ofMul a))) : f = g := by
  ext v
  obtain ⟨n, a, hn, hv⟩ := exists_eq_inv_smul_cls v
  rw [hv, map_smul, map_smul, h]

section map

variable {H' : Subgroup Lˣ} {H₀ : Subgroup Kˣ}

/-- The `ℚ`-linear map `VOf H₀ → VOf H'` induced by a group homomorphism `f : Kˣ →* Lˣ`
with `f(H₀) ⊆ H'`; it sends `[a]` to `[f a]`. -/
noncomputable def map (f : Kˣ →* Lˣ) (h : H₀ ≤ H'.comap f) : VOf H₀ →ₗ[ℚ] VOf H' :=
  LinearMap.baseChange ℚ (QuotientGroup.map H₀ H' f h).toAdditive.toIntLinearMap

@[simp]
theorem map_cls (f : Kˣ →* Lˣ) (h : H₀ ≤ H'.comap f) (a : Kˣ) :
    map f h (cls H₀ (.ofMul a)) = cls H' (.ofMul (f a)) := by
  simp only [map, cls_apply]
  rfl

/-- The natural projection `VOf H → VOf H'` for subgroups `H ≤ H'` of `Lˣ`;
it sends `[a]` to `[a]`. -/
noncomputable def proj (h : H ≤ H') : VOf H →ₗ[ℚ] VOf H' :=
  map (MonoidHom.id Lˣ) h

@[simp]
theorem proj_cls (h : H ≤ H') (a : Lˣ) : proj h (cls H (.ofMul a)) = cls H' (.ofMul a) :=
  map_cls _ _ a

/-- The `ℚ`-linear map `VOf H₀ → VOf H'` induced by a ring homomorphism `τ : K →+* L` with
`τ(H₀) ⊆ H'`; it sends `[a]` to `[τ a]`. -/
noncomputable def mapRingHom (τ : K →+* L) (h : H₀ ≤ H'.comap (Units.map (τ : K →* L))) :
    VOf H₀ →ₗ[ℚ] VOf H' :=
  map (Units.map (τ : K →* L)) h

@[simp]
theorem mapRingHom_cls (τ : K →+* L) (h : H₀ ≤ H'.comap (Units.map (τ : K →* L))) (a : Kˣ) :
    mapRingHom τ h (cls H₀ (.ofMul a)) = cls H' (.ofMul (Units.map (τ : K →* L) a)) :=
  map_cls _ _ a

theorem map_comp {M : Type*} [Field M] {H'' : Subgroup Mˣ} (f : Kˣ →* Lˣ) (g : Lˣ →* Mˣ)
    (hf : H₀ ≤ H'.comap f) (hg : H' ≤ H''.comap g) :
    (map g hg).comp (map f hf) =
      map (g.comp f) (fun _ hx ↦ Subgroup.mem_comap.2 (Subgroup.mem_comap.1 (hg (hf hx)))) := by
  refine linearMap_ext fun a ↦ ?_
  rw [LinearMap.comp_apply, map_cls, map_cls, map_cls, MonoidHom.comp_apply]

end map

section lift

/-! ### Lifts, projections and functoriality -/

variable {M : Type*} [Field M] {H : Subgroup Lˣ} {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- The `ℚ`-linear map `VOf H → W` into a `ℚ`-vector space induced by an additive map
`f : Additive Lˣ →+ W` vanishing on `H`; it sends `[a]` to `f a` (`lift_cls`). -/
noncomputable def lift (f : Additive Lˣ →+ W) (hf : ∀ a ∈ H, f (.ofMul a) = 0) :
    VOf H →ₗ[ℚ] W :=
  LinearMap.liftBaseChange ℚ
    (MonoidHom.toAdditiveLeft
      (QuotientGroup.lift H (MonoidHom.toAdditiveLeft.symm f) fun a ha ↦ by
        rw [MonoidHom.mem_ker]
        exact congrArg Multiplicative.ofAdd (hf a ha))).toIntLinearMap

@[simp]
theorem lift_cls (f : Additive Lˣ →+ W) (hf : ∀ a ∈ H, f (.ofMul a) = 0) (a : Lˣ) :
    lift f hf (cls H (.ofMul a)) = f (.ofMul a) := by
  rw [cls_apply, lift]
  exact one_smul ℚ (f (.ofMul a))

/-- `lift` composed with a projection. -/
theorem lift_comp_proj {H' : Subgroup Lˣ} (h : H ≤ H') (f : Additive Lˣ →+ W)
    (hf : ∀ a ∈ H', f (.ofMul a) = 0) :
    lift f hf ∘ₗ proj h = lift f fun a ha ↦ hf a (h ha) :=
  linearMap_ext fun a ↦ by rw [LinearMap.comp_apply, proj_cls, lift_cls, lift_cls]

theorem proj_comp_proj {H H' H'' : Subgroup Lˣ} (h : H ≤ H') (h' : H' ≤ H'') :
    proj h' ∘ₗ proj h = proj (h.trans h') :=
  linearMap_ext fun a ↦ by rw [LinearMap.comp_apply, proj_cls, proj_cls, proj_cls]

@[simp]
theorem proj_self {H : Subgroup Lˣ} : proj (le_refl H) = LinearMap.id :=
  linearMap_ext fun a ↦ by rw [proj_cls, LinearMap.id_apply]

theorem _root_.Subgroup.comap_units_map_ringHom_id (H : Subgroup Lˣ) :
    H.comap (Units.map (RingHom.id L : L →* L)) = H :=
  Subgroup.ext fun _ ↦ Iff.rfl

theorem mapRingHom_id {H H' : Subgroup Lˣ}
    (h : H ≤ H'.comap (Units.map (RingHom.id L : L →* L))) :
    mapRingHom (RingHom.id L) h = proj (h.trans (Subgroup.comap_units_map_ringHom_id H').le) := by
  refine linearMap_ext fun a ↦ ?_
  rw [mapRingHom_cls, proj_cls]
  rfl

theorem mapRingHom_comp {H₀ : Subgroup Kˣ} {H : Subgroup Lˣ} {H' : Subgroup Mˣ} (τ : K →+* L)
    (σ : L →+* M) (h : H₀ ≤ H.comap (Units.map (τ : K →* L)))
    (h' : H ≤ H'.comap (Units.map (σ : L →* M))) :
    mapRingHom σ h' ∘ₗ mapRingHom τ h =
      mapRingHom (σ.comp τ)
        (fun _ hx ↦ Subgroup.mem_comap.2 (Subgroup.mem_comap.1 (h' (h hx)))) := by
  refine linearMap_ext fun a ↦ ?_
  rw [LinearMap.comp_apply, mapRingHom_cls, mapRingHom_cls, mapRingHom_cls]
  rfl

end lift

end VOf

end MilnorAlgDep
