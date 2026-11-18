module

public import MilnorAlgDep.Milnor.Basic
public import MilnorAlgDep.Milnor.ValuationExt
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The tame symbol

Blueprint Lemma 7.1 (`lem:tame`), and the relative variant used in the proof of Lemma 7.2(a).

Let `A : ValuationSubring L` be a valuation ring of `L`, with residue field
`κ = IsLocalRing.ResidueField A`, value group `Γ_v = Lˣ ⧸ A.unitGroup` (written additively) and
`Γ_{v,ℚ} = Γ_v ⊗ ℚ = VOf A.unitGroup`; `κ^×_ℚ = VOf (⊥ : Subgroup κˣ)` and
`L^×_ℚ = VOf (⊥ : Subgroup Lˣ)`.

## Main definitions

* `Tame.val A : L^×_ℚ →ₗ[ℚ] Γ_{v,ℚ}`: the valuation, `[b] ↦ v(b)`; its kernel on classes is the
  unit group (`Tame.val_cls_eq_zero_iff`, since `Γ_v` is torsion free).
* `Tame.unitPart A : L^×_ℚ →ₗ[ℚ] κ^×_ℚ`: the blueprint's `𝔲 = res ∘ π`, where `π` is a (chosen)
  `ℚ`-linear retraction of `O^× ⊗ ℚ → L^×_ℚ`. It satisfies `𝔲 [c] = [c̄]` for every unit
  `c ∈ A.unitGroup` (`Tame.unitPart_cls_of_mem`).
* `Tame.form A`: the bilinear form `B(α, β) = v(α) ⊗ 𝔲(β) - v(β) ⊗ 𝔲(α)` with values in
  `Γ_{v,ℚ} ⊗[ℚ] κ^×_ℚ`; it vanishes on Steinberg pairs (`Tame.form_cls_cls_eq_zero`).
* `tameSymbol A : 𝒦_*(L) →ₗ[ℚ] Γ_{v,ℚ} ⊗[ℚ] κ^×_ℚ`: the tame symbol `T_v`, with
  `T_v (ι α * ι β) = B(α, β)` (`tameSymbol_ι_mul_ι`), hence `T_v {c, b} = -v(b) ⊗ [c̄]` for units
  `c` (`tameSymbol_symbol_of_mem`). It is defined on all of `𝒦_*(L)` (and vanishes in degrees
  `0` and `1`, see `MilnorKQ.ofBilin`); only its restriction to `𝒦_2(L)` matters.
* The relative variant, for a field `l` with `[Algebra l L]` on which the valuation is trivial
  (`hl : ∀ x : l, algebraMap l L x ∈ A`): `Tame.resConstUnits A hl ≤ κˣ` is the image of `lˣ`,
  `Tame.valRel`, `Tame.unitPartRel`, `Tame.formRel` are the analogues on `V_{L|l}`, and
  `tameSymbolRel A hl : 𝒦_*(L|l) →ₗ[ℚ] Γ_{v,ℚ} ⊗[ℚ] (κˣ ⧸ lˣ)_ℚ` is the factorization of
  `(id ⊗ proj) ∘ T_v` through `𝒦_*(L) → 𝒦_*(L|l)` (`tameSymbolRel_comp_proj`).

## Auxiliary constructions

* `MilnorKQ.ofBilin B hB : MilnorKQ H →ₗ[ℚ] W`: the linear map induced by a bilinear form `B` on
  `VOf H` vanishing on Steinberg pairs, with `ofBilin B hB (ι α * ι β) = B α β`. It is defined by
  lifting `α ↦ (left multiplication by (0, α, 0))` to an algebra homomorphism into the
  endomorphisms of `ℚ × VOf H × W`, with product `(q, x, w)(q', x', w') = (q q', q x' + q' x,
  q w' + q' w + B(x, x'))`, and taking the third component of the image of `(1, 0, 0)`. This
  avoids the direct sum decomposition of `MilnorKQ H`.
* `tmul_ne_zero`: `x ⊗ y ≠ 0` for non-zero vectors `x`, `y` of `ℚ`-vector spaces.

## Main statements

* `Tame.val_cls_ne_zero_of_valuation_lt_one`: `v(b) ≠ 0` if `v(b) > 0`.
* `Tame.unitPart_cls_eq_zero_iff_of_isAlgebraic`: if the valuation is trivial on `M` and `c` is
  algebraic over `M`, then `𝔲 [c] = 0` iff `c` is a root of unity.
* `Tame.unitPartRel_cls_ne_zero`: if the valuation is trivial on `M ⊇ l` and `a` is algebraic
  over `M` with no positive power in `l`, then the class of `ā` in `(κˣ ⧸ lˣ)_ℚ` is non-zero.
-/

@[expose] public section

namespace MilnorAlgDep

open TensorProduct IsLocalRing VOf MilnorKQ

variable {L : Type*} [Field L]

section Tensor

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- In a tensor product of `ℚ`-vector spaces, `x ⊗ y ≠ 0` if `x ≠ 0` and `y ≠ 0`. -/
theorem tmul_ne_zero {x : V} {y : W} (hx : x ≠ 0) (hy : y ≠ 0) : x ⊗ₜ[ℚ] y ≠ 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℚ hx
  obtain ⟨g, hg⟩ := Module.Projective.exists_dual_eq_one ℚ hy
  intro h
  have := congrArg (TensorProduct.lift ((LinearMap.mul ℚ ℚ).compl₁₂ f g)) h
  simp [hf, hg] at this

/-- In a tensor product of `ℚ`-vector spaces, `x ⊗ y = 0` iff `x = 0` or `y = 0`. -/
theorem tmul_eq_zero_iff {x : V} {y : W} : x ⊗ₜ[ℚ] y = 0 ↔ x = 0 ∨ y = 0 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_contra h'
    push Not at h'
    exact tmul_ne_zero h'.1 h'.2 h
  · rintro (rfl | rfl)
    · exact zero_tmul _ _
    · exact tmul_zero _ _

/-- The alternating bilinear form `(α, β) ↦ f α ⊗ g β - f β ⊗ g α`. -/
noncomputable def altTensorForm {U X Y : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup X]
    [Module ℚ X] [AddCommGroup Y] [Module ℚ Y] (f : U →ₗ[ℚ] X) (g : U →ₗ[ℚ] Y) :
    U →ₗ[ℚ] U →ₗ[ℚ] X ⊗[ℚ] Y :=
  (TensorProduct.mk ℚ X Y).compl₁₂ f g - ((TensorProduct.mk ℚ X Y).compl₁₂ f g).flip

@[simp]
theorem altTensorForm_apply {U X Y : Type*} [AddCommGroup U] [Module ℚ U] [AddCommGroup X]
    [Module ℚ X] [AddCommGroup Y] [Module ℚ Y] (f : U →ₗ[ℚ] X) (g : U →ₗ[ℚ] Y) (α β : U) :
    altTensorForm f g α β = f α ⊗ₜ g β - f β ⊗ₜ g α :=
  rfl

end Tensor

namespace MilnorKQ

/-! ### Linear maps out of `MilnorKQ H` from Steinberg bilinear forms -/

variable {H : Subgroup Lˣ} {W : Type*} [AddCommGroup W] [Module ℚ W]

/-- Auxiliary for `ofBilin`: `α ↦` left multiplication by `(0, α, 0)` on `ℚ × VOf H × W`, where
the product is `(q, x, w)(q', x', w') = (q q', q x' + q' x, q w' + q' w + B(x, x'))`. -/
noncomputable def bilinRep (B : VOf H →ₗ[ℚ] VOf H →ₗ[ℚ] W) :
    VOf H →ₗ[ℚ] Module.End ℚ (ℚ × VOf H × W) :=
  LinearMap.mk₂ ℚ (fun x p ↦ (0, p.1 • x, B x p.2.1))
    (fun x y p ↦ by simp [smul_add])
    (fun c x p ↦ by simp [smul_comm c])
    (fun x p p' ↦ by simp [add_smul])
    (fun c x p ↦ by simp [smul_smul])

theorem bilinRep_apply (B : VOf H →ₗ[ℚ] VOf H →ₗ[ℚ] W) (x : VOf H) (p : ℚ × VOf H × W) :
    bilinRep B x p = (0, p.1 • x, B x p.2.1) :=
  rfl

theorem bilinRep_mul_bilinRep (B : VOf H →ₗ[ℚ] VOf H →ₗ[ℚ] W) (x y : VOf H)
    (p : ℚ × VOf H × W) : (bilinRep B x * bilinRep B y) p = (0, 0, p.1 • B x y) := by
  simp [bilinRep_apply]

/-- Auxiliary for `ofBilin`: the algebra homomorphism `MilnorKQ H → End(ℚ × VOf H × W)` extending
`bilinRep B`. -/
noncomputable def ofBilinRep (B : VOf H →ₗ[ℚ] VOf H →ₗ[ℚ] W)
    (hB : ∀ a b : Lˣ, (a : L) + b = 1 → B (cls H (.ofMul a)) (cls H (.ofMul b)) = 0) :
    MilnorKQ H →ₐ[ℚ] Module.End ℚ (ℚ × VOf H × W) :=
  lift (bilinRep B) fun a b hab ↦ LinearMap.ext fun p ↦ by
    rw [bilinRep_mul_bilinRep, hB a b hab, smul_zero]
    rfl

/-- Blueprint, start of Section 7: a `ℚ`-bilinear form `B` on `VOf H` with `B([a], [b]) = 0`
whenever `a + b = 1` induces a `ℚ`-linear map `MilnorKQ H → W` with `ι α * ι β ↦ B α β`
(`ofBilin_ι_mul_ι`); it vanishes in degrees `0` and `1` (`ofBilin_algebraMap`, `ofBilin_ι`). -/
noncomputable def ofBilin (B : VOf H →ₗ[ℚ] VOf H →ₗ[ℚ] W)
    (hB : ∀ a b : Lˣ, (a : L) + b = 1 → B (cls H (.ofMul a)) (cls H (.ofMul b)) = 0) :
    MilnorKQ H →ₗ[ℚ] W :=
  (LinearMap.snd ℚ (VOf H) W ∘ₗ LinearMap.snd ℚ ℚ (VOf H × W)) ∘ₗ
    LinearMap.applyₗ ((1 : ℚ), (0 : VOf H), (0 : W)) ∘ₗ (ofBilinRep B hB).toLinearMap

variable (B : VOf H →ₗ[ℚ] VOf H →ₗ[ℚ] W)
  (hB : ∀ a b : Lˣ, (a : L) + b = 1 → B (cls H (.ofMul a)) (cls H (.ofMul b)) = 0)

theorem ofBilinRep_ι (α : VOf H) : ofBilinRep B hB (ι H α) = bilinRep B α :=
  lift_ι _ _ α

theorem ofBilin_apply (x : MilnorKQ H) : ofBilin B hB x = (ofBilinRep B hB x (1, 0, 0)).2.2 :=
  rfl

@[simp]
theorem ofBilin_ι_mul_ι (α β : VOf H) : ofBilin B hB (ι H α * ι H β) = B α β := by
  rw [ofBilin_apply, map_mul, ofBilinRep_ι, ofBilinRep_ι, bilinRep_mul_bilinRep, one_smul]

@[simp]
theorem ofBilin_ι (α : VOf H) : ofBilin B hB (ι H α) = 0 := by
  rw [ofBilin_apply, ofBilinRep_ι, bilinRep_apply, map_zero]

@[simp]
theorem ofBilin_algebraMap (q : ℚ) : ofBilin B hB (algebraMap ℚ (MilnorKQ H) q) = 0 := by
  rw [ofBilin_apply, AlgHom.commutes, Module.algebraMap_end_apply, Prod.smul_snd, Prod.smul_snd,
    smul_zero]

@[simp]
theorem ofBilin_one : ofBilin B hB 1 = 0 := by
  simpa using ofBilin_algebraMap B hB 1

theorem ofBilin_symbol (a b : Lˣ) :
    ofBilin B hB (symbol H a b) = B (cls H (.ofMul a)) (cls H (.ofMul b)) :=
  ofBilin_ι_mul_ι B hB _ _

/-- Naturality of `ofBilin` with respect to graded homomorphisms: if `φ` is graded and
`B'(φ₁ α, φ₁ β) = g (B(α, β))`, then `ofBilin B' ∘ φ = g ∘ ofBilin B`. -/
theorem ofBilin_comp {K : Type*} [Field K] {H' : Subgroup Kˣ} {W' : Type*} [AddCommGroup W']
    [Module ℚ W'] (B' : VOf H' →ₗ[ℚ] VOf H' →ₗ[ℚ] W')
    (hB' : ∀ a b : Kˣ, (a : K) + b = 1 → B' (cls H' (.ofMul a)) (cls H' (.ofMul b)) = 0)
    {φ : MilnorKQ H →ₐ[ℚ] MilnorKQ H'} (hφ : IsGraded φ) (g : W →ₗ[ℚ] W')
    (hg : ∀ α β, B' (degOne φ α) (degOne φ β) = g (B α β)) :
    ofBilin B' hB' ∘ₗ φ.toLinearMap = g ∘ₗ ofBilin B hB := by
  -- the stronger statement: `P (ρ x e) = ρ' (φ x) e'` with `P = id × φ₁ × g`
  let P := LinearMap.prodMap (LinearMap.id : ℚ →ₗ[ℚ] ℚ) (LinearMap.prodMap (degOne φ) g)
  have key : P ∘ₗ LinearMap.applyₗ ((1 : ℚ), (0 : VOf H), (0 : W)) ∘ₗ
      (ofBilinRep B hB).toLinearMap =
      LinearMap.applyₗ ((1 : ℚ), (0 : VOf H'), (0 : W')) ∘ₗ (ofBilinRep B' hB').toLinearMap ∘ₗ
        φ.toLinearMap := by
    refine MilnorKQ.linearMap_ext ?_ fun v x hx ↦ ?_
    · simp [P]
    · simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, LinearMap.applyₗ_apply_apply,
        map_mul, mul_apply_eq_comp, ofBilinRep_ι, hφ.apply_ι] at hx ⊢
      rw [← hx]
      simp [P, bilinRep_apply, hg]
  refine LinearMap.ext fun x ↦ ?_
  have := congrArg (fun p ↦ p.2.2) (LinearMap.congr_fun key x)
  simpa [P, ofBilin_apply] using this.symm

end MilnorKQ

namespace Tame

/-! ### The valuation and the unit part on `L^×_ℚ` -/

variable (A : ValuationSubring L)

/-- Blueprint Lemma 7.1 (proof): the valuation `v : L^×_ℚ → Γ_{v,ℚ} = VOf A.unitGroup`,
`[b] ↦ v(b)` (the projection `VOf ⊥ → VOf A.unitGroup`). -/
noncomputable def val : VOf (⊥ : Subgroup Lˣ) →ₗ[ℚ] VOf A.unitGroup :=
  VOf.proj bot_le

@[simp]
theorem val_cls (b : Lˣ) : val A (cls ⊥ (.ofMul b)) = cls A.unitGroup (.ofMul b) :=
  proj_cls _ b

/-- `v(b) = 0` iff `b` is a unit of `A` (the value group is torsion free). -/
theorem val_cls_eq_zero_iff (b : Lˣ) : val A (cls ⊥ (.ofMul b)) = 0 ↔ b ∈ A.unitGroup := by
  rw [val_cls, VOf.cls_eq_zero_iff]
  exact ⟨fun ⟨n, hn, h⟩ ↦ (ValuationExt.pow_mem_unitGroup_iff hn.ne').1 h,
    fun h ↦ ⟨1, one_pos, by rwa [pow_one]⟩⟩

theorem val_cls_of_mem {c : Lˣ} (hc : c ∈ A.unitGroup) : val A (cls ⊥ (.ofMul c)) = 0 :=
  (val_cls_eq_zero_iff A c).2 hc

/-- `v(b) ≠ 0` if `v(b) > 0`. -/
theorem val_cls_ne_zero_of_valuation_lt_one {b : Lˣ} (hb : A.valuation (b : L) < 1) :
    val A (cls ⊥ (.ofMul b)) ≠ 0 := by
  rw [Ne, val_cls_eq_zero_iff, ValuationSubring.mem_unitGroup_iff]
  exact hb.ne

/-- `O^× ⊗ ℚ → L^×_ℚ`, induced by the inclusion `A.unitGroup ≤ Lˣ`. -/
noncomputable def unitsIncl : ℚ ⊗[ℤ] Additive A.unitGroup →ₗ[ℚ] VOf (⊥ : Subgroup Lˣ) :=
  LinearMap.baseChange ℚ
    (MonoidHom.toAdditive ((QuotientGroup.mk' ⊥).comp A.unitGroup.subtype)).toIntLinearMap

theorem unitsIncl_tmul (c : A.unitGroup) :
    unitsIncl A ((1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul c) = cls ⊥ (.ofMul (c : Lˣ)) :=
  rfl

/-- `O^× ⊗ ℚ → L^×_ℚ` is injective (`ℚ` is flat over `ℤ`). -/
theorem unitsIncl_injective : Function.Injective (unitsIncl A) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨n, c, hn, hc⟩ := ratTensor_exists_nsmul_eq_tmul x
  have h1 : cls (⊥ : Subgroup Lˣ) (.ofMul ((Additive.toMul c : A.unitGroup) : Lˣ)) = 0 := by
    rw [← unitsIncl_tmul, ofMul_toMul, ← hc, map_nsmul, hx, nsmul_zero]
  obtain ⟨m, hm, hcm⟩ := (VOf.cls_eq_zero_iff _).1 h1
  have h2 : (1 : ℚ) ⊗ₜ[ℤ] c = 0 := by
    refine (ratTensor_tmul_eq_zero_iff c).2 ⟨m, hm, ?_⟩
    have hpow : (Additive.toMul c) ^ m = 1 := Subtype.ext (by simpa using hcm)
    rw [← ofMul_toMul c, ← ofMul_pow, hpow, ofMul_one]
  rw [h2, ← Nat.cast_smul_eq_nsmul ℚ, smul_eq_zero] at hc
  exact hc.resolve_left (by exact_mod_cast hn.ne')

/-- `res : O^× ⊗ ℚ → κ^×_ℚ`, induced by the residue map `A.unitGroup → κˣ`. -/
noncomputable def unitsRes :
    ℚ ⊗[ℤ] Additive A.unitGroup →ₗ[ℚ] VOf (⊥ : Subgroup (ResidueField A)ˣ) :=
  LinearMap.baseChange ℚ
    (MonoidHom.toAdditive
      ((QuotientGroup.mk' ⊥).comp A.unitGroupToResidueFieldUnits)).toIntLinearMap

theorem unitsRes_tmul (c : A.unitGroup) :
    unitsRes A ((1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul c) =
      cls ⊥ (.ofMul (A.unitGroupToResidueFieldUnits c)) :=
  rfl

/-- Blueprint Lemma 7.1 (proof): the map `𝔲 = res ∘ π : L^×_ℚ → κ^×_ℚ`, where `π` is a
`ℚ`-linear retraction of `O^× ⊗ ℚ → L^×_ℚ` (chosen with `LinearMap.leftInverse`). It satisfies
`𝔲 [c] = [c̄]` for `c ∈ A.unitGroup` (`unitPart_cls_of_mem`). -/
noncomputable def unitPart :
    VOf (⊥ : Subgroup Lˣ) →ₗ[ℚ] VOf (⊥ : Subgroup (ResidueField A)ˣ) :=
  unitsRes A ∘ₗ (unitsIncl A).leftInverse

/-- `𝔲 [c] = [c̄]` for every unit `c` of `A`. -/
theorem unitPart_cls_of_mem {c : Lˣ} (hc : c ∈ A.unitGroup) :
    unitPart A (cls ⊥ (.ofMul c)) = cls ⊥ (.ofMul (A.unitGroupToResidueFieldUnits ⟨c, hc⟩)) := by
  rw [unitPart, LinearMap.comp_apply, ← unitsRes_tmul]
  congr 1
  rw [← unitsIncl_tmul A ⟨c, hc⟩, LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.2 (unitsIncl_injective A))]

/-- If `v(x) > 0` and `u = 1 - x`, then `v(u) = 0` and `𝔲 [u] = 0`. -/
theorem val_unitPart_cls_one_sub {x : L} (hx : A.valuation x < 1) {u : Lˣ}
    (hu : (u : L) = 1 - x) :
    val A (cls ⊥ (.ofMul u)) = 0 ∧ unitPart A (cls ⊥ (.ofMul u)) = 0 := by
  have hu' : u ∈ A.principalUnitGroup := by
    have : u = Units.mk0 (1 - x) (ValuationExt.one_sub_ne_zero_of_valuation_lt_one hx) :=
      Units.ext hu
    rw [this]
    exact ValuationExt.mk0_one_sub_mem_principalUnitGroup hx
  have hmem := A.principal_units_le_units hu'
  refine ⟨val_cls_of_mem A hmem, ?_⟩
  have hker : A.unitGroupToResidueFieldUnits ⟨u, hmem⟩ = 1 := by
    rw [← MonoidHom.mem_ker, A.ker_unitGroupToResidueFieldUnits]
    exact hu'
  rw [unitPart_cls_of_mem A hmem, hker, cls_one]

/-- If the valuation is trivial on `M`, it is trivial on the elements algebraic over `M`. -/
theorem val_cls_of_isAlgebraic {M : Type*} [Field M] [Algebra M L]
    (hM : ∀ x : M, algebraMap M L x ∈ A) {c : Lˣ} (hc : IsAlgebraic M (c : L)) :
    val A (cls ⊥ (.ofMul c)) = 0 :=
  val_cls_of_mem A (ValuationExt.mem_unitGroup_of_isAlgebraic hM hc)

/-- The residue class of a unit `x` of `A`, as an element of `κ`. -/
theorem coe_unitGroupToResidueFieldUnits (x : A.unitGroup) :
    (A.unitGroupToResidueFieldUnits x : ResidueField A) =
      residue A ⟨((x : Lˣ) : L), (A.valuation_le_one_iff _).1 (le_of_eq x.2)⟩ :=
  rfl

/-- If the valuation is trivial on `M` and the unit `d` of `A` is algebraic over `M`, then
`d̄ = 1` iff `d = 1`. -/
theorem unitGroupToResidueFieldUnits_eq_one_iff_of_isAlgebraic {M : Type*} [Field M]
    [Algebra M L] (hM : ∀ x : M, algebraMap M L x ∈ A) {d : Lˣ} (hdu : d ∈ A.unitGroup)
    (hd : IsAlgebraic M (d : L)) : A.unitGroupToResidueFieldUnits ⟨d, hdu⟩ = 1 ↔ d = 1 := by
  refine ⟨fun h ↦ Units.ext ?_, fun h ↦ by subst h; exact map_one _⟩
  have h' := congrArg (fun z : (ResidueField A)ˣ ↦ (z : ResidueField A)) h
  simp only [coe_unitGroupToResidueFieldUnits, Units.val_one] at h'
  rw [← map_one (residue A)] at h'
  exact ValuationExt.eq_of_residue_eq_of_isAlgebraic hM hd isAlgebraic_one h'

/-- If the valuation is trivial on `M` and `c` is algebraic over `M`, then `𝔲 [c] = 0` iff `c` is
a root of unity (the relative algebraic closure of `M` embeds in the residue field). -/
theorem unitPart_cls_eq_zero_iff_of_isAlgebraic {M : Type*} [Field M] [Algebra M L]
    (hM : ∀ x : M, algebraMap M L x ∈ A) {c : Lˣ} (hc : IsAlgebraic M (c : L)) :
    unitPart A (cls ⊥ (.ofMul c)) = 0 ↔ ∃ n : ℕ, 0 < n ∧ c ^ n = 1 := by
  have hcu := ValuationExt.mem_unitGroup_of_isAlgebraic hM hc
  rw [unitPart_cls_of_mem A hcu, VOf.cls_eq_zero_iff]
  refine exists_congr fun n ↦ and_congr_right fun _ ↦ ?_
  rw [Subgroup.mem_bot, ← map_pow]
  have hpow : (⟨c, hcu⟩ ^ n : A.unitGroup) = ⟨c ^ n, pow_mem hcu n⟩ := rfl
  rw [hpow, unitGroupToResidueFieldUnits_eq_one_iff_of_isAlgebraic A hM]
  rw [Units.val_pow_eq_pow_val]
  exact hc.pow n

/-- The same, in terms of the class of `c` in `L^×_ℚ`. -/
theorem unitPart_cls_eq_zero_iff_of_isAlgebraic' {M : Type*} [Field M] [Algebra M L]
    (hM : ∀ x : M, algebraMap M L x ∈ A) {c : Lˣ} (hc : IsAlgebraic M (c : L)) :
    unitPart A (cls ⊥ (.ofMul c)) = 0 ↔ cls ⊥ (.ofMul c) = 0 := by
  rw [unitPart_cls_eq_zero_iff_of_isAlgebraic A hM hc, VOf.cls_eq_zero_iff]
  simp [Subgroup.mem_bot]

/-- Blueprint Lemma 7.1 (proof, case `v(a) < 0`): if `a + b = 1` and `v(a) < 0`, then
`v(b) = v(a)` and `𝔲 [b] = 𝔲 [a]`, because `[b] = [a] + [1 - a⁻¹]` in `L^×_ℚ` and `1 - a⁻¹` is a
principal unit. -/
theorem val_unitPart_cls_of_one_lt {a b : Lˣ} (hab : (a : L) + b = 1)
    (ha : 1 < A.valuation (a : L)) :
    val A (cls ⊥ (.ofMul b)) = val A (cls ⊥ (.ofMul a)) ∧
      unitPart A (cls ⊥ (.ofMul b)) = unitPart A (cls ⊥ (.ofMul a)) := by
  have hx : A.valuation ((a : L)⁻¹) < 1 := by
    rw [map_inv₀]
    exact inv_lt_one_of_one_lt₀ ha
  set u := Units.mk0 (1 - (a : L)⁻¹) (ValuationExt.one_sub_ne_zero_of_valuation_lt_one hx)
  have hb : b = -1 * a * u := Units.ext (by
    simp only [u, Units.val_mul, Units.val_neg, Units.val_one, Units.val_mk0]
    rw [mul_sub, mul_one, mul_assoc, mul_inv_cancel₀ a.ne_zero]
    linear_combination hab)
  have hm1 : cls (⊥ : Subgroup Lˣ) (.ofMul (-1)) = 0 :=
    (VOf.cls_eq_zero_iff _).2 ⟨2, two_pos, by simp⟩
  obtain ⟨h1, h2⟩ := val_unitPart_cls_one_sub A hx (u := u) rfl
  rw [hb, cls_mul, cls_mul, hm1, zero_add, map_add, map_add, h1, h2, add_zero, add_zero]
  exact ⟨rfl, rfl⟩

/-! ### The bilinear form and the tame symbol -/

/-- Blueprint Lemma 7.1 (proof): the bilinear form `B(α, β) = v(α) ⊗ 𝔲(β) - v(β) ⊗ 𝔲(α)` on
`L^×_ℚ`, with values in `Γ_{v,ℚ} ⊗ κ^×_ℚ`. -/
noncomputable def form : VOf (⊥ : Subgroup Lˣ) →ₗ[ℚ] VOf (⊥ : Subgroup Lˣ) →ₗ[ℚ]
    VOf A.unitGroup ⊗[ℚ] VOf (⊥ : Subgroup (ResidueField A)ˣ) :=
  altTensorForm (val A) (unitPart A)

theorem form_apply (α β : VOf (⊥ : Subgroup Lˣ)) :
    form A α β = val A α ⊗ₜ unitPart A β - val A β ⊗ₜ unitPart A α :=
  rfl

/-- Blueprint Lemma 7.1 (proof): `B([a], [b]) = 0` whenever `a + b = 1`. -/
theorem form_cls_cls_eq_zero {a b : Lˣ} (hab : (a : L) + b = 1) :
    form A (cls ⊥ (.ofMul a)) (cls ⊥ (.ofMul b)) = 0 := by
  have hb_eq : (b : L) = 1 - a := by rw [← hab]; ring
  have ha_eq : (a : L) = 1 - b := by rw [← hab]; ring
  have hright : ∀ α β, val A β = 0 → unitPart A β = 0 → form A α β = 0 := fun α β h1 h2 ↦ by
    rw [form_apply, h1, h2, tmul_zero, zero_tmul, sub_zero]
  have hleft : ∀ α β, val A α = 0 → unitPart A α = 0 → form A α β = 0 := fun α β h1 h2 ↦ by
    rw [form_apply, h1, h2, tmul_zero, zero_tmul, sub_zero]
  have hdiag : ∀ α β, val A α = val A β → unitPart A α = unitPart A β → form A α β = 0 :=
    fun α β h1 h2 ↦ by rw [form_apply, h1, h2, sub_self]
  rcases lt_trichotomy (A.valuation (a : L)) 1 with ha | ha | ha
  · obtain ⟨h1, h2⟩ := val_unitPart_cls_one_sub A ha hb_eq
    exact hright _ _ h1 h2
  · rcases lt_trichotomy (A.valuation (b : L)) 1 with hb | hb | hb
    · obtain ⟨h1, h2⟩ := val_unitPart_cls_one_sub A hb ha_eq
      exact hleft _ _ h1 h2
    · rw [form_apply, val_cls_of_mem A ((A.mem_unitGroup_iff a).2 ha),
        val_cls_of_mem A ((A.mem_unitGroup_iff b).2 hb), zero_tmul, zero_tmul, sub_zero]
    · obtain ⟨h1, h2⟩ := val_unitPart_cls_of_one_lt A (by rwa [add_comm]) hb
      exact hdiag _ _ h1 h2
  · obtain ⟨h1, h2⟩ := val_unitPart_cls_of_one_lt A hab ha
    exact hdiag _ _ h1.symm h2.symm

end Tame

open Tame

variable (A : ValuationSubring L)

/-- **Blueprint Lemma 7.1** (tame symbol). For a valuation ring `A` of `L` with residue field
`κ` and value group `Γ_v`, the `ℚ`-linear map `T_v : 𝒦_*(L) → Γ_{v,ℚ} ⊗[ℚ] κ^×_ℚ` with
`T_v (ι α * ι β) = v(α) ⊗ 𝔲(β) - v(β) ⊗ 𝔲(α)` (`tameSymbol_ι_mul_ι`); in particular
`T_v {c, b} = -v(b) ⊗ [c̄]` for `c ∈ O^×` (`tameSymbol_symbol_of_mem`). (The blueprint defines
`T_v` on `𝒦_2(L)`; ours is defined on all of `𝒦_*(L)` and vanishes in degrees `0` and `1`.) -/
noncomputable def tameSymbol : MilnorKQ (⊥ : Subgroup Lˣ) →ₗ[ℚ]
    VOf A.unitGroup ⊗[ℚ] VOf (⊥ : Subgroup (ResidueField A)ˣ) :=
  ofBilin (form A) fun _ _ hab ↦ form_cls_cls_eq_zero A hab

/-- The tame symbol on products of degree one elements: `T_v (ι α * ι β) = B(α, β)`. -/
theorem tameSymbol_ι_mul_ι (α β : VOf (⊥ : Subgroup Lˣ)) :
    tameSymbol A (ι ⊥ α * ι ⊥ β) = val A α ⊗ₜ unitPart A β - val A β ⊗ₜ unitPart A α :=
  ofBilin_ι_mul_ι _ _ α β

/-- **Blueprint Lemma 7.1**: `T_v {c, b} = -v(b) ⊗ [c̄]` for `c ∈ O^×` and `b ∈ Lˣ`. -/
theorem tameSymbol_symbol_of_mem {c : Lˣ} (hc : c ∈ A.unitGroup) (b : Lˣ) :
    tameSymbol A (symbol ⊥ c b) =
      -(val A (cls ⊥ (.ofMul b)) ⊗ₜ cls ⊥ (.ofMul (A.unitGroupToResidueFieldUnits ⟨c, hc⟩))) := by
  rw [symbol, tameSymbol_ι_mul_ι, val_cls_of_mem A hc, zero_tmul, zero_sub, unitPart_cls_of_mem]

theorem tameSymbol_ι (α : VOf (⊥ : Subgroup Lˣ)) : tameSymbol A (ι ⊥ α) = 0 :=
  ofBilin_ι _ _ α

/-! ### The relative tame symbol -/

namespace Tame

variable {l : Type*} [Field l] [Algebra l L] (hl : ∀ x : l, algebraMap l L x ∈ A)

/-- The image of `lˣ` in `κˣ`, for a valuation trivial on `l`. -/
noncomputable def resConstUnits : Subgroup (ResidueField A)ˣ :=
  (ValuationExt.residueUnitsHom hl).range

include hl in
/-- A valuation trivial on `l` maps `lˣ` into its unit group. -/
theorem constUnits_le_unitGroup : constUnits l L ≤ A.unitGroup := by
  rintro _ ⟨u, rfl⟩
  exact ValuationExt.units_map_mem_unitGroup hl u

/-- The valuation on `V_{L|l}`, for a valuation trivial on `l`. -/
noncomputable def valRel : V l L →ₗ[ℚ] VOf A.unitGroup :=
  VOf.proj (constUnits_le_unitGroup A hl)

@[simp]
theorem valRel_cls (b : Lˣ) :
    valRel A hl (cls (constUnits l L) (.ofMul b)) = cls A.unitGroup (.ofMul b) :=
  proj_cls _ b

theorem valRel_comp_proj : valRel A hl ∘ₗ VOf.proj bot_le = val A :=
  linearMap_ext fun b ↦ by rw [LinearMap.comp_apply, proj_cls, valRel_cls, val_cls]

theorem unitPart_cls_mem_ker {a : Lˣ} (ha : a ∈ constUnits l L) :
    VOf.proj (bot_le : ⊥ ≤ resConstUnits A hl) (unitPart A (cls ⊥ (.ofMul a))) = 0 := by
  obtain ⟨u, rfl⟩ := ha
  have hmem := constUnits_le_unitGroup A hl ⟨u, rfl⟩
  rw [unitPart_cls_of_mem A hmem, proj_cls]
  exact cls_eq_zero_of_mem ⟨u, (ValuationExt.unitGroupToResidueFieldUnits_units_map hl u).symm⟩

/-- The unit part on `V_{L|l}`: `𝔲` followed by the projection `κ^×_ℚ → (κˣ ⧸ lˣ)_ℚ`, which
factors through `V_{L|l}` (`unitPartRel_comp_proj`). -/
noncomputable def unitPartRel : V l L →ₗ[ℚ] VOf (resConstUnits A hl) :=
  VOf.lift ((VOf.proj bot_le ∘ₗ unitPart A).toAddMonoidHom.comp (cls ⊥))
    fun _ ha ↦ unitPart_cls_mem_ker A hl ha

theorem unitPartRel_cls (a : Lˣ) :
    unitPartRel A hl (cls (constUnits l L) (.ofMul a)) =
      VOf.proj bot_le (unitPart A (cls ⊥ (.ofMul a))) :=
  lift_cls _ _ a

theorem unitPartRel_comp_proj :
    unitPartRel A hl ∘ₗ VOf.proj bot_le = VOf.proj bot_le ∘ₗ unitPart A :=
  linearMap_ext fun a ↦ by
    rw [LinearMap.comp_apply, proj_cls, unitPartRel_cls, LinearMap.comp_apply]

/-- `𝔲' [c] = [c̄]` for every unit `c` of `A`. -/
theorem unitPartRel_cls_of_mem {c : Lˣ} (hc : c ∈ A.unitGroup) :
    unitPartRel A hl (cls (constUnits l L) (.ofMul c)) =
      cls (resConstUnits A hl) (.ofMul (A.unitGroupToResidueFieldUnits ⟨c, hc⟩)) := by
  rw [unitPartRel_cls, unitPart_cls_of_mem A hc, proj_cls]

/-- Used in Lemma 7.2(a): if the valuation is trivial on an intermediate field `l ⊆ M ⊆ L` and
`a` is algebraic over `M` with no positive power in `l`, then the class of `ā` in
`(κˣ ⧸ lˣ)_ℚ` is non-zero. -/
theorem unitPartRel_cls_ne_zero {M : Type*} [Field M] [Algebra l M] [Algebra M L]
    [IsScalarTower l M L] (hM : ∀ x : M, algebraMap M L x ∈ A) {a : Lˣ}
    (ha : IsAlgebraic M (a : L))
    (ha' : ∀ n : ℕ, 0 < n → (a : L) ^ n ∉ Set.range (algebraMap l L)) :
    unitPartRel A hl (cls (constUnits l L) (.ofMul a)) ≠ 0 := by
  have hau : a ∈ A.unitGroup := ValuationExt.mem_unitGroup_of_isAlgebraic hM ha
  rw [unitPartRel_cls_of_mem A hl hau]
  intro h
  obtain ⟨n, hn, u, hu⟩ := (VOf.cls_eq_zero_iff _).1 h
  have hu' : A.unitGroupToResidueFieldUnits ⟨_, ValuationExt.units_map_mem_unitGroup hl u⟩ =
      A.unitGroupToResidueFieldUnits ⟨a ^ n, pow_mem hau n⟩ := by
    rw [ValuationExt.unitGroupToResidueFieldUnits_units_map hl, hu, ← map_pow]
    rfl
  have hu'' := congrArg (fun z : (ResidueField A)ˣ ↦ (z : ResidueField A)) hu'
  simp only [coe_unitGroupToResidueFieldUnits] at hu''
  have halg : IsAlgebraic M (algebraMap l L u) := by
    rw [IsScalarTower.algebraMap_apply l M L]
    exact isAlgebraic_algebraMap _
  have key := ValuationExt.eq_of_residue_eq_of_isAlgebraic hM halg
    (by rw [Units.val_pow_eq_pow_val]; exact ha.pow n) hu''
  exact ha' n hn ⟨u, by rw [← Units.val_pow_eq_pow_val, ← key]⟩

/-- The bilinear form `B'(α, β) = v(α) ⊗ 𝔲'(β) - v(β) ⊗ 𝔲'(α)` on `V_{L|l}`. -/
noncomputable def formRel : V l L →ₗ[ℚ] V l L →ₗ[ℚ]
    VOf A.unitGroup ⊗[ℚ] VOf (resConstUnits A hl) :=
  altTensorForm (valRel A hl) (unitPartRel A hl)

theorem formRel_apply (α β : V l L) :
    formRel A hl α β = valRel A hl α ⊗ₜ unitPartRel A hl β - valRel A hl β ⊗ₜ unitPartRel A hl α :=
  rfl

/-- `B'` is the image of `B` under `id ⊗ proj`. -/
theorem formRel_proj_proj (α β : VOf (⊥ : Subgroup Lˣ)) :
    formRel A hl (VOf.proj bot_le α) (VOf.proj bot_le β) =
      LinearMap.lTensor _ (VOf.proj bot_le) (form A α β) := by
  have h1 γ : valRel A hl (VOf.proj bot_le γ) = val A γ :=
    LinearMap.congr_fun (valRel_comp_proj A hl) γ
  have h2 γ : unitPartRel A hl (VOf.proj bot_le γ) = VOf.proj bot_le (unitPart A γ) :=
    LinearMap.congr_fun (unitPartRel_comp_proj A hl) γ
  rw [formRel_apply, h1, h1, h2, h2, form_apply, map_sub, LinearMap.lTensor_tmul,
    LinearMap.lTensor_tmul]

theorem formRel_cls_cls_eq_zero {a b : Lˣ} (hab : (a : L) + b = 1) :
    formRel A hl (cls (constUnits l L) (.ofMul a)) (cls (constUnits l L) (.ofMul b)) = 0 := by
  rw [← proj_cls (bot_le : ⊥ ≤ constUnits l L), ← proj_cls (bot_le : ⊥ ≤ constUnits l L) b,
    formRel_proj_proj, form_cls_cls_eq_zero A hab, map_zero]

end Tame

variable {l : Type*} [Field l] [Algebra l L] (hl : ∀ x : l, algebraMap l L x ∈ A)

/-- Blueprint Lemma 7.2 (proof of (a)): the relative tame symbol
`T'_v : 𝒦_*(L|l) → Γ_{v,ℚ} ⊗[ℚ] (κˣ ⧸ lˣ)_ℚ` for a valuation trivial on `l`, with
`T'_v (ι α * ι β) = B'(α, β)` (`tameSymbolRel_ι_mul_ι`). It is the factorization of
`(id ⊗ proj) ∘ T_v` through `𝒦_*(L) → 𝒦_*(L|l)` (`tameSymbolRel_comp_proj`). -/
noncomputable def tameSymbolRel : MilnorKQ (constUnits l L) →ₗ[ℚ]
    VOf A.unitGroup ⊗[ℚ] VOf (resConstUnits A hl) :=
  ofBilin (formRel A hl) fun _ _ hab ↦ formRel_cls_cls_eq_zero A hl hab

theorem tameSymbolRel_ι_mul_ι (α β : V l L) :
    tameSymbolRel A hl (ι _ α * ι _ β) =
      valRel A hl α ⊗ₜ unitPartRel A hl β - valRel A hl β ⊗ₜ unitPartRel A hl α :=
  ofBilin_ι_mul_ι _ _ α β

/-- `T'_v {c, b} = -v(b) ⊗ [c̄]` for `c ∈ O^×` and `b ∈ Lˣ`. -/
theorem tameSymbolRel_symbol_of_mem {c : Lˣ} (hc : c ∈ A.unitGroup) (b : Lˣ) :
    tameSymbolRel A hl (symbol (constUnits l L) c b) =
      -(cls A.unitGroup (.ofMul b) ⊗ₜ
        cls (resConstUnits A hl) (.ofMul (A.unitGroupToResidueFieldUnits ⟨c, hc⟩))) := by
  rw [symbol, tameSymbolRel_ι_mul_ι, valRel_cls, valRel_cls,
    cls_eq_zero_of_mem (H := A.unitGroup) hc, zero_tmul, zero_sub, unitPartRel_cls_of_mem]

/-- `T'_v ∘ (𝒦_*(L) → 𝒦_*(L|l)) = (id ⊗ proj) ∘ T_v`. -/
theorem tameSymbolRel_comp_proj :
    tameSymbolRel A hl ∘ₗ (MilnorKQ.proj (bot_le : ⊥ ≤ constUnits l L)).toLinearMap =
      LinearMap.lTensor _ (VOf.proj bot_le) ∘ₗ tameSymbol A :=
  ofBilin_comp _ _ _ _ (isGraded_proj _) _ fun α β ↦ by
    rw [degOne_proj, formRel_proj_proj]

end MilnorAlgDep
