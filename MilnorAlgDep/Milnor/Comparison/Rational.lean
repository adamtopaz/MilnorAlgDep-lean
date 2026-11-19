module

public import MilnorAlgDep.Milnor.Basic
public import MilnorAlgDep.Milnor.Comparison.Integral
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The rational comparison `ℚ ⊗ K^M_*(L) ≅ MilnorKQ ⊥`

Blueprint, Section 1.2 (`𝒦_*(K) = ℚ ⊗ K^M_*(K)`) and the start of Section 7
(`𝒦_1(L) = L^× ⊗ ℚ`).

The paper's `𝒦_*(L)` is `ℚ ⊗ K^M_*(L)`; the formalization uses `MilnorKQ (⊥ : Subgroup Lˣ)`, the
quotient of the tensor algebra over `ℚ` of `VOf ⊥ = ℚ ⊗[ℤ] Additive (Lˣ ⧸ ⊥)` by the Steinberg
relations. We construct the canonical isomorphism of `ℚ`-algebras between them, from the universal
properties on both sides.

## Main definitions

* `VOf.botEquiv L : VOf ⊥ ≃ₗ[ℚ] ℚ ⊗[ℤ] Additive Lˣ`: the degree one part, `𝒦_1(L) = L^× ⊗ ℚ`.
* `MilnorK.ratEquiv L : ℚ ⊗[ℤ] MilnorK L ≃ₐ[ℚ] MilnorKQ ⊥`: the comparison isomorphism.
* `MilnorK.ratMap τ = id_ℚ ⊗ τ_*`.

## Main statements

* `MilnorK.ratEquiv_one_tmul_ι`, `MilnorK.ratEquiv_one_tmul_symbol`: `1 ⊗ ι a ↦ ι [a]` and
  `1 ⊗ {a, b} ↦ {a, b}`; `MilnorK.ratEquiv_baseChange_ι`, `MilnorK.ratEquiv_symm_ι`: in degree one
  the isomorphism is the identification `VOf.botEquiv`.
* `MilnorK.ratEquiv_comp_ratMap`: compatibility with `τ_*`.
* `MilnorK.grade_bot_eq_span`: the isomorphism is graded, i.e. it identifies `𝒦_n(L)` with the
  `ℚ`-span of `1 ⊗ K^M_n(L)`; `MilnorK.degScale_ratEquiv_tmul`: compatibility with `r^deg`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf TensorProduct

variable {K L : Type*} [Field K] [Field L]

namespace VOf

variable (L) in
/-- The degree one part of the comparison: `VOf ⊥ = ℚ ⊗[ℤ] Additive (Lˣ ⧸ ⊥)` is
`ℚ ⊗[ℤ] Additive Lˣ = L^× ⊗ ℚ`. -/
noncomputable def botEquiv : VOf (⊥ : Subgroup Lˣ) ≃ₗ[ℚ] ℚ ⊗[ℤ] Additive Lˣ :=
  LinearEquiv.baseChange ℤ ℚ _ _ (QuotientGroup.quotientBot.toAdditive.toIntLinearEquiv)

@[simp]
theorem botEquiv_cls (a : Lˣ) : botEquiv L (cls ⊥ (.ofMul a)) = (1 : ℚ) ⊗ₜ .ofMul a :=
  rfl

@[simp]
theorem botEquiv_symm_tmul (a : Lˣ) :
    (botEquiv L).symm ((1 : ℚ) ⊗ₜ .ofMul a) = cls ⊥ (.ofMul a) := by
  rw [← botEquiv_cls, LinearEquiv.symm_apply_apply]

end VOf

namespace MilnorK

variable (L)

/-- The ring homomorphism `K^M_*(L) → 𝒦_*(L) = MilnorKQ ⊥`, `ι a ↦ ι [a]`. -/
noncomputable def toMilnorKQ : MilnorK L →+* MilnorKQ (⊥ : Subgroup Lˣ) :=
  lift ((MilnorKQ.ι ⊥).toAddMonoidHom.comp (cls ⊥)) fun _ _ hab ↦ MilnorKQ.ι_mul_ι_eq_zero ⊥ hab

@[simp]
theorem toMilnorKQ_ι (a : Lˣ) :
    toMilnorKQ L (ι L (.ofMul a)) = MilnorKQ.ι ⊥ (cls ⊥ (.ofMul a)) :=
  lift_ι _ _ _

/-- The `ℚ`-linear map `VOf ⊥ → ℚ ⊗[ℤ] K^M_*(L)`, `[a] ↦ 1 ⊗ ι a` (the degree one part of the
inverse comparison map). -/
noncomputable def ofVOf : VOf (⊥ : Subgroup Lˣ) →ₗ[ℚ] ℚ ⊗[ℤ] MilnorK L :=
  VOf.lift ((TensorProduct.mk ℤ ℚ (MilnorK L) 1).toAddMonoidHom.comp (ι L)) fun a ha ↦ by
    rw [Subgroup.mem_bot] at ha
    rw [ha, ofMul_one, map_zero]

@[simp]
theorem ofVOf_cls (a : Lˣ) : ofVOf L (cls ⊥ (.ofMul a)) = (1 : ℚ) ⊗ₜ ι L (.ofMul a) :=
  VOf.lift_cls _ _ a

/-- The algebra homomorphism `𝒦_*(L) = MilnorKQ ⊥ → ℚ ⊗[ℤ] K^M_*(L)`, `ι [a] ↦ 1 ⊗ ι a`. -/
noncomputable def ofMilnorKQ : MilnorKQ (⊥ : Subgroup Lˣ) →ₐ[ℚ] ℚ ⊗[ℤ] MilnorK L :=
  MilnorKQ.lift (ofVOf L) fun a b hab ↦ by
    rw [ofVOf_cls, ofVOf_cls, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
      ι_mul_ι_eq_zero L hab, tmul_zero]

@[simp]
theorem ofMilnorKQ_ι_cls (a : Lˣ) :
    ofMilnorKQ L (MilnorKQ.ι ⊥ (cls ⊥ (.ofMul a))) = (1 : ℚ) ⊗ₜ ι L (.ofMul a) := by
  rw [ofMilnorKQ, MilnorKQ.lift_ι, ofVOf_cls]

/-- The algebra homomorphism `ℚ ⊗[ℤ] K^M_*(L) → 𝒦_*(L) = MilnorKQ ⊥`, `q ⊗ x ↦ q • x`, obtained
from `toMilnorKQ` by base change. -/
noncomputable def ratToMilnorKQ : ℚ ⊗[ℤ] MilnorK L →ₐ[ℚ] MilnorKQ (⊥ : Subgroup Lˣ) :=
  AlgHom.liftEquiv ℤ ℚ (MilnorK L) (MilnorKQ ⊥) (toMilnorKQ L).toIntAlgHom

theorem ratToMilnorKQ_tmul (q : ℚ) (x : MilnorK L) :
    ratToMilnorKQ L (q ⊗ₜ x) = q • toMilnorKQ L x :=
  rfl

variable {L}

/-- Two `ℚ`-algebra homomorphisms out of `ℚ ⊗[ℤ] K^M_*(L)` agreeing on all `1 ⊗ ι a` are
equal. -/
theorem ratAlgHom_ext {A : Type*} [Ring A] [Algebra ℚ A] {f g : ℚ ⊗[ℤ] MilnorK L →ₐ[ℚ] A}
    (h : ∀ a : Lˣ, f ((1 : ℚ) ⊗ₜ ι L (.ofMul a)) = g ((1 : ℚ) ⊗ₜ ι L (.ofMul a))) : f = g :=
  Algebra.TensorProduct.ext_ring (intAlgHom_ext h)

variable (L)

theorem ofMilnorKQ_comp_ratToMilnorKQ :
    (ofMilnorKQ L).comp (ratToMilnorKQ L) = AlgHom.id ℚ _ :=
  ratAlgHom_ext fun a ↦ by
    rw [AlgHom.comp_apply, ratToMilnorKQ_tmul, one_smul, toMilnorKQ_ι, ofMilnorKQ_ι_cls,
      AlgHom.id_apply]

theorem ratToMilnorKQ_comp_ofMilnorKQ :
    (ratToMilnorKQ L).comp (ofMilnorKQ L) = AlgHom.id ℚ _ :=
  MilnorKQ.algHom_ext <| VOf.linearMap_ext fun a ↦ by
    simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, AlgHom.comp_apply,
      AlgHom.id_apply]
    rw [ofMilnorKQ_ι_cls, ratToMilnorKQ_tmul, one_smul, toMilnorKQ_ι]

/-- **Comparison with the paper's `𝒦_*(L) = ℚ ⊗ K^M_*(L)`.** The isomorphism of `ℚ`-algebras
`ℚ ⊗[ℤ] K^M_*(L) ≃ MilnorKQ ⊥`, sending `q ⊗ ι a` to `q • ι [a]` (`ratEquiv_one_tmul_ι`), hence
`1 ⊗ {a, b}` to `{a, b}` (`ratEquiv_one_tmul_symbol`). -/
noncomputable def ratEquiv : ℚ ⊗[ℤ] MilnorK L ≃ₐ[ℚ] MilnorKQ (⊥ : Subgroup Lˣ) :=
  AlgEquiv.ofAlgHom (ratToMilnorKQ L) (ofMilnorKQ L) (ratToMilnorKQ_comp_ofMilnorKQ L)
    (ofMilnorKQ_comp_ratToMilnorKQ L)

theorem ratEquiv_tmul (q : ℚ) (x : MilnorK L) : ratEquiv L (q ⊗ₜ x) = q • toMilnorKQ L x :=
  rfl

theorem ratEquiv_one_tmul (x : MilnorK L) : ratEquiv L ((1 : ℚ) ⊗ₜ x) = toMilnorKQ L x := by
  rw [ratEquiv_tmul, one_smul]

/-- The comparison isomorphism in degree one: `1 ⊗ ι a ↦ ι [a]`. -/
@[simp]
theorem ratEquiv_one_tmul_ι (a : Lˣ) :
    ratEquiv L ((1 : ℚ) ⊗ₜ ι L (.ofMul a)) = MilnorKQ.ι ⊥ (cls ⊥ (.ofMul a)) := by
  rw [ratEquiv_one_tmul, toMilnorKQ_ι]

/-- The comparison isomorphism on symbols: `1 ⊗ {a, b} ↦ {a, b}`. -/
@[simp]
theorem ratEquiv_one_tmul_symbol (a b : Lˣ) :
    ratEquiv L ((1 : ℚ) ⊗ₜ symbol L a b) = MilnorKQ.symbol ⊥ a b := by
  rw [ratEquiv_one_tmul, symbol, map_mul, toMilnorKQ_ι, toMilnorKQ_ι, MilnorKQ.symbol]

@[simp]
theorem ratEquiv_symm_ι_cls (a : Lˣ) :
    (ratEquiv L).symm (MilnorKQ.ι ⊥ (cls ⊥ (.ofMul a))) = (1 : ℚ) ⊗ₜ ι L (.ofMul a) := by
  rw [AlgEquiv.symm_apply_eq, ratEquiv_one_tmul_ι]

/-- The comparison isomorphism in degree one, for all elements: under the identification
`VOf ⊥ ≃ ℚ ⊗[ℤ] Additive Lˣ` (`VOf.botEquiv`), the inverse of `ratEquiv` restricted to degree one
is `id_ℚ ⊗ ι`. -/
theorem ratEquiv_symm_ι (v : VOf (⊥ : Subgroup Lˣ)) :
    (ratEquiv L).symm (MilnorKQ.ι ⊥ v) =
      (ι L).toIntLinearMap.baseChange ℚ (VOf.botEquiv L v) := by
  refine LinearMap.congr_fun (f := (ratEquiv L).symm.toLinearMap ∘ₗ MilnorKQ.ι ⊥)
    (g := (ι L).toIntLinearMap.baseChange ℚ ∘ₗ (VOf.botEquiv L).toLinearMap)
    (VOf.linearMap_ext fun a ↦ ?_) v
  simp only [LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, LinearEquiv.coe_coe,
    ratEquiv_symm_ι_cls, VOf.botEquiv_cls, LinearMap.baseChange_tmul]
  rfl

/-- The comparison isomorphism in degree one: `ratEquiv (q ⊗ ι a) = q • ι [a]`; more precisely,
`ratEquiv ∘ (id_ℚ ⊗ ι) = ι ∘ botEquiv⁻¹` on `ℚ ⊗[ℤ] Additive Lˣ`. -/
theorem ratEquiv_baseChange_ι (x : ℚ ⊗[ℤ] Additive Lˣ) :
    ratEquiv L ((ι L).toIntLinearMap.baseChange ℚ x) =
      MilnorKQ.ι ⊥ ((VOf.botEquiv L).symm x) := by
  rw [← AlgEquiv.eq_symm_apply, ratEquiv_symm_ι, LinearEquiv.apply_symm_apply]

section Functoriality

variable {L}

/-- The homomorphism `id_ℚ ⊗ τ_* : ℚ ⊗[ℤ] K^M_*(K) → ℚ ⊗[ℤ] K^M_*(L)` induced by a ring
homomorphism `τ : K →+* L`. -/
noncomputable def ratMap (τ : K →+* L) : ℚ ⊗[ℤ] MilnorK K →ₐ[ℚ] ℚ ⊗[ℤ] MilnorK L :=
  Algebra.TensorProduct.map (AlgHom.id ℚ ℚ) (map τ).toIntAlgHom

@[simp]
theorem ratMap_tmul (τ : K →+* L) (q : ℚ) (x : MilnorK K) : ratMap τ (q ⊗ₜ x) = q ⊗ₜ map τ x :=
  rfl

/-- The comparison isomorphism is compatible with the maps `τ_*` induced by a ring homomorphism
`τ : K →+* L`. -/
theorem ratEquiv_comp_ratMap (τ : K →+* L) :
    (ratEquiv L).toAlgHom.comp (ratMap τ) =
      (MilnorKQ.map τ bot_le).comp (ratEquiv K).toAlgHom :=
  ratAlgHom_ext fun a ↦ by
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, ratMap_tmul, map_ι, ratEquiv_one_tmul_ι,
      MilnorKQ.map_ι, mapRingHom_cls]

theorem ratEquiv_ratMap (τ : K →+* L) (x : ℚ ⊗[ℤ] MilnorK K) :
    ratEquiv L (ratMap τ x) = MilnorKQ.map τ bot_le (ratEquiv K x) :=
  AlgHom.congr_fun (ratEquiv_comp_ratMap τ) x

end Functoriality

section Grading

variable {L}

/-- `toMilnorKQ` is graded: it maps `K^M_n(L)` into `𝒦_n(L)`. -/
theorem toMilnorKQ_mem_grade {n : ℕ} {x : MilnorK L} (hx : x ∈ grade L n) :
    toMilnorKQ L x ∈ MilnorKQ.grade ⊥ n := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [algebraMap_int_eq, eq_intCast, map_intCast, ← map_intCast (algebraMap ℚ (MilnorKQ ⊥)) r]
    exact MilnorKQ.algebraMap_mem_grade_zero _
  | add x y i _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | mem_mul m hm i x _ hx =>
    obtain ⟨a, rfl⟩ := hm
    rw [map_mul, show toMilnorKQ L ((ι L).toIntLinearMap a) = MilnorKQ.ι ⊥ (cls ⊥ a) from
      toMilnorKQ_ι L (Additive.toMul a)]
    exact MilnorKQ.ι_mul_mem_grade _ hx

/-- The comparison isomorphism is graded: it maps `q ⊗ x` with `x ∈ K^M_n(L)` into `𝒦_n(L)`. -/
theorem ratEquiv_tmul_mem_grade (q : ℚ) {n : ℕ} {x : MilnorK L} (hx : x ∈ grade L n) :
    ratEquiv L (q ⊗ₜ x) ∈ MilnorKQ.grade ⊥ n := by
  rw [ratEquiv_tmul]
  exact Submodule.smul_mem _ q (toMilnorKQ_mem_grade hx)

variable (L) in
/-- The comparison isomorphism is graded: `𝒦_n(L)` is the `ℚ`-span of the image of
`1 ⊗ K^M_n(L)`. -/
theorem grade_bot_eq_span (n : ℕ) :
    MilnorKQ.grade (⊥ : Subgroup Lˣ) n =
      Submodule.span ℚ ((fun x ↦ ratEquiv L ((1 : ℚ) ⊗ₜ x)) '' grade L n) := by
  simp_rw [ratEquiv_one_tmul]
  refine le_antisymm (fun y hy ↦ ?_) (Submodule.span_le.2 ?_)
  · induction hy using Submodule.pow_induction_on_left' with
    | algebraMap q =>
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ q (Submodule.subset_span ⟨1, one_mem_grade_zero, map_one _⟩)
    | add x y i _ _ hx hy => exact add_mem hx hy
    | mem_mul m hm i x _ hx =>
      obtain ⟨v, rfl⟩ := hm
      obtain ⟨k, a, -, rfl⟩ := VOf.exists_eq_inv_smul_cls v
      rw [map_smul, smul_mul_assoc]
      refine Submodule.smul_mem _ _ ?_
      have key : Submodule.span ℚ (toMilnorKQ L '' grade L i) ≤
          (Submodule.span ℚ (toMilnorKQ L '' grade L (i + 1))).comap
            (LinearMap.mulLeft ℚ (MilnorKQ.ι ⊥ (cls ⊥ (.ofMul a)))) := by
        rw [Submodule.span_le]
        rintro _ ⟨y, hy, rfl⟩
        refine Submodule.subset_span ⟨ι L (.ofMul a) * y, ?_, ?_⟩
        · rw [grade, pow_succ']
          exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) hy
        · rw [map_mul, toMilnorKQ_ι]
          rfl
      exact key hx
  · rintro _ ⟨x, hx, rfl⟩
    exact toMilnorKQ_mem_grade hx

/-- The comparison isomorphism is graded, stated with `Submodule.baseChange`: it maps
`ℚ ⊗ K^M_n(L)` (the `ℚ`-span of `1 ⊗ K^M_n(L)`) onto `𝒦_n(L)`. -/
theorem map_baseChange_grade (n : ℕ) :
    ((grade L n).baseChange ℚ).map (ratEquiv L).toLinearMap = MilnorKQ.grade ⊥ n := by
  rw [Submodule.baseChange_eq_span, Submodule.map_span, grade_bot_eq_span, Submodule.map_coe,
    Set.image_image]
  rfl

/-- The comparison isomorphism is compatible with `r^deg`: if `x ∈ K^M_n(L)`, then
`r^deg (q ⊗ x) = (r ^ n q) ⊗ x`. -/
theorem degScale_ratEquiv_tmul (r q : ℚ) {n : ℕ} {x : MilnorK L} (hx : x ∈ grade L n) :
    MilnorKQ.degScale ⊥ r (ratEquiv L (q ⊗ₜ x)) = ratEquiv L ((r ^ n * q) ⊗ₜ x) := by
  rw [MilnorKQ.degScale_apply_of_mem_grade r (ratEquiv_tmul_mem_grade q hx), ratEquiv_tmul,
    ratEquiv_tmul, mul_smul]

end Grading

end MilnorK

end MilnorAlgDep
