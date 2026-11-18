module

public import MilnorAlgDep.Standard.Differentials.Basis
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Flat.Basic

/-!
# Functoriality of `Ω` for field extensions

Standard facts used in the blueprint around Lemma 6.10 (`lem:tauinQ`, line 656) and in the proof of
Proposition 6.12 (line 708): for fields `l ⊆ E ⊆ E'`,

* if `E'` is separable algebraic over `E`, then `E' ⊗[E] Ω[E⁄l] ≃ Ω[E'⁄l]`
  (`MilnorAlgDep.kaehlerTensorEquivOfIsSeparable`) and `Ω[E⁄l] → Ω[E'⁄l]` is injective
  (`MilnorAlgDep.kaehler_map_injective_of_isSeparable`);
* if `E` is separable algebraic over `l(a)` with `a` algebraically independent, and the
  differentials `d aᵢ` stay linearly independent in `Ω[E'⁄l]`, then `E' ⊗[E] Ω[E⁄l] → Ω[E'⁄l]`
  and `Ω[E⁄l] → Ω[E'⁄l]` are injective
  (`MilnorAlgDep.kaehler_mapBaseChange_injective_of_linearIndependent`,
  `MilnorAlgDep.kaehler_map_injective_of_linearIndependent`). For a single generator `a` the
  hypothesis is `d a ≠ 0` in `Ω[E'⁄l]` (`MilnorAlgDep.kaehler_map_injective_of_ne_zero`).
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential IntermediateField
open scoped TensorProduct

variable {l E E' : Type*} [Field l] [Field E] [Field E'] [Algebra l E] [Algebra E E']
  [Algebra l E'] [IsScalarTower l E E']

/-- A linear map sending a basis to a linearly independent family is injective. -/
theorem injective_of_basis_of_linearIndependent {R M N ι : Type*} [CommRing R] [AddCommGroup M]
    [AddCommGroup N] [Module R M] [Module R N] (f : M →ₗ[R] N) (b : Module.Basis ι R M)
    (h : LinearIndependent R (f ∘ b)) : Function.Injective f := by
  have := b.injective_constr_of_linearIndependent (R₂ := R) h
  rwa [show b.constr R (f ∘ b) = f from b.constr_self R f] at this

variable (l E E') in
/-- If `E'` is separable algebraic over `E`, then `E' ⊗[E] Ω[E⁄l] ≃ Ω[E'⁄l]`. -/
noncomputable def kaehlerTensorEquivOfIsSeparable [Algebra.IsSeparable E E'] :
    E' ⊗[E] Ω[E⁄l] ≃ₗ[E'] Ω[E'⁄l] :=
  have : Algebra.FormallyEtale E E' := .of_isSeparable E E'
  tensorKaehlerEquivOfFormallyEtale l E E'

theorem kaehlerTensorEquivOfIsSeparable_tmul [Algebra.IsSeparable E E'] (x : E')
    (ω : Ω[E⁄l]) :
    kaehlerTensorEquivOfIsSeparable l E E' (x ⊗ₜ ω) = x • map l l E E' ω := by
  simp [kaehlerTensorEquivOfIsSeparable]

variable (l E E') in
/-- If `E'` is separable algebraic over `E`, then `Ω[E⁄l] → Ω[E'⁄l]` is injective. -/
theorem kaehler_map_injective_of_isSeparable [Algebra.IsSeparable E E'] :
    Function.Injective (map l l E E') := by
  intro x y hxy
  apply Module.Flat.tensorProduct_mk_injective E Ω[E⁄l] E'
  apply (kaehlerTensorEquivOfIsSeparable l E E').injective
  simpa [kaehlerTensorEquivOfIsSeparable_tmul] using hxy

variable {ι : Type*} {a : ι → E}

/-- If `E` is separable algebraic over `l(a)` with `a` algebraically independent and the
`d aᵢ` are linearly independent in `Ω[E'⁄l]`, then `E' ⊗[E] Ω[E⁄l] → Ω[E'⁄l]` is injective. -/
theorem kaehler_mapBaseChange_injective_of_linearIndependent (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E)
    (h : LinearIndependent E' fun i ↦ D l E' (algebraMap E E' (a i))) :
    Function.Injective (mapBaseChange l E E') := by
  refine injective_of_basis_of_linearIndependent _ ((kaehlerBasis hb hsep).baseChange E') ?_
  convert h using 1
  ext i
  simp

/-- If `E` is separable algebraic over `l(a)` with `a` algebraically independent and the
`d aᵢ` are linearly independent in `Ω[E'⁄l]`, then `Ω[E⁄l] → Ω[E'⁄l]` is injective. -/
theorem kaehler_map_injective_of_linearIndependent (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E)
    (h : LinearIndependent E' fun i ↦ D l E' (algebraMap E E' (a i))) :
    Function.Injective (map l l E E') := by
  have h1 := kaehler_mapBaseChange_injective_of_linearIndependent hb hsep h
  have h2 := Module.Flat.tensorProduct_mk_injective E Ω[E⁄l] E'
  convert h1.comp h2 using 1
  ext ω
  simp

/-- Single generator case (blueprint line 656): if `E` is separable algebraic over `l(a)` with
`a` transcendental over `l` and `d a ≠ 0` in `Ω[E'⁄l]`, then `Ω[E⁄l] → Ω[E'⁄l]` is injective. -/
theorem kaehler_map_injective_of_ne_zero {x : E} (hx : Transcendental l x)
    (hsep : Algebra.IsSeparable (adjoin l {x}) E) (h : D l E' (algebraMap E E' x) ≠ 0) :
    Function.Injective (map l l E E') := by
  have hb : AlgebraicIndependent l fun _ : Unit ↦ x := algebraicIndependent_unique_type_iff.mpr hx
  have hsep' : Algebra.IsSeparable (adjoin l (Set.range fun _ : Unit ↦ x)) E := by
    rwa [Set.range_const]
  exact kaehler_map_injective_of_linearIndependent hb hsep'
    (linearIndependent_unique_iff.mpr h)

end MilnorAlgDep
