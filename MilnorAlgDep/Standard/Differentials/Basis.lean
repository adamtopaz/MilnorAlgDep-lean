module

public import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Kaehler.Polynomial
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree

/-!
# Kähler differentials of separably generated field extensions

This file formalizes the first half of blueprint Lemma 2.1 (`lem:standard`), part (S2):
if a field `E ⊇ l` is separable algebraic over `l(a)` for an algebraically independent family
`a : ι → E`, then `(d aᵢ)ᵢ` is a basis of the `E`-vector space `Ω[E⁄l]`.

Throughout, "`E` is separable algebraic over `l(a)`" is expressed as
`Algebra.IsSeparable (IntermediateField.adjoin l (Set.range a)) E`, passed as an *explicit*
hypothesis. Use `algebraIsSeparable_adjoin_of_forall` to produce it from the elementwise
statement.

## Proof

Everything is in Mathlib: `MvPolynomial ι l → l(a)` (evaluation at `a`) is a localization, hence
formally étale (`Algebra.FormallyEtale.of_isLocalization`); `l(a) → E` is separable, hence
formally étale (`Algebra.FormallyEtale.of_isSeparable`). Hence
`E ⊗ Ω[MvPolynomial ι l⁄l] ≃ Ω[E⁄l]` (`KaehlerDifferential.isBaseChange_of_formallyEtale`), and
the former has the basis `(1 ⊗ d Xᵢ)ᵢ` (`KaehlerDifferential.mvPolynomialBasis`,
`IsBaseChange.basis`).

## Main results

* `MilnorAlgDep.kaehlerBasis`: the basis `(d aᵢ)ᵢ` of `Ω[E⁄l]` (`kaehlerBasis_apply`).
* `MilnorAlgDep.linearIndependent_kaehler_D`, `MilnorAlgDep.span_kaehler_D_eq_top`.
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential MvPolynomial IntermediateField

variable {l E : Type*} [Field l] [Field E] [Algebra l E]
variable {ι : Type*} {a : ι → E}

/-- Convert the elementwise formulation of "`E` is separable algebraic over `l(a)`" into the one
used in this file. -/
theorem algebraIsSeparable_adjoin_of_forall (S : Set E) (h : ∀ x : E, IsSeparable (adjoin l S) x) :
    Algebra.IsSeparable (adjoin l S) E :=
  ⟨h⟩

namespace KaehlerBasis

/-- The family `a`, viewed in `l(a)`. -/
def gen (a : ι → E) (i : ι) : adjoin l (Set.range a) :=
  ⟨a i, subset_adjoin _ _ ⟨i, rfl⟩⟩

@[simp] lemma coe_gen (i : ι) : (gen (l := l) a i : E) = a i := rfl

lemma coe_aeval_gen (g : MvPolynomial ι l) :
    ((aeval (gen (l := l) a) g : adjoin l (Set.range a)) : E) = aeval a g := by
  rw [← IntermediateField.algebraMap_apply, ← IsScalarTower.coe_toAlgHom' l, ← AlgHom.comp_apply,
    MvPolynomial.comp_aeval]
  rfl

lemma algebraicIndependent_gen (hb : AlgebraicIndependent l a) :
    AlgebraicIndependent l (gen (l := l) a) :=
  AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom l (adjoin l (Set.range a)) E) hb

/-- `l(a)` as an algebra over `MvPolynomial ι l`, via evaluation at `a`. -/
noncomputable abbrev algebraAdjoin (a : ι → E) :
    Algebra (MvPolynomial ι l) (adjoin l (Set.range a)) :=
  (aeval (gen (l := l) a)).toAlgebra

/-- `E` as an algebra over `MvPolynomial ι l`, via evaluation at `a`. -/
noncomputable abbrev algebraE (a : ι → E) : Algebra (MvPolynomial ι l) E :=
  (aeval a).toAlgebra

section

variable [Algebra (MvPolynomial ι l) (adjoin l (Set.range a))]

/-- `l(a)` is the fraction field of `MvPolynomial ι l`. -/
lemma isFractionRing (hb : AlgebraicIndependent l a)
    (h : ∀ g, algebraMap (MvPolynomial ι l) (adjoin l (Set.range a)) g = aeval (gen a) g) :
    IsFractionRing (MvPolynomial ι l) (adjoin l (Set.range a)) := by
  have : FaithfulSMul (MvPolynomial ι l) (adjoin l (Set.range a)) := by
    refine (faithfulSMul_iff_algebraMap_injective _ _).mpr ?_
    convert algebraicIndependent_iff_injective_aeval.mp (algebraicIndependent_gen hb)
    ext1 g
    exact h g
  refine IsFractionRing.of_field _ _ fun z ↦ ?_
  obtain ⟨r, hr, s, hs, hz⟩ := mem_adjoin_iff_div.mp z.2
  rw [Algebra.adjoin_range_eq_range_aeval] at hr hs
  obtain ⟨g, rfl⟩ := hr
  obtain ⟨g', rfl⟩ := hs
  refine ⟨g, g', Subtype.ext ?_⟩
  simp only [IntermediateField.coe_div, h, coe_aeval_gen, hz]
  rfl

variable [Algebra (MvPolynomial ι l) E]

/-- `E` is formally étale over `MvPolynomial ι l`. -/
lemma formallyEtale (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E)
    (h : ∀ g, algebraMap (MvPolynomial ι l) (adjoin l (Set.range a)) g = aeval (gen a) g)
    (h' : ∀ g, algebraMap (MvPolynomial ι l) E g = aeval a g) :
    Algebra.FormallyEtale (MvPolynomial ι l) E := by
  have := isFractionRing hb h
  have : IsScalarTower (MvPolynomial ι l) (adjoin l (Set.range a)) E :=
    IsScalarTower.of_algebraMap_eq fun g ↦ by
      rw [h, h', IntermediateField.algebraMap_apply, coe_aeval_gen]
  have : Algebra.FormallyEtale (MvPolynomial ι l) (adjoin l (Set.range a)) :=
    .of_isLocalization (nonZeroDivisors _)
  have : Algebra.FormallyEtale (adjoin l (Set.range a)) E := .of_isSeparable _ _
  exact .comp _ (adjoin l (Set.range a)) _

end

/-- `Ω[E⁄l]` is the base change of `Ω[MvPolynomial ι l⁄l]` along evaluation at `a`. -/
lemma isBaseChange (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) :
    letI := algebraE (l := l) a
    IsBaseChange E (KaehlerDifferential.map l l (MvPolynomial ι l) E) := by
  let := algebraE (l := l) a
  let := algebraAdjoin (l := l) a
  have : IsScalarTower l (MvPolynomial ι l) E :=
    IsScalarTower.of_algebraMap_eq fun c ↦ (aeval_C a c).symm
  have := formallyEtale hb hsep (fun _ ↦ rfl) (fun _ ↦ rfl)
  exact isBaseChange_of_formallyEtale l _ E

end KaehlerBasis

open KaehlerBasis in
/-- **Blueprint Lemma 2.1 (S2), basis.** If `a` is algebraically independent over `l` and `E`
is separable algebraic over `l(a)`, then `(d aᵢ)ᵢ` is a basis of the `E`-vector space
`Ω[E⁄l]`. See `kaehlerBasis_apply`. -/
noncomputable def kaehlerBasis (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) : Module.Basis ι E Ω[E⁄l] :=
  letI := algebraE (l := l) a
  (isBaseChange hb hsep).basis (mvPolynomialBasis l ι)

open KaehlerBasis in
@[simp]
theorem kaehlerBasis_apply (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) (i : ι) :
    kaehlerBasis hb hsep i = D l E (a i) := by
  let := algebraE (l := l) a
  rw [kaehlerBasis, IsBaseChange.basis_apply, mvPolynomialBasis_apply, map_D]
  exact congrArg _ (aeval_X a i)

theorem coe_kaehlerBasis (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) :
    ⇑(kaehlerBasis hb hsep) = fun i ↦ D l E (a i) :=
  funext (kaehlerBasis_apply hb hsep)

/-- **Blueprint Lemma 2.1 (S2), basis**, linear independence: if `a` is algebraically
independent over `l` and `E` is separable algebraic over `l(a)`, then the `d aᵢ` are linearly
independent over `E`. -/
theorem linearIndependent_kaehler_D (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) :
    LinearIndependent E fun i ↦ D l E (a i) := by
  rw [← coe_kaehlerBasis hb hsep]
  exact (kaehlerBasis hb hsep).linearIndependent

/-- **Blueprint Lemma 2.1 (S2), basis**, spanning: if `a` is algebraically independent over `l`
and `E` is separable algebraic over `l(a)`, then the `d aᵢ` span `Ω[E⁄l]`. -/
theorem span_kaehler_D_eq_top (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) :
    Submodule.span E (Set.range fun i ↦ D l E (a i)) = ⊤ := by
  rw [← coe_kaehlerBasis hb hsep]
  exact (kaehlerBasis hb hsep).span_eq

/-- If `E` is separable algebraic over `l(x)` with `x` transcendental over `l`, there is an
`l`-derivation `δ` of `E` with `δ x = 1`: the coordinate of `d : E → Ω[E⁄l]` along the basis
`d x` (`MilnorAlgDep.kaehlerBasis`). -/
theorem exists_derivation_apply_eq_one {a : Unit → E}
    (hb : AlgebraicIndependent l a) (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) :
    ∃ δ : Derivation l E E, δ (a ()) = 1 := by
  let b := kaehlerBasis hb hsep
  refine ⟨(b.coord ()).compDer (D l E), ?_⟩
  change b.coord () (D l E (a ())) = 1
  rw [← kaehlerBasis_apply hb hsep (), Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same]

end MilnorAlgDep
