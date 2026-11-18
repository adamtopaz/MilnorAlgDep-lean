module

public import MilnorAlgDep.CharP.Frobenius
public import MilnorAlgDep.Standard.Differentials
public import MilnorAlgDep.Standard.SepCrit

/-!
# Models

Blueprint, Section 4: Definition 4.1 and Lemma 4.2, together with the two facts about
differentials in a model which Sections 3-6 use: the separability criterion (replacing
Lemma 3.1, see `MilnorAlgDep.Standard.SepCrit`) and the lax property in its general form
(Lemma 4.5, `lem:lax`).

Numbering: Definition 4.1 (model), Lemma 4.2 (`lem:model`), Lemma 4.3 (`lem:pointsmodel`),
Definition 4.4 (model level, height, line), Lemma 4.5 (`lem:lax`), Lemma 4.6 (`lem:trichotomy`).

For a family `B : ι → L` the *model* `model l B` is the intermediate field of the elements of `L`
which are separable algebraic over `l(B)`. The blueprint only uses it for a transcendence basis
`B` of `L / l` (the field `L_A`, with `Ω_A = Ω[L_A⁄l]`), but the proofs of Sections 3 and 6 also
use it for small algebraically independent families, e.g. `B = ![x, y]` (the field `E` of
"elements separable algebraic over `l(x, y)`" in the proofs of Lemmas 3.5 and 6.2). So it is
defined for every family, and the results assume what they need (`AlgebraicIndependent l B` or
`IsTranscendenceBasis l B`).

`modelD l B y ∈ Ω[model l B⁄l]` is the differential `d y` of `y ∈ L_B`; it is `0` (junk) if
`y ∉ L_B`, so statements about `modelD l B y` should also say `y ∈ model l B`.

## Main definitions

* `MilnorAlgDep.model l B : IntermediateField l L`: the model `L_B` (Definition 4.1).
* `MilnorAlgDep.modelD l B : L → Ω[model l B⁄l]`: `y ↦ d y` on `L_B`, `0` elsewhere.
* `MilnorAlgDep.modelBasis`: the basis `(d B i)ᵢ` of `Ω[L_B⁄l]` (Lemma 4.2(a)).

## Main statements

* `mem_model_of_isSeparable` (Lemma 4.2(b)), `exists_pow_pow_mem_model` (Lemma 4.2(c)).
* `isSeparable_of_linearIndependent_modelD`: if `d xᵢ` are linearly independent in `Ω[L_B⁄l]`
  and `y ∈ L_B` is algebraic over `l(x)`, then `y` is separable over `l(x)` (the differential form
  of Lemma 3.1(c), used in Lemmas 3.2, 3.5, 4.6(d) and 6.2).
* `algebraicIndependent_of_linearIndependent_modelD`: Lemma 4.5 (lax property), general form.
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential IntermediateField

variable {l L : Type*} [Field l] [Field L] [Algebra l L] {ι κ : Type*}

section Defs

variable (l) in
/-- **Blueprint Definition 4.1**: the *model* `L_B`, the field of elements of `L` which are
separable algebraic over `l(B)`. The blueprint takes `B` a transcendence basis of `L / l`; here
`B` is any family. -/
noncomputable def model (B : ι → L) : IntermediateField l L :=
  (separableClosure (adjoin l (Set.range B)) L).restrictScalars l

theorem mem_model_iff {B : ι → L} {y : L} :
    y ∈ model l B ↔ IsSeparable (adjoin l (Set.range B)) y := by
  rw [model, mem_restrictScalars, mem_separableClosure_iff]

theorem self_mem_model (B : ι → L) (i : ι) : B i ∈ model l B :=
  mem_separableClosure_adjoin B i

open Classical in
variable (l) in
/-- The differential `d y ∈ Ω_B = Ω[L_B⁄l]` of an element `y ∈ L_B`; by convention `0` if
`y ∉ L_B` (so `modelD l B y ≠ 0` implies `y ∈ L_B`, see `mem_model_of_modelD_ne_zero`). -/
noncomputable def modelD (B : ι → L) (y : L) : Ω[model l B⁄l] :=
  if h : y ∈ model l B then D l (model l B) ⟨y, h⟩ else 0

theorem modelD_of_mem {B : ι → L} {y : L} (h : y ∈ model l B) :
    modelD l B y = D l (model l B) ⟨y, h⟩ :=
  dite_eq_left h

theorem modelD_of_notMem {B : ι → L} {y : L} (h : y ∉ model l B) : modelD l B y = 0 :=
  dite_eq_right h

theorem mem_model_of_modelD_ne_zero {B : ι → L} {y : L} (h : modelD l B y ≠ 0) :
    y ∈ model l B := by
  by_contra hy
  exact h (modelD_of_notMem hy)

@[simp]
theorem modelD_coe {B : ι → L} (y : model l B) : modelD l B y = D l (model l B) y :=
  modelD_of_mem y.2

theorem modelD_algebraMap (B : ι → L) (c : l) : modelD l B (algebraMap l L c) = 0 := by
  rw [modelD_of_mem (IntermediateField.algebraMap_mem _ c)]
  exact (D l (model l B)).map_algebraMap c

theorem modelD_add {B : ι → L} {x y : L} (hx : x ∈ model l B) (hy : y ∈ model l B) :
    modelD l B (x + y) = modelD l B x + modelD l B y := by
  rw [modelD_of_mem hx, modelD_of_mem hy, modelD_of_mem (add_mem hx hy), ← map_add]
  rfl

theorem modelD_mul {B : ι → L} {x y : L} (hx : x ∈ model l B) (hy : y ∈ model l B) :
    modelD l B (x * y) =
      (⟨x, hx⟩ : model l B) • modelD l B y + (⟨y, hy⟩ : model l B) • modelD l B x := by
  rw [modelD_of_mem hx, modelD_of_mem hy, modelD_of_mem (mul_mem hx hy), ← Derivation.leibniz]
  rfl

theorem modelD_pow_char (p : ℕ) [CharP L p] {B : ι → L} {y : L} (hy : y ∈ model l B) :
    modelD l B (y ^ p) = 0 := by
  have : CharP (model l B) p := (Algebra.charP_iff (model l B) L p).mpr inferInstance
  rw [modelD_of_mem (pow_mem hy p)]
  exact kaehler_D_pow_char p (⟨y, hy⟩ : model l B)

end Defs

section Transfer

/-! ### Intermediate fields of an intermediate field

For `M : IntermediateField l L` and `S ⊆ M`, the fields `l(S) ⊆ M` and `l(S) ⊆ L` are identified
by `adjoinValEquiv`; algebraicity and separability of elements of `M` over them agree. -/

variable (M : IntermediateField l L) (S : Set M)

/-- The `l`-algebra isomorphism between `l(S) ⊆ M` and `l(S) ⊆ L`, for `S ⊆ M`. -/
noncomputable def adjoinValEquiv : adjoin l S ≃ₐ[l] adjoin l (Subtype.val '' S) :=
  (liftAlgEquiv (adjoin l S)).trans (equivOfEq (lift_adjoin (K := M) (S := S)))

theorem coe_adjoinValEquiv (k : adjoin l S) : (adjoinValEquiv M S k : L) = ((k : M) : L) :=
  rfl

theorem algebraMap_comp_adjoinValEquiv :
    (algebraMap (adjoin l (Subtype.val '' S)) L).comp (adjoinValEquiv M S : adjoin l S →+* _) =
      (M.val : M →+* L).comp (algebraMap (adjoin l S) M) :=
  rfl

variable {M S}

theorem isAlgebraic_adjoin_val_iff {y : M} :
    IsAlgebraic (adjoin l (Subtype.val '' S)) (y : L) ↔ IsAlgebraic (adjoin l S) y :=
  ⟨fun h ↦ h.of_ringHom_of_comp_eq (adjoinValEquiv M S) M.val (adjoinValEquiv M S).surjective
      M.val.injective (algebraMap_comp_adjoinValEquiv M S),
    fun h ↦ h.ringHom_of_comp_eq (adjoinValEquiv M S) M.val (adjoinValEquiv M S).injective
      (algebraMap_comp_adjoinValEquiv M S)⟩

theorem minpoly_adjoin_val {y : M} (hy : IsIntegral (adjoin l S) y) :
    minpoly (adjoin l (Subtype.val '' S)) (y : L) =
      (minpoly (adjoin l S) y).map (adjoinValEquiv M S : adjoin l S →+* _) := by
  refine (minpoly.eq_of_irreducible_of_monic ?_ ?_ ((minpoly.monic hy).map _)).symm
  · have : (minpoly (adjoin l S) y).map (adjoinValEquiv M S : adjoin l S →+* _) =
        Polynomial.mapEquiv (adjoinValEquiv M S).toRingEquiv (minpoly (adjoin l S) y) := rfl
    rw [this, MulEquiv.irreducible_iff]
    exact minpoly.irreducible hy
  · have := Polynomial.map_aeval_eq_aeval_map (algebraMap_comp_adjoinValEquiv M S)
      (minpoly (adjoin l S) y) y
    rw [minpoly.aeval, map_zero] at this
    exact this.symm

theorem isSeparable_adjoin_val_iff {y : M} :
    IsSeparable (adjoin l (Subtype.val '' S)) (y : L) ↔ IsSeparable (adjoin l S) y := by
  constructor
  · intro h
    have hint : IsIntegral (adjoin l S) y :=
      (isAlgebraic_adjoin_val_iff.1 h.isIntegral.isAlgebraic).isIntegral
    rw [IsSeparable, minpoly_adjoin_val hint, Polynomial.separable_map] at h
    exact h
  · intro h
    rw [IsSeparable, minpoly_adjoin_val h.isIntegral, Polynomial.separable_map]
    exact h

end Transfer

section Basis

variable {B : ι → L}

/-- **Blueprint Lemma 4.2(a)** ((S2) for the model): if `B` is algebraically independent over `l`,
then `(d B i)ᵢ` is a basis of the `L_B`-vector space `Ω_B = Ω[L_B⁄l]`; see `modelBasis_apply`. -/
noncomputable def modelBasis (hB : AlgebraicIndependent l B) :
    Module.Basis ι (model l B) Ω[model l B⁄l] :=
  kaehlerBasis (algebraicIndependent_restrictFamily _ (mem_separableClosure_adjoin B) hB)
    (isSeparable_adjoin_restrictFamily_separableClosure B)

@[simp]
theorem modelBasis_apply (hB : AlgebraicIndependent l B) (i : ι) :
    modelBasis hB i = modelD l B (B i) := by
  rw [modelD_of_mem (self_mem_model B i)]
  exact kaehlerBasis_apply _ _ i

theorem linearIndependent_modelD (hB : AlgebraicIndependent l B) :
    LinearIndependent (model l B) fun i ↦ modelD l B (B i) := by
  have h := (modelBasis hB).linearIndependent
  rwa [show ⇑(modelBasis hB) = fun i ↦ modelD l B (B i) from funext (modelBasis_apply hB)] at h

/-- **Blueprint Lemma 4.2(b)**, for `j = 0`, in a form which also covers the use of (b) in the
proof of Lemma 4.3: if `y` is separable algebraic over an intermediate field `K ⊆ L_B`, then
`y ∈ L_B`. (The case `j > 0` follows by applying `frobZ L p (-j)`.) -/
theorem mem_model_of_isSeparable {K : IntermediateField l L} (hK : K ≤ model l B) {y : L}
    (hy : IsSeparable K y) : y ∈ model l B := by
  set F := adjoin l (Set.range B)
  set M := separableClosure F L
  let i : K →ₐ[l] model l B := IntermediateField.inclusion hK
  let : Algebra K M := (i.toRingHom : K →+* M).toAlgebra
  have : IsScalarTower K M L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  rw [mem_model_iff]
  exact IsSeparable.of_algebra_isSeparable_of_isSeparable F (hy.tower_top M)

variable (p : ℕ) [Fact p.Prime] [CharP L p]

/-- **Blueprint Lemma 4.2(c)**: if `y` is algebraic over `l(B)` (e.g. `B` a transcendence basis),
then `y ^ p ^ n ∈ L_B` for some `n`, i.e. `y ∈ Frob^{-n}(L_B)`. -/
theorem exists_pow_pow_mem_model {y : L} (hy : IsAlgebraic (adjoin l (Set.range B)) y) :
    ∃ n : ℕ, y ^ p ^ n ∈ model l B := by
  have : CharP (adjoin l (Set.range B)) p :=
    (Algebra.charP_iff (adjoin l (Set.range B)) L p).mpr inferInstance
  obtain ⟨n, hn⟩ := exists_isSeparable_pow_pow p hy
  exact ⟨n, mem_model_iff.2 hn⟩

end Basis

section Differentials

variable {B : ι → L} [PerfectField l]

/-- **Separability criterion** (differential form of blueprint Lemma 3.1(c)): if `xₖ ∈ L_B` have
linearly independent differentials in `Ω_B` and `y ∈ L_B` is algebraic over `l(x)`, then `y` is
separable over `l(x)`.

This replaces the irreducible relation of Lemma 3.1 in the proofs of Lemmas 3.2, 3.5, 4.6(d) and
6.2: e.g. if `X, Y, Z ∈ L_B` are collinear and `d X, d Z` are linearly independent, then `Y` is
separable over `l(X, Z)`. -/
theorem isSeparable_of_linearIndependent_modelD {x : κ → L} (hx : ∀ k, x k ∈ model l B)
    (hli : LinearIndependent (model l B) fun k ↦ modelD l B (x k)) {y : L} (hy : y ∈ model l B)
    (halg : IsAlgebraic (adjoin l (Set.range x)) y) : IsSeparable (adjoin l (Set.range x)) y := by
  set x' : κ → model l B := fun k ↦ ⟨x k, hx k⟩
  have himage : Subtype.val '' Set.range x' = Set.range x := by
    rw [← Set.range_comp]
    rfl
  have hli' : LinearIndependent (model l B) fun k ↦ D l (model l B) (x' k) := by
    simpa only [modelD_of_mem (hx _)] using hli
  have halg' : IsAlgebraic (adjoin l (Set.range x')) (⟨y, hy⟩ : model l B) := by
    rw [← isAlgebraic_adjoin_val_iff, himage]
    exact halg
  have := isSeparable_adjoin_of_linearIndependent_kaehler_D hli' halg'
  rw [← isSeparable_adjoin_val_iff, himage] at this
  exact this

/-- The separability criterion `isSeparable_of_linearIndependent_modelD` for two elements: if
`x, z, y ∈ L_B`, `d x, d z` are linearly independent and `y` is algebraic over `l(x, z)`, then `y`
is separable over `l(x, z)`. -/
theorem isSeparable_of_linearIndependent_modelD_pair {x z y : L} (hx : x ∈ model l B)
    (hz : z ∈ model l B) (hli : LinearIndependent (model l B) ![modelD l B x, modelD l B z])
    (hy : y ∈ model l B) (halg : IsAlgebraic l⟮x, z⟯ y) : IsSeparable l⟮x, z⟯ y := by
  have hrange : Set.range ![x, z] = {x, z} := Matrix.range_cons_cons_empty x z _
  have hx' : ∀ k, ![x, z] k ∈ model l B := by
    intro k
    fin_cases k
    exacts [hx, hz]
  have hli' : LinearIndependent (model l B) fun k ↦ modelD l B (![x, z] k) := by
    convert hli using 1
    ext k
    fin_cases k <;> rfl
  have := isSeparable_of_linearIndependent_modelD hx' hli' hy (by rwa [hrange])
  rwa [hrange] at this

/-- **Blueprint Lemma 4.5 (Lax property)**, general form: elements of `L_B` whose differentials
are linearly independent in `Ω_B` are algebraically independent over `l`. (Equivalently,
algebraically dependent elements of `L_B` have linearly dependent differentials; the blueprint's
statement about the lines of points is `not_linearIndependent_modelD_of_not_algebraicIndependent`
in `MilnorAlgDep.CharP.Models`.) -/
theorem algebraicIndependent_of_linearIndependent_modelD {x : κ → L} (hx : ∀ k, x k ∈ model l B)
    (hli : LinearIndependent (model l B) fun k ↦ modelD l B (x k)) : AlgebraicIndependent l x := by
  have hli' : LinearIndependent (model l B) fun k ↦ D l (model l B) ⟨x k, hx k⟩ := by
    simpa only [modelD_of_mem (hx _)] using hli
  exact (algebraicIndependent_of_linearIndependent_kaehler_D hli').map'
    (f := (model l B).val) (model l B).val.injective

end Differentials

end MilnorAlgDep
