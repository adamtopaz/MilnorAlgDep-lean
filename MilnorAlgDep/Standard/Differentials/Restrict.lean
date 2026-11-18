module

public import MilnorAlgDep.Standard.Differentials.Basis
public import Mathlib.FieldTheory.SeparableClosure

/-!
# Separably generated intermediate fields

The results of `MilnorAlgDep.Standard.Differentials` are stated for a field `E` over `l` with a
family `a : ι → E`. In the blueprint they are applied to intermediate fields `E` of a big field
`L`, given as "the elements of `L` separable algebraic over `l(a)`" (the model `L_A` of Section 4,
and the fields `E` in the proofs of Lemma 6.3 and Proposition 6.9). This file provides the
translation: for `E : IntermediateField l L` containing the `aᵢ`,

* `MilnorAlgDep.algebraicIndependent_restrictFamily`: `a` stays algebraically independent in `E`;
* `MilnorAlgDep.isSeparable_adjoin_restrictFamily`: if every element of `E` is separable over
  `l(a) ⊆ L`, then `E` is separable over `l(a) ⊆ E`;
* `MilnorAlgDep.isSeparable_adjoin_restrictFamily_separableClosure`: the case
  `E = {y ∈ L | y separable over l(a)}`;
* `MilnorAlgDep.relAlgClosed_intermediateField`: relative algebraic closedness of `l` passes
  from `L` to `E`.
-/

@[expose] public section

namespace MilnorAlgDep

open IntermediateField

variable {l L : Type*} [Field l] [Field L] [Algebra l L] {ι : Type*}

/-- A family `a` of elements of an intermediate field `E`, viewed in `E`. -/
def restrictFamily (E : IntermediateField l L) (a : ι → L) (ha : ∀ i, a i ∈ E) (i : ι) : E :=
  ⟨a i, ha i⟩

@[simp] theorem coe_restrictFamily (E : IntermediateField l L) (a : ι → L) (ha : ∀ i, a i ∈ E)
    (i : ι) : (restrictFamily E a ha i : L) = a i := rfl

/-- An algebraically independent family in an intermediate field `E` stays algebraically
independent when viewed in `E`. -/
theorem algebraicIndependent_restrictFamily (E : IntermediateField l L) {a : ι → L}
    (ha : ∀ i, a i ∈ E) (hb : AlgebraicIndependent l a) :
    AlgebraicIndependent l (restrictFamily E a ha) :=
  AlgebraicIndependent.of_comp E.val hb

/-- If every element of the intermediate field `E ∋ aᵢ` is separable over `l(a) ⊆ L`, then `E` is
separable algebraic over `l(a) ⊆ E`, i.e. the hypothesis of `MilnorAlgDep.kaehlerBasis` holds
for `E`. -/
theorem isSeparable_adjoin_restrictFamily (E : IntermediateField l L) {a : ι → L}
    (ha : ∀ i, a i ∈ E) (hsep : ∀ y ∈ E, IsSeparable (adjoin l (Set.range a)) y) :
    Algebra.IsSeparable (adjoin l (Set.range (restrictFamily E a ha))) E := by
  set K := adjoin l (Set.range a)
  set K' := adjoin l (Set.range (restrictFamily E a ha))
  have hKE : K ≤ E := adjoin_le_iff.mpr (by rintro _ ⟨i, rfl⟩; exact ha i)
  let incl : K →ₐ[l] E := IntermediateField.inclusion hKE
  have hmap : K'.map E.val = K := by
    rw [adjoin_map, ← Set.range_comp]
    rfl
  have hK' : ∀ k : K, incl k ∈ K' := by
    intro k
    have hk : (k : L) ∈ K'.map E.val := by
      rw [hmap]
      exact k.2
    obtain ⟨x, hx, hxk⟩ := hk
    have : x = incl k := Subtype.ext hxk
    exact this ▸ hx
  let : Algebra K E := incl.toRingHom.toAlgebra
  have : IsScalarTower K E L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra K K' := (incl.toRingHom.codRestrict K'.toSubring hK').toAlgebra
  have : IsScalarTower K K' E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hsepK : Algebra.IsSeparable K E :=
    ⟨fun y ↦ IsSeparable.of_algHom K (IsScalarTower.toAlgHom K E L) (hsep y y.2)⟩
  exact Algebra.isSeparable_tower_top_of_isSeparable K K' E

/-- The elements `aᵢ` lie in the field of elements of `L` separable algebraic over `l(a)`. -/
theorem mem_separableClosure_adjoin (a : ι → L) (i : ι) :
    a i ∈ (separableClosure (adjoin l (Set.range a)) L).restrictScalars l :=
  (mem_separableClosure_iff (F := adjoin l (Set.range a))).mpr
    (isSeparable_algebraMap (⟨a i, subset_adjoin _ _ ⟨i, rfl⟩⟩ : adjoin l (Set.range a)))

/-- The field `E` of elements of `L` separable algebraic over `l(a)` (the model `L_A` of the
blueprint, Section 4) is separable algebraic over `l(a) ⊆ E`. -/
theorem isSeparable_adjoin_restrictFamily_separableClosure (a : ι → L) :
    Algebra.IsSeparable
      (adjoin l (Set.range (restrictFamily _ a (mem_separableClosure_adjoin (l := l) a))))
      ((separableClosure (adjoin l (Set.range a)) L).restrictScalars l) :=
  isSeparable_adjoin_restrictFamily _ _ fun _ hy ↦ mem_separableClosure_iff.mp hy

/-- If `l` is relatively algebraically closed in `L`, it is relatively algebraically closed in
every intermediate field. -/
theorem relAlgClosed_intermediateField (E : IntermediateField l L)
    (hl : ∀ x : L, IsAlgebraic l x → x ∈ (algebraMap l L).range) :
    ∀ x : E, IsAlgebraic l x → x ∈ (algebraMap l E).range := by
  intro x hx
  obtain ⟨c, hc⟩ := hl x (hx.algHom E.val)
  exact ⟨c, Subtype.ext hc⟩

end MilnorAlgDep
