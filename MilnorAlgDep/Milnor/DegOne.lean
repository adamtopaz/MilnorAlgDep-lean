module

public import MilnorAlgDep.Milnor.BCDAux
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
* `MilnorKQ.degOne_bijective`: an isomorphism of graded algebras whose inverse is graded has a
  bijective degree one part.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf MilnorKQ

/-- Blueprint, remark after Lemma 7.2: if `v, w ∈ V_{L|l}` satisfy `{v, w} = 0` in `𝒦_2(L|l)`,
then `v, w` are algebraically dependent over `l` (or one of them is `0`, which is included, as
algebraically independent elements are non-zero). -/
theorem not_vAlgIndep_of_ι_mul_ι_eq_zero {l L : Type*} [Field l] [Field L] [Algebra l L]
    [IsRelAlgClosed l L] {v w : V l L}
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

/-- Blueprint 7.2, proof of Theorem B, (A2): for a graded `φ : 𝒦_*(K|k) → 𝒦_*(L|l)` and units
`x, y` with `x + y = 1`, the elements `φ₁ [x]` and `φ₁ [y]` of `V_{L|l}` are algebraically
dependent (or one of them is `0`), because `{φ₁ [x], φ₁ [y]} = φ {x, y} = 0`. -/
theorem not_vAlgIndep_of_isGraded {H : Subgroup Kˣ} {l : Type*} [Field l] [Algebra l L]
    [IsRelAlgClosed l L] {φ : MilnorKQ H →ₐ[ℚ] MilnorKQ (constUnits l L)} (hφ : IsGraded φ)
    {x y : Kˣ} (hxy : (x : K) + y = 1) :
    ¬ VAlgIndep l ![degOne φ (cls H (.ofMul x)), degOne φ (cls H (.ofMul y))] := by
  apply not_vAlgIndep_of_ι_mul_ι_eq_zero
  rw [← hφ.map_ι, ← hφ.map_ι, ← map_mul, ι_mul_ι_eq_zero _ hxy, map_zero]

/-- An isomorphism of graded algebras whose inverse is graded has a bijective degree one part. -/
theorem degOne_bijective {H : Subgroup Lˣ} {H' : Subgroup Kˣ}
    (φ : MilnorKQ H ≃ₐ[ℚ] MilnorKQ H') (hφ : IsGraded φ.toAlgHom)
    (hφsymm : IsGraded φ.symm.toAlgHom) : Function.Bijective (degOne φ.toAlgHom) := by
  have h1 : degOne φ.symm.toAlgHom ∘ₗ degOne φ.toAlgHom = LinearMap.id := by
    rw [← degOne_comp hφ]
    convert degOne_id (H := H)
    ext v
    simp
  have h2 : degOne φ.toAlgHom ∘ₗ degOne φ.symm.toAlgHom = LinearMap.id := by
    rw [← degOne_comp hφsymm]
    convert degOne_id (H := H')
    ext v
    simp
  refine ⟨Function.LeftInverse.injective (g := degOne φ.symm.toAlgHom) fun v ↦ ?_,
    Function.RightInverse.surjective (g := degOne φ.symm.toAlgHom) fun v ↦ ?_⟩
  · exact LinearMap.congr_fun h1 v
  · exact LinearMap.congr_fun h2 v

end MilnorKQ

end MilnorAlgDep
