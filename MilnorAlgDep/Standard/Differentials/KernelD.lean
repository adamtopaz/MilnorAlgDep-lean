module

public import MilnorAlgDep.Standard.Differentials.Basis
public import MilnorAlgDep.Standard.Differentials.ChainRule
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.FieldTheory.PurelyInseparable.PerfectClosure

/-!
# The kernel of `d : E → Ω[E⁄l]` in characteristic `p`

This file formalizes the first part of blueprint Lemma 2.1 (`lem:standard`), (S3): if `E` is
separable algebraic over `l(a)` for an algebraically independent family `a`, and `l` is perfect
of characteristic `p > 0`, then the kernel of `d : E → Ω[E⁄l]` is `E ^ p`
(`MilnorAlgDep.kaehler_D_eq_zero_iff_exists_pow_eq`).

## Proof

Let `F = E ^ p` (an intermediate field since `l` is perfect, `MilnorAlgDep.powField`) and let
`∂ᵢ` be the coordinate derivations of the basis `(d aᵢ)ᵢ` (`MilnorAlgDep.coordDerivation`), so
`∂ᵢ aₖ = δᵢₖ` and `d y = 0 ↔ ∀ i, ∂ᵢ y = 0`. All `∂ᵢ` vanish on `F`.

* `E = F(a)`: `y ∈ E` is separable over `l(a) ⊆ F(a)` and `y ^ p ∈ F`, so `y ∈ F(a)`; hence
  `y ∈ F(a_S)` for a finite `S` (`MilnorAlgDep.exists_finset_mem_adjoin_powField`).
* One step (`MilnorAlgDep.mem_of_mem_adjoin_simple_of_derivation_eq_zero`): if a derivation `∂`
  kills `M`, `x ^ p ∈ M` and `∂ x ≠ 0`, then every `y ∈ M(x)` with `∂ y = 0` lies in `M`. Indeed
  `y = g(x)` with `deg g < deg (minpoly x)`, `0 = ∂ y = g'(x) ∂ x` forces `g' = 0`, so `g` is a
  polynomial in `X ^ p` and `y ∈ M(x ^ p) = M`.
* Induction on `S` (`MilnorAlgDep.mem_powField_of_mem_adjoin_finset`), applying the step to
  `M = F(a_{S'})`, `x = aᵢ`, `∂ = ∂ᵢ`.
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential IntermediateField Polynomial

variable {l E : Type*} [Field l] [Field E] [Algebra l E]

/-- A derivation killing an intermediate field `K` acts on `g(x)`, `g ∈ K[X]`, by
`d (g(x)) = g'(x) • d x`. -/
theorem derivation_aeval_of_forall_mem_eq_zero {V : Type*} [AddCommGroup V] [Module E V]
    [Module l V] (K : IntermediateField l E) (d : Derivation l E V)
    (hK : ∀ m ∈ K, d m = 0) (x : E) (g : K[X]) :
    d (aeval x g) = aeval x (derivative g) • d x := by
  induction g using Polynomial.induction_on' with
  | add f g hf hg => simp [hf, hg, add_smul]
  | monomial n c =>
    have hc : d (c : E) = 0 := hK _ c.2
    simp only [aeval_monomial, Derivation.leibniz, Derivation.leibniz_pow, derivative_monomial,
      map_mul, map_natCast]
    rw [show (algebraMap K E c) = (c : E) from rfl, hc, smul_zero, add_zero,
      ← Nat.cast_smul_eq_nsmul E]
    simp only [smul_smul]
    congr 1
    ring

/-- The kernel of a derivation of a field, as an intermediate field. -/
def derivationKerField {V : Type*} [AddCommGroup V] [Module E V] [Module l V]
    [IsScalarTower l E V] (d : Derivation l E V) : IntermediateField l E where
  carrier := {z | d z = 0}
  mul_mem' {x y} hx hy := by
    change d (x * y) = 0
    change d x = 0 at hx
    change d y = 0 at hy
    rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]
  add_mem' {x y} hx hy := by
    change d (x + y) = 0
    change d x = 0 at hx
    change d y = 0 at hy
    rw [map_add, hx, hy, add_zero]
  algebraMap_mem' c := Derivation.map_algebraMap d c
  inv_mem' x hx := by
    change d x⁻¹ = 0
    change d x = 0 at hx
    rw [Derivation.leibniz_inv, hx, smul_zero]

@[simp] theorem mem_derivationKerField {V : Type*} [AddCommGroup V] [Module E V] [Module l V]
    [IsScalarTower l E V] (d : Derivation l E V) (z : E) :
    z ∈ derivationKerField d ↔ d z = 0 := Iff.rfl

variable (p : ℕ) [Fact p.Prime] [CharP E p]

/-- One step of the `p`-basis argument: if a derivation `d` kills the intermediate field `M`,
`x ^ p ∈ M` and `d x ≠ 0`, then the elements of `M(x)` killed by `d` are those of `M`. -/
theorem mem_of_mem_adjoin_simple_of_derivation_eq_zero (M : IntermediateField l E)
    (d : Derivation l E E) (hM : ∀ m ∈ M, d m = 0) {x : E} (hxp : x ^ p ∈ M) (hdx : d x ≠ 0)
    {y : E} (hy : y ∈ adjoin M {x}) (hdy : d y = 0) : y ∈ M := by
  have hp := (Fact.out : p.Prime)
  have : CharP M p := (Algebra.charP_iff M E p).mpr inferInstance
  have hint : IsIntegral M x := by
    refine ⟨X ^ p - C ⟨x ^ p, hxp⟩, monic_X_pow_sub_C _ hp.ne_zero, ?_⟩
    simp
  have hy' : y ∈ (adjoin M {x}).toSubalgebra := hy
  rw [adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic,
    Algebra.adjoin_singleton_eq_range_aeval] at hy'
  obtain ⟨g, rfl⟩ := hy'
  set g' := g %ₘ minpoly M x with hg'
  have hgg' : aeval x g' = aeval x g :=
    aeval_modByMonic_eq_self_of_root (minpoly.aeval M x)
  have hdeg : g'.degree < (minpoly M x).degree := degree_modByMonic_lt _ (minpoly.monic hint)
  change d (aeval x g) = 0 at hdy
  rw [← hgg', derivation_aeval_of_forall_mem_eq_zero M d hM, smul_eq_mul] at hdy
  have h1 : aeval x (derivative g') = 0 := (mul_eq_zero.mp hdy).resolve_right hdx
  have h2 : derivative g' = 0 := by
    by_contra h
    have := minpoly.degree_le_of_ne_zero M x h h1
    exact absurd ((this.trans (degree_derivative_le)).trans_lt hdeg) (lt_irrefl _)
  have h3 := expand_contract p h2 hp.ne_zero
  change aeval x g ∈ M
  rw [← hgg', ← h3, expand_aeval]
  have : x ^ p = algebraMap M E ⟨x ^ p, hxp⟩ := rfl
  rw [this, aeval_algebraMap_apply]
  exact SetLike.coe_mem _

omit [Fact p.Prime] [CharP E p] in
/-- In a perfect field of characteristic `p`, every element is a `p ^ j`-th power. -/
theorem exists_pow_pow_eq_of_perfectField [PerfectField l] [Fact p.Prime] [CharP l p] (c : l)
    (j : ℕ) : ∃ c' : l, c' ^ p ^ j = c := by
  obtain ⟨c', hc'⟩ := (iterateFrobeniusEquiv l p j).surjective c
  exact ⟨c', by rw [← hc', coe_iterateFrobeniusEquiv, iterateFrobenius_def]⟩

/-- The intermediate field `E ^ (p ^ j)` of `p ^ j`-th powers (for `l` perfect). -/
def powField (l E : Type*) [Field l] [Field E] [Algebra l E] [PerfectField l] (p : ℕ)
    [Fact p.Prime] [CharP E p] (j : ℕ) : IntermediateField l E where
  carrier := {x | ∃ z, z ^ p ^ j = x}
  mul_mem' := by
    rintro _ _ ⟨z, rfl⟩ ⟨w, rfl⟩
    exact ⟨z * w, mul_pow ..⟩
  add_mem' := by
    rintro _ _ ⟨z, rfl⟩ ⟨w, rfl⟩
    exact ⟨z + w, add_pow_char_pow ..⟩
  algebraMap_mem' c := by
    have : CharP l p := (Algebra.charP_iff l E p).mpr inferInstance
    obtain ⟨c', rfl⟩ := exists_pow_pow_eq_of_perfectField p c j
    exact ⟨algebraMap l E c', (map_pow _ _ _).symm⟩
  inv_mem' := by
    rintro _ ⟨z, rfl⟩
    exact ⟨z⁻¹, inv_pow ..⟩

@[simp] theorem mem_powField [PerfectField l] (j : ℕ) {x : E} :
    x ∈ powField l E p j ↔ ∃ z, z ^ p ^ j = x := Iff.rfl

variable {ι : Type*} {a : ι → E}

/-- The coordinate derivations `∂/∂aᵢ` attached to the basis `(d aᵢ)ᵢ`. -/
noncomputable def coordDerivation (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) (i : ι) : Derivation l E E :=
  ((kaehlerBasis hb hsep).coord i).compDer (D l E)

/-- `∂ᵢ y` is the `i`-th coordinate of `d y` in the basis `(d aₖ)ₖ`. -/
theorem coordDerivation_apply (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) (i : ι) (y : E) :
    coordDerivation hb hsep i y = (kaehlerBasis hb hsep).repr (D l E y) i := rfl

/-- `∂ᵢ aₖ = δᵢₖ`. -/
theorem coordDerivation_gen [DecidableEq ι] (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) (i k : ι) :
    coordDerivation hb hsep i (a k) = if k = i then 1 else 0 := by
  rw [coordDerivation_apply, ← kaehlerBasis_apply hb hsep, Module.Basis.repr_self,
    Finsupp.single_apply]

/-- `d y = 0` if and only if all coordinate derivations vanish on `y`. -/
theorem kaehler_D_eq_zero_iff_forall_coordDerivation (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) (y : E) :
    D l E y = 0 ↔ ∀ i, coordDerivation hb hsep i y = 0 := by
  simp only [coordDerivation_apply]
  rw [← (kaehlerBasis hb hsep).repr.map_eq_zero_iff, Finsupp.ext_iff]
  simp

variable [PerfectField l]

/-- The induction in the proof of (S3): an element of `E ^ p (a_S)` killed by all `∂ᵢ`, `i ∈ S`,
lies in `E ^ p`. -/
theorem mem_powField_of_mem_adjoin_finset (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) (S : Finset ι) :
    ∀ y ∈ adjoin l ((powField l E p 1 : Set E) ∪ a '' S),
      (∀ i ∈ S, coordDerivation hb hsep i y = 0) → y ∈ powField l E p 1 := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro y hy _
    simpa [adjoin_self] using hy
  | insert i S hi ih =>
    intro y hy hdy
    set M := adjoin l ((powField l E p 1 : Set E) ∪ a '' S)
    have hkill : ∀ m ∈ M, coordDerivation hb hsep i m = 0 := by
      intro m hm
      have : M ≤ derivationKerField (coordDerivation hb hsep i) := by
        rw [adjoin_le_iff]
        rintro _ (⟨z, rfl⟩ | ⟨k, hk, rfl⟩)
        · change coordDerivation hb hsep i (z ^ p ^ 1) = 0
          rw [pow_one]
          exact derivation_pow_char p _ z
        · have : k ≠ i := fun h ↦ hi (h ▸ hk)
          simp [coordDerivation_gen, this]
      simpa using this hm
    have hyM : y ∈ adjoin M {a i} := by
      have : adjoin l ((powField l E p 1 : Set E) ∪ a '' ↑(insert i S)) ≤
          (adjoin M {a i}).restrictScalars l := by
        rw [restrictScalars_adjoin, adjoin_le_iff]
        rintro z (hz | ⟨k, hk, rfl⟩)
        · exact subset_adjoin _ _ (Or.inl (subset_adjoin _ _ (Or.inl hz)))
        · rw [Finset.coe_insert, Set.mem_insert_iff] at hk
          rcases hk with rfl | hk
          · exact subset_adjoin _ _ (Or.inr rfl)
          · exact subset_adjoin _ _ (Or.inl (subset_adjoin _ _ (Or.inr ⟨k, hk, rfl⟩)))
      exact this hy
    have hxp : a i ^ p ∈ M := subset_adjoin _ _ (Or.inl ⟨a i, by rw [pow_one]⟩)
    have hdx : coordDerivation hb hsep i (a i) ≠ 0 := by simp [coordDerivation_gen]
    have := mem_of_mem_adjoin_simple_of_derivation_eq_zero p M _ hkill hxp hdx hyM
      (hdy i (Finset.mem_insert_self i S))
    exact ih y this fun k hk ↦ hdy k (Finset.mem_insert_of_mem hk)


/-- `E = E ^ p (a)`: every element of `E` lies in `l(E ^ p, a_S)` for a finite `S`. -/
theorem exists_finset_mem_adjoin_powField (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) (y : E) :
    ∃ S : Finset ι, y ∈ adjoin l ((powField l E p 1 : Set E) ∪ a '' S) := by
  classical
  set K := adjoin l (Set.range a)
  set N := adjoin K (powField l E p 1 : Set E)
  have hyN : y ∈ N := by
    have : CharP N p := (Algebra.charP_iff N E p).mpr inferInstance
    have : ExpChar N p := ExpChar.prime Fact.out
    have hsepy : IsSeparable N y := (hsep.isSeparable' y).tower_top N
    have h1 := adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable N E hsepy p
    have h2 : N⟮y ^ p⟯ = ⊥ := by
      rw [adjoin_simple_eq_bot_iff, mem_bot]
      exact ⟨⟨y ^ p, subset_adjoin _ _ ⟨y, by rw [pow_one]⟩⟩, rfl⟩
    have h3 : y ∈ N⟮y⟯ := mem_adjoin_simple_self N y
    rw [h1, h2, mem_bot] at h3
    obtain ⟨z, hz⟩ := h3
    rw [← hz]
    exact z.2
  have hyN' : y ∈ adjoin l ((powField l E p 1 : Set E) ∪ Set.range a) := by
    have : N.restrictScalars l ≤ adjoin l ((powField l E p 1 : Set E) ∪ Set.range a) := by
      rw [restrictScalars_adjoin, adjoin_le_iff]
      rintro z (hz | hz)
      · exact (adjoin.mono _ _ _ Set.subset_union_right) hz
      · exact subset_adjoin _ _ (Or.inl hz)
    exact this hyN
  obtain ⟨T, hT, hyT⟩ := exists_finset_of_mem_adjoin hyN'
  refine ⟨T.preimage a hb.injective.injOn, adjoin.mono _ _ _ ?_ hyT⟩
  intro z hz
  rcases hT hz with hz' | ⟨i, rfl⟩
  · exact Or.inl hz'
  · exact Or.inr ⟨i, by simpa using hz, rfl⟩

/-- **Blueprint Lemma 2.1 (S3)**, kernel of `d`: if `E` is separable algebraic over `l(a)` with
`a` algebraically independent and `l` perfect of characteristic `p`, then `d y = 0` in `Ω[E⁄l]`
only if `y` is a `p`-th power in `E`. -/
theorem exists_pow_eq_of_kaehler_D_eq_zero (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) {y : E} (hy : D l E y = 0) :
    ∃ z, z ^ p = y := by
  obtain ⟨S, hS⟩ := exists_finset_mem_adjoin_powField p hb hsep y
  rw [kaehler_D_eq_zero_iff_forall_coordDerivation hb hsep] at hy
  obtain ⟨z, hz⟩ := mem_powField_of_mem_adjoin_finset p hb hsep S y hS fun i _ ↦ hy i
  exact ⟨z, by rw [← hz, pow_one]⟩

/-- **Blueprint Lemma 2.1 (S3)**: the kernel of `d : E → Ω[E⁄l]` is `E ^ p`. -/
theorem kaehler_D_eq_zero_iff_exists_pow_eq (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) {y : E} :
    D l E y = 0 ↔ ∃ z, z ^ p = y := by
  refine ⟨exists_pow_eq_of_kaehler_D_eq_zero p hb hsep, ?_⟩
  rintro ⟨z, rfl⟩
  exact kaehler_D_pow_char p z


end MilnorAlgDep
