module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Supported
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# The chain rule for Kähler differentials

This file formalizes the second half of blueprint Lemma 2.3 (`lem:standard`), part (S2):

* the chain rule `d (g(x)) = ∑ᵢ (∂g/∂Xᵢ)(x) dxᵢ` for a polynomial `g` over `l`, so that
  `∑ᵢ g_{Xᵢ}(x) dxᵢ = 0` for every polynomial relation `g(x) = 0`
  (`MilnorAlgDep.derivation_aeval_eq_sum`, `MilnorAlgDep.kaehler_D_aeval`, ...);
* if `y` is separable algebraic over `l(x₁, …, xᵣ)` then `dy ∈ ∑ᵢ E dxᵢ`
  (`MilnorAlgDep.kaehler_D_mem_span_range_of_isSeparable`);
* `d (y ^ p) = 0` in characteristic `p` (`MilnorAlgDep.kaehler_D_pow_char`).

The chain rule is stated for an arbitrary derivation `d : Derivation R A M`; for a family indexed
by an infinite type, the sum runs over the variables of `g` (`derivation_aeval_eq_sum_vars`).

We also record that `{z | d z ∈ N}` is an intermediate field for a derivation `d` of a field and
a subspace `N` of the target (`MilnorAlgDep.derivationPreimageField`); in particular the kernel
of a derivation is an intermediate field.
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential MvPolynomial IntermediateField

section ChainRule

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module A M]
  [Module R M] {σ : Type*}

/-- **Chain rule** (blueprint Lemma 2.3 (S2)): for a derivation `d` and a polynomial `g` in
finitely many variables, `d (g(x)) = ∑ᵢ (∂g/∂Xᵢ)(x) • d xᵢ`. -/
theorem derivation_aeval_eq_sum [Fintype σ] (d : Derivation R A M) (x : σ → A)
    (g : MvPolynomial σ R) :
    d (aeval x g) = ∑ i, aeval x (pderiv i g) • d (x i) := by
  classical
  induction g using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq, add_smul, Finset.sum_add_distrib]
  | mul_X p n hp =>
    have h : ∀ i, aeval x (pderiv i (p * X n)) =
        aeval x (pderiv i p) * x n + if n = i then aeval x p else 0 := by
      intro i
      simp only [Derivation.leibniz, pderiv_X, smul_eq_mul, map_add, map_mul, aeval_X,
        Pi.single_apply]
      split_ifs <;> simp <;> ring
    calc d (aeval x (p * X n)) = aeval x p • d (x n) + x n • d (aeval x p) := by
          simp [Derivation.leibniz]
      _ = ∑ i, (aeval x (pderiv i p) * x n + if n = i then aeval x p else 0) • d (x i) := by
          simp only [hp, add_smul, Finset.sum_add_distrib, ite_smul, zero_smul,
            Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.smul_sum, smul_smul]
          rw [add_comm]
          congr 1
          exact Finset.sum_congr rfl fun i _ ↦ by rw [mul_comm]
      _ = ∑ i, aeval x (pderiv i (p * X n)) • d (x i) :=
          Finset.sum_congr rfl fun i _ ↦ by rw [h]

/-- **Chain rule**, version for an arbitrary index type: the sum may run over any finite set
containing the variables of `g`. -/
theorem derivation_aeval_eq_sum_of_vars_subset (d : Derivation R A M) (x : σ → A)
    (g : MvPolynomial σ R) (s : Finset σ) (hs : g.vars ⊆ s) :
    d (aeval x g) = ∑ i ∈ s, aeval x (pderiv i g) • d (x i) := by
  have hg : g ∈ supported R (s : Set σ) := by
    rw [mem_supported]; exact_mod_cast hs
  rw [supported_eq_range_rename] at hg
  obtain ⟨g', rfl⟩ := hg
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [aeval_rename, derivation_aeval_eq_sum, ← Finset.sum_coe_sort s]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have := pderiv_rename (R := R) (Subtype.val_injective (p := fun x ↦ x ∈ (s : Set σ))) i g'
  erw [this, aeval_rename]
  rfl

/-- **Chain rule**, version for an arbitrary index type, summing over the variables of `g`. -/
theorem derivation_aeval_eq_sum_vars (d : Derivation R A M) (x : σ → A)
    (g : MvPolynomial σ R) :
    d (aeval x g) = ∑ i ∈ g.vars, aeval x (pderiv i g) • d (x i) :=
  derivation_aeval_eq_sum_of_vars_subset d x g _ subset_rfl

/-- Blueprint Lemma 2.3 (S2): a polynomial relation `g(x) = 0` gives the linear relation
`∑ᵢ g_{Xᵢ}(x) d xᵢ = 0`. -/
theorem sum_pderiv_smul_derivation_eq_zero (d : Derivation R A M) (x : σ → A)
    {g : MvPolynomial σ R} (hg : aeval x g = 0) :
    ∑ i ∈ g.vars, aeval x (pderiv i g) • d (x i) = 0 := by
  rw [← derivation_aeval_eq_sum_vars, hg, map_zero]

end ChainRule

section Frobenius

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [AddCommGroup M] [Module A M]
  [Module R M]

/-- In characteristic `p`, every derivation kills `p`-th powers. -/
theorem derivation_pow_char (p : ℕ) [CharP A p] (d : Derivation R A M) (y : A) :
    d (y ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul A, CharP.cast_eq_zero, zero_smul]

/-- In characteristic `p`, every derivation kills `p ^ j`-th powers for `j ≠ 0`. -/
theorem derivation_pow_char_pow (p : ℕ) [CharP A p] (d : Derivation R A M) (y : A) {j : ℕ}
    (hj : j ≠ 0) : d (y ^ p ^ j) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  rw [pow_succ, pow_mul, derivation_pow_char]

end Frobenius

variable {l E : Type*} [Field l] [Field E] [Algebra l E]

/-- **Frobenius** (blueprint Lemma 2.3 (S2)): if `E` has characteristic `p` then
`d (y ^ p) = 0` in `Ω[E⁄l]`. -/
theorem kaehler_D_pow_char (p : ℕ) [CharP E p] (y : E) : D l E (y ^ p) = 0 :=
  derivation_pow_char p _ y

/-- **Frobenius**, iterated: `d (y ^ p ^ j) = 0` in `Ω[E⁄l]` for `j ≠ 0`. -/
theorem kaehler_D_pow_char_pow (p : ℕ) [CharP E p] (y : E) {j : ℕ} (hj : j ≠ 0) :
    D l E (y ^ p ^ j) = 0 :=
  derivation_pow_char_pow p _ y hj

/-- **Chain rule** (blueprint Lemma 2.3 (S2)) in `Ω[E⁄l]`, finitely many variables. -/
theorem kaehler_D_aeval {σ : Type*} [Fintype σ] (g : MvPolynomial σ l) (x : σ → E) :
    D l E (aeval x g) = ∑ i, aeval x (pderiv i g) • D l E (x i) :=
  derivation_aeval_eq_sum _ x g

/-- **Chain rule** (blueprint Lemma 2.3 (S2)) in `Ω[E⁄l]`, summing over the variables of `g`. -/
theorem kaehler_D_aeval_vars {σ : Type*} (g : MvPolynomial σ l) (x : σ → E) :
    D l E (aeval x g) = ∑ i ∈ g.vars, aeval x (pderiv i g) • D l E (x i) :=
  derivation_aeval_eq_sum_vars _ x g

/-- The image of `B ⊗ Ω[A⁄R] → Ω[B⁄R]` is spanned by the differentials of elements of `A`. -/
theorem range_mapBaseChange_le (R A B : Type*) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] :
    LinearMap.range (mapBaseChange R A B) ≤
      Submodule.span B (Set.range fun x : A ↦ D R B (algebraMap A B x)) := by
  rintro _ ⟨x, rfl⟩
  induction x with
  | add x y hx hy => rw [map_add]; exact add_mem hx hy
  | tmul b ω =>
    rw [mapBaseChange_tmul]
    refine Submodule.smul_mem _ _ ?_
    have : ω ∈ Submodule.span A (Set.range (D R A)) := by
      rw [span_range_derivation]; trivial
    induction this using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, rfl⟩ := hx
      rw [map_D]
      exact Submodule.subset_span ⟨x, rfl⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx =>
      rw [map_smul, algebra_compatible_smul B]
      exact Submodule.smul_mem _ _ hx

/-- If `y` is separable over an intermediate field `K`, then `d y` lies in the `E`-span of
`d K` in `Ω[E⁄l]`. (Because `d y = 0` in `Ω[E⁄K]`, and `E ⊗ Ω[K⁄l] → Ω[E⁄l] → Ω[E⁄K] → 0` is
exact.) -/
theorem kaehler_D_mem_span_of_isSeparable (K : IntermediateField l E) {y : E}
    (hy : IsSeparable K y) :
    D l E y ∈ Submodule.span E ((D l E) '' (K : Set E)) := by
  have h0 : D K E y = 0 := by
    have h := congrArg (D K E) (minpoly.aeval K y)
    rw [Derivation.map_aeval, map_zero] at h
    exact (smul_eq_zero.mp h).resolve_left (hy.aeval_derivative_ne_zero (minpoly.aeval K y))
  have hker : D l E y ∈ LinearMap.ker (map l K E E) := by
    rw [LinearMap.mem_ker, map_D]; exact h0
  rw [← range_mapBaseChange] at hker
  refine Submodule.span_mono ?_ (range_mapBaseChange_le l K E hker)
  rintro _ ⟨x, rfl⟩
  exact ⟨x, x.2, rfl⟩

/-- For a derivation `d` on a field `E` and an `E`-subspace `N` of the target, the elements `z`
with `d z ∈ N` form an intermediate field. -/
def derivationPreimageField {M : Type*} [AddCommGroup M] [Module E M] [Module l M]
    [IsScalarTower l E M] (d : Derivation l E M) (N : Submodule E M) : IntermediateField l E where
  carrier := {z | d z ∈ N}
  mul_mem' {x y} hx hy := by
    change d (x * y) ∈ N
    rw [Derivation.leibniz]
    exact add_mem (N.smul_mem _ hy) (N.smul_mem _ hx)
  add_mem' {x y} hx hy := by
    change d (x + y) ∈ N
    rw [map_add]
    exact add_mem hx hy
  algebraMap_mem' c := by
    change d (algebraMap l E c) ∈ N
    rw [Derivation.map_algebraMap]
    exact N.zero_mem
  inv_mem' x hx := by
    change d x⁻¹ ∈ N
    rw [Derivation.leibniz_inv]
    exact N.smul_mem _ hx

@[simp] theorem mem_derivationPreimageField {M : Type*} [AddCommGroup M] [Module E M]
    [Module l M] [IsScalarTower l E M] (d : Derivation l E M) (N : Submodule E M) (z : E) :
    z ∈ derivationPreimageField d N ↔ d z ∈ N := Iff.rfl

/-- If `y ∈ l(S)` then `d y` lies in the `E`-span of `d S`. -/
theorem kaehler_D_mem_span_of_mem_adjoin (S : Set E) {y : E} (hy : y ∈ adjoin l S) :
    D l E y ∈ Submodule.span E ((D l E) '' S) := by
  have : adjoin l S ≤ derivationPreimageField (D l E) (Submodule.span E ((D l E) '' S)) :=
    adjoin_le_iff.mpr fun z hz ↦ Submodule.subset_span ⟨z, hz, rfl⟩
  exact this hy

/-- **Blueprint Lemma 2.3 (S2)**, second half: if `y` is separable algebraic over `l(S)`, then
`d y` lies in the `E`-span of `d S`. -/
theorem kaehler_D_mem_span_of_isSeparable_adjoin (S : Set E) {y : E}
    (hy : IsSeparable (adjoin l S) y) :
    D l E y ∈ Submodule.span E ((D l E) '' S) := by
  refine Submodule.span_le.mpr ?_ (kaehler_D_mem_span_of_isSeparable _ hy)
  rintro _ ⟨z, hz, rfl⟩
  exact kaehler_D_mem_span_of_mem_adjoin S hz

/-- **Blueprint Lemma 2.3 (S2)**, second half, for a family: if `y` is separable algebraic over
`l(x)`, then `d y ∈ span_E {d xᵢ}`. -/
theorem kaehler_D_mem_span_range_of_isSeparable {σ : Type*} (x : σ → E) {y : E}
    (hy : IsSeparable (adjoin l (Set.range x)) y) :
    D l E y ∈ Submodule.span E (Set.range fun i ↦ D l E (x i)) := by
  have := kaehler_D_mem_span_of_isSeparable_adjoin _ hy
  rwa [← Set.range_comp] at this

end MilnorAlgDep
