module

public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.MvPolynomial.Expand

/-!
# Polynomials with vanishing partial derivatives

This file formalizes the part of blueprint Lemma 2.3 (`lem:standard`), (S1), used later
(in the proof of Lemma 4.6, `lem:lax`): if all partial derivatives of `f ∈ R[Yᵢ : i ∈ σ]` vanish,
then

* `f` is constant if `R` is a domain of characteristic `0` (`MilnorAlgDep.eq_C_of_pderiv_eq_zero`);
* `f` is a polynomial in the `Yᵢ ^ p` if `R` is a domain of characteristic `p > 0`
  (`MilnorAlgDep.exists_expand_eq_of_pderiv_eq_zero`);
* `f` is a `p`-th power if moreover `R` is perfect
  (`MilnorAlgDep.exists_eq_pow_of_pderiv_eq_zero`).

We also show that a non-zero partial derivative has smaller total degree
(`MilnorAlgDep.totalDegree_pderiv_lt`).
-/

@[expose] public section

namespace MilnorAlgDep

open MvPolynomial

variable {R σ : Type*}

section CommSemiring

variable [CommSemiring R]

/-- If `∂f/∂Yᵢ = 0` then `cₘ · mᵢ = 0` for every coefficient `cₘ` of `f`. -/
theorem coeff_mul_cast_eq_zero_of_pderiv_eq_zero {f : MvPolynomial σ R} {i : σ}
    (h : pderiv i f = 0) (m : σ →₀ ℕ) : f.coeff m * (m i : R) = 0 := by
  classical
  rcases Nat.eq_zero_or_pos (m i) with hm | hm
  · simp [hm]
  have hm' : m - Finsupp.single i 1 + Finsupp.single i 1 = m := by
    ext j
    by_cases hj : j = i
    · subst hj; simp; omega
    · simp [Ne.symm hj]
  have := congrArg (fun q : MvPolynomial σ R ↦ q.coeff (m - Finsupp.single i 1)) h
  have e : (((m - Finsupp.single i 1 : σ →₀ ℕ) i : ℕ) : R) + 1 = (m i : R) := by
    norm_cast
    simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
    rw [Nat.sub_add_cancel hm]
  rwa [coeff_pderiv, hm', AddMonoidAlgebra.coeff_zero, e] at this

/-- A non-zero partial derivative has smaller total degree. -/
theorem totalDegree_pderiv_lt {f : MvPolynomial σ R} {i : σ} (h : pderiv i f ≠ 0) :
    (pderiv i f).totalDegree < f.totalDegree := by
  have key : ∀ m ∈ (pderiv i f).support, (m.sum fun _ e ↦ e) < f.totalDegree := by
    intro m hm
    have hm' : m + Finsupp.single i 1 ∈ f.support := by
      rw [mem_support_iff, coeff_pderiv] at hm
      rw [mem_support_iff]
      exact left_ne_zero_of_mul hm
    have := le_totalDegree hm'
    rw [Finsupp.sum_add_index' (fun _ ↦ rfl) (fun _ _ _ ↦ rfl), Finsupp.sum_single_index rfl]
      at this
    omega
  obtain ⟨m, hm⟩ := ne_zero_iff.mp h
  rw [← mem_support_iff] at hm
  rw [totalDegree, Finset.sup_lt_iff (lt_of_le_of_lt (Nat.zero_le _) (key m hm))]
  exact key

end CommSemiring

section Domain

variable [CommRing R] [IsDomain R]

/-- **Blueprint Lemma 2.3 (S1)**, characteristic `0`: if all partial derivatives of `f` vanish,
then `f` is constant. -/
theorem eq_C_of_pderiv_eq_zero [CharZero R] {f : MvPolynomial σ R}
    (h : ∀ i, pderiv i f = 0) : f = C (f.coeff 0) := by
  classical
  ext m
  rw [coeff_C]
  split_ifs with hm
  · rw [hm]
  obtain ⟨i, hi⟩ : ∃ i, m i ≠ 0 := by
    by_contra! H
    exact hm (Finsupp.ext fun j ↦ (H j).trans rfl).symm
  have := coeff_mul_cast_eq_zero_of_pderiv_eq_zero (h i) m
  exact (mul_eq_zero.mp this).resolve_right (Nat.cast_ne_zero.mpr hi)

/-- Blueprint Lemma 2.3 (S1), first sentence, characteristic `0`: if `∂f/∂Yᵢ = 0` then `Yᵢ` does
not occur in `f`. -/
theorem notMem_vars_of_pderiv_eq_zero [CharZero R] {f : MvPolynomial σ R} {i : σ}
    (h : pderiv i f = 0) : i ∉ f.vars := by
  classical
  intro hi
  obtain ⟨m, hm, hmi⟩ := (mem_vars_iff_mem_support i).mp hi
  have := coeff_mul_cast_eq_zero_of_pderiv_eq_zero h m
  rw [mem_support_iff] at hm
  exact Finsupp.mem_support_iff.mp hmi
    (Nat.cast_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hm))

/-- Blueprint Lemma 2.3 (S1), first sentence, characteristic `p`: if `∂f/∂Yᵢ = 0` then `Yᵢ`
occurs in `f` only with exponents divisible by `p`. -/
theorem dvd_of_mem_support_of_pderiv_eq_zero (p : ℕ) [CharP R p] {f : MvPolynomial σ R}
    {i : σ} (h : pderiv i f = 0) {m : σ →₀ ℕ} (hm : m ∈ f.support) : p ∣ m i := by
  have := coeff_mul_cast_eq_zero_of_pderiv_eq_zero h m
  rw [mem_support_iff] at hm
  exact (CharP.cast_eq_zero_iff R p _).mp ((mul_eq_zero.mp this).resolve_left hm)

/-- **Blueprint Lemma 2.3 (S1)**, characteristic `p`: a polynomial all of whose partial
derivatives vanish is a polynomial in the `p`-th powers of the variables. -/
theorem exists_expand_eq_of_pderiv_eq_zero (p : ℕ) [CharP R p] (hp : p ≠ 0)
    {f : MvPolynomial σ R} (h : ∀ i, pderiv i f = 0) : ∃ g, expand p g = f := by
  classical
  have hinj : Function.Injective fun m : σ →₀ ℕ ↦ p • m := smul_right_injective _ hp
  let g : MvPolynomial σ R :=
    AddMonoidAlgebra.ofCoeff (Finsupp.comapDomain (fun m : σ →₀ ℕ ↦ p • m) f.coeff hinj.injOn)
  have hg : ∀ m, g.coeff m = f.coeff (p • m) := fun m ↦ rfl
  refine ⟨g, ?_⟩
  ext m
  by_cases hdvd : ∀ i, p ∣ m i
  · let m' : σ →₀ ℕ := Finsupp.mapRange (· / p) (Nat.zero_div p) m
    have hm' : p • m' = m := by
      ext i
      simp [m', Nat.mul_div_cancel' (hdvd i)]
    rw [← hm', coeff_expand_smul p hp, hg]
  · push Not at hdvd
    obtain ⟨i, hi⟩ := hdvd
    rw [coeff_expand_of_not_dvd _ hi]
    by_contra hne
    exact hi (dvd_of_mem_support_of_pderiv_eq_zero p (h i) (mem_support_iff.mpr (Ne.symm hne)))

/-- **Blueprint Lemma 2.3 (S1)**: over a perfect domain of exponential characteristic `p`, a
polynomial all of whose partial derivatives vanish is a `p`-th power. (For `p = 1` this is
empty; use `eq_C_of_pderiv_eq_zero` in characteristic `0`.) -/
theorem exists_eq_pow_of_pderiv_eq_zero (p : ℕ) [ExpChar R p] [PerfectRing R p]
    {f : MvPolynomial σ R} (h : ∀ i, pderiv i f = 0) : ∃ g, f = g ^ p := by
  rcases ‹ExpChar R p› with _ | ⟨hp⟩
  · exact ⟨f, (pow_one f).symm⟩
  obtain ⟨g₀, rfl⟩ := exists_expand_eq_of_pderiv_eq_zero p hp.ne_zero h
  refine ⟨map ((frobeniusEquiv R p).symm : R →+* R) g₀, ?_⟩
  rw [← map_frobenius_expand p, map_expand, map_map]
  rw [frobenius_comp_frobeniusEquiv_symm, map_id]

/-- Over a domain, the total degree is multiplicative on powers of a non-zero polynomial. -/
theorem totalDegree_pow_of_isDomain {g : MvPolynomial σ R} (hg : g ≠ 0) (n : ℕ) :
    (g ^ n).totalDegree = n * g.totalDegree := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, totalDegree_mul_of_isDomain (pow_ne_zero n hg) hg, ih]
    ring

end Domain

end MilnorAlgDep
