import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The eigenvalue lemma

This file formalizes Lemma `lem:R` (Blueprint Lemma 2.2, "Eigenvalue lemma") of
`blueprint/milnor-k-fields.tex`, Section 2.4 ("Standard facts").

Let `l ⊆ E` be fields, `a ∈ E` transcendental over `l` and `δ` an `l`-linear derivation of `E`
with `δ a = a`. If `b ∈ Eˣ` is separable algebraic over `l(a)` and `δ b = κ b` with `κ ∈ l`,
then `κ` lies in the prime field of `l`.

## Proof

We work with the minimal polynomial `f = ∑ f_j Y^j` of `b` over `l(a)` directly, which avoids
Gauss's lemma. The derivation `δ` preserves `l(a)` (on `l(a)` it is `a · d/da`). Applying `δ` to
`f(b) = 0` gives `∑ (δ f_j + j κ f_j) b^j = 0`; subtracting `n κ f(b)` (with `n = deg f`) gives a
polynomial over `l(a)` of degree `< n` vanishing at `b`, so `δ f_j = (n - j) κ f_j` for all `j`.

A non-zero `g ∈ l(a)` with `δ g = ε g`, `ε ∈ l`, forces `ε ∈ ℤ`: writing `g = P(a)/Q(a)`, this
is the polynomial identity `X (P' Q - P Q') = ε P Q`, and comparing the coefficients of index
`ord_X P + ord_X Q` gives `ε = ord_X P - ord_X Q` (`exists_intCast_eq_of_euler`).

Applying this to `f_0 ≠ 0` (as `b ≠ 0`) and to some `f_j ≠ 0` with `j ≠ 0` in `l` (which exists
since `f' ≠ 0` by separability) gives `n κ ∈ ℤ` and `(n - j) κ ∈ ℤ`, hence `j κ ∈ ℤ`.

## Main results

* `MilnorAlgDep.exists_natCast_mul_eigenvalue_eq_intCast`: `j κ = m` for some `m : ℤ` and some
  `j : ℕ` that is non-zero in `l`.
* `MilnorAlgDep.eigenvalue_mem_primeField`: Blueprint Lemma 2.2, `κ ∈ (⊥ : Subfield l)`.
* `MilnorAlgDep.exists_ratCast_eq_eigenvalue`: in characteristic `0`, `κ` is a rational number.
* `MilnorAlgDep.exists_zmod_eq_eigenvalue`, `MilnorAlgDep.exists_intCast_eq_eigenvalue`:
  in characteristic `p`, `κ` is the image of an element of `ZMod p`, equivalently of an integer.
-/

namespace MilnorAlgDep

open Polynomial IntermediateField

section Euler

variable {l : Type*} [Field l]

/-- The coefficients of `X * P'` are those of `P` multiplied by their index. -/
theorem coeff_X_mul_derivative (P : l[X]) (n : ℕ) :
    (X * derivative P).coeff n = P.coeff n * n := by
  cases n with
  | zero => simp
  | succ n => simp [coeff_X_mul, coeff_derivative]

/-- The coefficient of index `m + k` of `p * q`, when the coefficients of `p` below `m` and those
of `q` below `k` vanish. -/
theorem coeff_mul_add_of_forall_lt {p q : l[X]} {m k : ℕ}
    (hp : ∀ i < m, p.coeff i = 0) (hq : ∀ i < k, q.coeff i = 0) :
    (p * q).coeff (m + k) = p.coeff m * q.coeff k := by
  rw [coeff_mul, Finset.sum_eq_single (m, k)]
  · rintro ⟨i, j⟩ h hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at h
    rcases lt_or_ge i m with hi | hi
    · simp [hp i hi]
    · have hj : j < k := by
        by_contra hj
        exact hne (Prod.ext (by simp only; omega) (by simp only; omega))
      simp [hq j hj]
  · intro h
    simp at h

/-- If non-zero polynomials `P, Q` satisfy `X (P' Q - P Q') = ε P Q`, i.e. the rational function
`P / Q` is an eigenvector with eigenvalue `ε` of the Euler operator `X d/dX`, then `ε` is an
integer (namely `ord_X P - ord_X Q`). -/
theorem exists_intCast_eq_of_euler {P Q : l[X]} (hP : P ≠ 0) (hQ : Q ≠ 0) {ε : l}
    (h : X * (derivative P * Q - P * derivative Q) = C ε * (P * Q)) :
    ∃ m : ℤ, ε = m := by
  set m := P.natTrailingDegree
  set k := Q.natTrailingDegree
  refine ⟨(m : ℤ) - k, ?_⟩
  have hPm : ∀ i < m, P.coeff i = 0 := fun i hi ↦ coeff_eq_zero_of_lt_natTrailingDegree hi
  have hQk : ∀ i < k, Q.coeff i = 0 := fun i hi ↦ coeff_eq_zero_of_lt_natTrailingDegree hi
  have hXP : ∀ i < m, (X * derivative P).coeff i = 0 := fun i hi ↦ by
    rw [coeff_X_mul_derivative, hPm i hi, zero_mul]
  have hXQ : ∀ i < k, (X * derivative Q).coeff i = 0 := fun i hi ↦ by
    rw [coeff_X_mul_derivative, hQk i hi, zero_mul]
  have h' := congrArg (fun p : l[X] ↦ p.coeff (m + k)) h
  rw [show X * (derivative P * Q - P * derivative Q) =
      X * derivative P * Q - P * (X * derivative Q) by ring, coeff_sub,
    coeff_mul_add_of_forall_lt hXP hQk, coeff_mul_add_of_forall_lt hPm hXQ, coeff_C_mul,
    coeff_mul_add_of_forall_lt hPm hQk, coeff_X_mul_derivative, coeff_X_mul_derivative] at h'
  have hP0 : P.coeff m ≠ 0 := mt trailingCoeff_eq_zero.mp hP
  have hQ0 : Q.coeff k ≠ 0 := mt trailingCoeff_eq_zero.mp hQ
  have : (ε - ((m : l) - k)) * (P.coeff m * Q.coeff k) = 0 := by linear_combination -h'
  push_cast
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_right (mul_ne_zero hP0 hQ0))

end Euler

section Derivation

variable {l E : Type*} [Field l] [Field E] [Algebra l E] {a : E} (δ : Derivation l E E)

/-- On `l(a)`, a derivation with `δ a = a` acts as `a · d/da`. -/
theorem derivation_aeval_div_aeval (hδa : δ a = a) (P Q : l[X]) :
    δ (aeval a P / aeval a Q) =
      aeval a (X * (derivative P * Q - P * derivative Q)) / aeval a (Q ^ 2) := by
  rw [Derivation.leibniz_div, δ.map_aeval, δ.map_aeval, hδa]
  simp only [smul_eq_mul, map_mul, map_sub, map_pow, aeval_X]
  ring

/-- A derivation with `δ a = a` maps `l(a)` into itself. -/
theorem derivation_mem_adjoin_simple (hδa : δ a = a) {g : E} (hg : g ∈ l⟮a⟯) : δ g ∈ l⟮a⟯ := by
  obtain ⟨P, Q, rfl⟩ := (mem_adjoin_simple_iff l g).mp hg
  rw [derivation_aeval_div_aeval δ hδa]
  exact (mem_adjoin_simple_iff l _).mpr ⟨_, _, rfl⟩

/-- A non-zero eigenvector `g ∈ l(a)` of a derivation `δ` with `δ a = a`, `a` transcendental,
has an integer eigenvalue. -/
theorem exists_intCast_eq_of_mem_adjoin (ha : Transcendental l a) (hδa : δ a = a) {g : E}
    (hg : g ∈ l⟮a⟯) (hg0 : g ≠ 0) {ε : l} (hε : δ g = algebraMap l E ε * g) :
    ∃ m : ℤ, ε = m := by
  obtain ⟨P, Q, rfl⟩ := (mem_adjoin_simple_iff l g).mp hg
  have hPa : aeval a P ≠ 0 := fun h ↦ hg0 (by rw [h, zero_div])
  have hQa : aeval a Q ≠ 0 := fun h ↦ hg0 (by rw [h, div_zero])
  have hP : P ≠ 0 := by rintro rfl; exact hPa (map_zero _)
  have hQ : Q ≠ 0 := by rintro rfl; exact hQa (map_zero _)
  refine exists_intCast_eq_of_euler hP hQ (sub_eq_zero.mp (transcendental_iff.mp ha _ ?_))
  rw [derivation_aeval_div_aeval δ hδa, map_pow, div_eq_iff (pow_ne_zero 2 hQa)] at hε
  rw [map_sub, hε, map_mul, aeval_C, map_mul]
  field_simp
  ring

/-- If `δ b = κ b` with `κ ∈ l`, then `δ (b ^ j) = j κ b ^ j`. -/
theorem derivation_pow_of_eq_mul {b : E} {κ : l} (hκ : δ b = algebraMap l E κ * b) (j : ℕ) :
    δ (b ^ j) = algebraMap l E (j * κ) * b ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Derivation.leibniz, ih, hκ, smul_eq_mul, smul_eq_mul]
    push_cast [map_add, map_mul, map_natCast]
    ring

/-- Applying `δ` to the minimal polynomial `f = ∑ f_j Y^j` of `b` over `l(a)`: if `δ a = a` and
`δ b = κ b` with `κ ∈ l`, then `δ f_j = (n - j) κ f_j` for all `j`, where `n = deg f`. -/
theorem derivation_coeff_minpoly (hδa : δ a = a) {b : E} (hb : IsIntegral l⟮a⟯ b) {κ : l}
    (hκ : δ b = algebraMap l E κ * b) (j : ℕ) :
    δ ((minpoly l⟮a⟯ b).coeff j) =
      algebraMap l E (((minpoly l⟮a⟯ b).natDegree - j) * κ) * (minpoly l⟮a⟯ b).coeff j := by
  set F := l⟮a⟯
  set f := minpoly F b
  set n := f.natDegree
  have hF : ∀ x : F, δ x ∈ F := fun x ↦ derivation_mem_adjoin_simple δ hδa x.2
  -- `f(b) = 0` and its image under `δ`
  have h1 : ∑ j ∈ Finset.range (n + 1), (f.coeff j : E) * b ^ j = 0 := by
    rw [← minpoly.aeval F b, aeval_eq_sum_range]
    rfl
  have h2 : ∑ j ∈ Finset.range (n + 1),
      (δ (f.coeff j) + algebraMap l E (j * κ) * f.coeff j) * b ^ j = 0 := by
    rw [← map_zero δ, ← h1, map_sum]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [Derivation.leibniz, derivation_pow_of_eq_mul δ hκ, smul_eq_mul, smul_eq_mul]
    ring
  -- `R = ∑ (δ f_j + (j - n) κ f_j) Y^j` has degree `< n` and `R(b) = 0`, so `R = 0`
  let c : ℕ → F := fun j ↦ ⟨δ (f.coeff j) + algebraMap l E ((j - n) * κ) * f.coeff j,
    add_mem (hF _) (mul_mem (IntermediateField.algebraMap_mem F _) (f.coeff j).2)⟩
  let R : F[X] := ∑ j ∈ Finset.range (n + 1), C (c j) * X ^ j
  have hc : ∀ j, n < j → c j = 0 := fun j hj ↦ by
    ext
    simp [c, coeff_eq_zero_of_natDegree_lt hj]
  have hcn : c n = 0 := by
    have hfn : f.coeff n = 1 := (minpoly.monic hb).coeff_natDegree
    ext
    simp [c, hfn]
  have hRc : ∀ j, R.coeff j = c j := by
    intro j
    simp only [R, finsetSum_coeff, coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq]
    split_ifs with hj
    · rfl
    · exact (hc j (by simpa using hj)).symm
  have hRb : aeval b R = 0 := by
    calc aeval b R = ∑ j ∈ Finset.range (n + 1),
          ((δ (f.coeff j) + algebraMap l E (j * κ) * f.coeff j) * b ^ j -
            algebraMap l E (n * κ) * ((f.coeff j : E) * b ^ j)) := by
          simp only [R, map_sum, map_mul, aeval_C, map_pow, aeval_X]
          refine Finset.sum_congr rfl fun j _ ↦ ?_
          simp only [IntermediateField.algebraMap_apply, c, map_mul, map_sub]
          ring
      _ = 0 := by rw [Finset.sum_sub_distrib, ← Finset.mul_sum, h1, h2, mul_zero, sub_zero]
  have hR : R = 0 := by
    by_contra hne
    have hdeg := minpoly.degree_le_of_ne_zero F b hne hRb
    rw [degree_eq_natDegree (minpoly.ne_zero hb)] at hdeg
    have hlt : R.degree < n := by
      rw [degree_lt_iff_coeff_zero]
      intro j hj
      rw [hRc]
      rcases hj.lt_or_eq with hj | rfl
      · exact hc j hj
      · exact hcn
    exact absurd (hdeg.trans_lt hlt) (lt_irrefl _)
  have hj := congrArg Subtype.val (hRc j)
  rw [hR, coeff_zero] at hj
  simp only [c, ZeroMemClass.coe_zero, map_mul, map_sub, map_natCast] at hj ⊢
  linear_combination -hj

/-- Separability of `b` gives an index `j` which is non-zero in `l` such that the coefficient of
`Y ^ j` in the minimal polynomial of `b` over `l(a)` is non-zero. -/
theorem exists_coeff_minpoly_ne_zero {b : E} (hb : IsSeparable l⟮a⟯ b) :
    ∃ j : ℕ, (j : l) ≠ 0 ∧ (minpoly l⟮a⟯ b).coeff j ≠ 0 := by
  set f := minpoly l⟮a⟯ b
  have hd : derivative f ≠ 0 :=
    (separable_iff_derivative_ne_zero (minpoly.irreducible hb.isIntegral)).mp hb
  have hi : (derivative f).coeff (derivative f).natDegree ≠ 0 := leadingCoeff_ne_zero.mpr hd
  rw [coeff_derivative] at hi
  refine ⟨(derivative f).natDegree + 1, fun h ↦ right_ne_zero_of_mul hi ?_,
    left_ne_zero_of_mul hi⟩
  have := congrArg (algebraMap l l⟮a⟯) h
  rwa [map_natCast, map_zero, Nat.cast_add, Nat.cast_one] at this

end Derivation

section Main

variable {l E : Type*} [Field l] [Field E] [Algebra l E]

/-- The eigenvalue lemma in explicit form: `j κ` is an integer for some natural number `j` which
is non-zero in `l`. See `eigenvalue_mem_primeField` for Blueprint Lemma 2.2. -/
theorem exists_natCast_mul_eigenvalue_eq_intCast
    (a : E) (ha : Transcendental l a) (δ : Derivation l E E) (hδa : δ a = a)
    (b : E) (hb0 : b ≠ 0) (hb : IsSeparable l⟮a⟯ b)
    (κ : l) (hκ : δ b = algebraMap l E κ * b) :
    ∃ (j : ℕ) (m : ℤ), (j : l) ≠ 0 ∧ (j : l) * κ = m := by
  set f := minpoly l⟮a⟯ b
  have key := derivation_coeff_minpoly δ hδa hb.isIntegral hκ
  -- `f_0 ≠ 0` gives `n κ ∈ ℤ`
  have hf0 : (f.coeff 0 : E) ≠ 0 := by
    simpa using minpoly.coeff_zero_ne_zero hb.isIntegral hb0
  obtain ⟨m₀, hm₀⟩ := exists_intCast_eq_of_mem_adjoin δ ha hδa (f.coeff 0).2 hf0 (key 0)
  -- `f_j ≠ 0` with `j ≠ 0` in `l` gives `(n - j) κ ∈ ℤ`
  obtain ⟨j, hj, hfj⟩ := exists_coeff_minpoly_ne_zero hb
  obtain ⟨m₁, hm₁⟩ := exists_intCast_eq_of_mem_adjoin δ ha hδa (f.coeff j).2
    (by simpa using hfj) (key j)
  refine ⟨j, m₀ - m₁, hj, ?_⟩
  push_cast at hm₀ hm₁ ⊢
  linear_combination hm₀ - hm₁

/-- Blueprint Lemma 2.2 (Eigenvalue lemma). Let `l ⊆ E` be fields, `a ∈ E` transcendental over
`l`, and `δ` a derivation of `E` with `δ(l) = 0` and `δ a = a`. Let `b ∈ Eˣ` be separable
algebraic over `l(a)` with `δ b = κ b` for some `κ ∈ l`. Then `κ` lies in the prime field
of `l`. -/
theorem eigenvalue_mem_primeField
    (a : E) (ha : Transcendental l a) (δ : Derivation l E E) (hδa : δ a = a)
    (b : E) (hb0 : b ≠ 0) (hb : IsSeparable l⟮a⟯ b)
    (κ : l) (hκ : δ b = algebraMap l E κ * b) :
    κ ∈ (⊥ : Subfield l) := by
  obtain ⟨j, m, hj, h⟩ :=
    exists_natCast_mul_eigenvalue_eq_intCast a ha δ hδa b hb0 hb κ hκ
  rw [show κ = m / j by rw [eq_div_iff hj, mul_comm, h]]
  exact div_mem (intCast_mem _ _) (natCast_mem _ _)

/-- The eigenvalue lemma in characteristic `0`: `κ` is a rational number. -/
theorem exists_ratCast_eq_eigenvalue [CharZero l]
    (a : E) (ha : Transcendental l a) (δ : Derivation l E E) (hδa : δ a = a)
    (b : E) (hb0 : b ≠ 0) (hb : IsSeparable l⟮a⟯ b)
    (κ : l) (hκ : δ b = algebraMap l E κ * b) :
    ∃ q : ℚ, (q : l) = κ := by
  obtain ⟨j, m, hj, h⟩ :=
    exists_natCast_mul_eigenvalue_eq_intCast a ha δ hδa b hb0 hb κ hκ
  refine ⟨(m : ℚ) / j, ?_⟩
  rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, div_eq_iff hj, mul_comm, h]

/-- The eigenvalue lemma in characteristic `p`: `κ` is the image of an element of `ZMod p`. -/
theorem exists_zmod_eq_eigenvalue (p : ℕ) [Fact p.Prime] [CharP l p]
    (a : E) (ha : Transcendental l a) (δ : Derivation l E E) (hδa : δ a = a)
    (b : E) (hb0 : b ≠ 0) (hb : IsSeparable l⟮a⟯ b)
    (κ : l) (hκ : δ b = algebraMap l E κ * b) :
    ∃ z : ZMod p, ZMod.castHom (dvd_refl p) l z = κ := by
  obtain ⟨j, m, hj, h⟩ :=
    exists_natCast_mul_eigenvalue_eq_intCast a ha δ hδa b hb0 hb κ hκ
  refine ⟨(m : ZMod p) / j, ?_⟩
  rw [map_div₀, map_intCast, map_natCast, div_eq_iff hj, mul_comm, h]

/-- The eigenvalue lemma in characteristic `p`: `κ` is the image of an integer. -/
theorem exists_intCast_eq_eigenvalue (p : ℕ) [Fact p.Prime] [CharP l p]
    (a : E) (ha : Transcendental l a) (δ : Derivation l E E) (hδa : δ a = a)
    (b : E) (hb0 : b ≠ 0) (hb : IsSeparable l⟮a⟯ b)
    (κ : l) (hκ : δ b = algebraMap l E κ * b) :
    ∃ m : ℤ, (m : l) = κ := by
  obtain ⟨z, hz⟩ := exists_zmod_eq_eigenvalue p a ha δ hδa b hb0 hb κ hκ
  refine ⟨z.val, ?_⟩
  rw [← hz, ZMod.castHom_apply, Int.cast_natCast, ZMod.natCast_val]

end Main

end MilnorAlgDep
