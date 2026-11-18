module

public import MilnorAlgDep.Foundations.PerfectClosure
public import MilnorAlgDep.Standard.Differentials.Restrict
public import Mathlib.RingTheory.Multiplicity

/-!
# Uniqueness in Theorem A

Blueprint Lemma 6.13 (`lem:unique`). The statement is that of
`MilnorAlgDep.theoremA_perfect_unique`: if `ψ = r • [τ ·] = r' • [τ' ·]` with `ψ ≠ 0`, then
`τ' = Frob^j ∘ τ` and `r' = p^{-j} r`, `p` the characteristic exponent of the perfect field `L`.

## Relation to the blueprint statement

The blueprint assumes `τ⁻¹(l) = τ'⁻¹(l) = k ≠ K` and `r, r' ≠ 0`; here only `ψ ≠ 0` is assumed.
This implies the blueprint's hypotheses: if `ψ x₀ ≠ 0` then `r, r' ≠ 0`, and by (V1)
`τ x ∈ l ↔ ψ x = 0 ↔ τ' x ∈ l`, while `τ x₀ ∉ l`. The proof below only uses `r, r' ≠ 0` and the
existence of `x₀` with `τ x₀ ∉ l`.

## Proof

* Write `r / r' = p ^ j * A / B` with `A : ℤ`, `B : ℕ` non-zero in `L`, i.e. prime to `p`
  (`exists_eq_zpow_mul_div`; `j = 0` in characteristic `0`). Using `[Frob^j y] = p ^ j • [y]`
  (`cls_frobeniusEquiv_zpow`) one gets `A • [Frob^j τ y] = B • [τ' y]` for all `y ∈ Kˣ`.
* Let `x ∈ K` with `τ x ∉ l`, `T = Frob^j (τ x)`, `S' = τ' x`. Applied to `x` and `1 - x`, (V1)
  gives `T ^ A = c * S' ^ B` and `(1 - T) ^ A = c' * (1 - S') ^ B` with `c, c' ∈ l`
  (`V.exists_zpow_eq_mul_pow_of_smul_cls_eq`), and `T` is transcendental over `l`.
* `eq_of_zpow_eq_of_transcendental`: then `T = S'`. As `B` is prime to `p`, `S'` is separable
  over `l(T)`, so `S'` lies in the field `E` of elements of `L` separable algebraic over `l(T)`.
  There `d T` is a basis of `Ω[E⁄l]` (`MilnorAlgDep.kaehlerBasis`), so there is an
  `l`-derivation `δ` of `E` with `δ T = 1`. Applying `δ` to both relations and eliminating
  `δ S'` gives `A * (S' - T) = 0` (`eq_of_derivation_of_zpow_eq`). This replaces the blueprint's
  division of logarithmic differentials and does not need `d S' ≠ 0` separately.
* Hence `τ' = Frob^j ∘ τ` on `{x | τ x ∉ l}`, and on all of `K` since for `τ x ∈ l` one writes
  `x = (x + x₀) - x₀` with `τ (x + x₀), τ x₀ ∉ l`. Finally `r • [τ x₀] = r' p ^ j • [τ x₀]` with
  `[τ x₀] ≠ 0` gives `r' = p ^ (-j) * r`.

The signs of `A`, `B` play no role (integer powers throughout, `B > 0` by construction).
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

section Derivation

variable {l E : Type*} [Field l] [Field E] [Algebra l E]

/-- The computation at the heart of Blueprint Lemma 6.13: if `δ` is an `l`-derivation of `E` with
`δ s = 1`, and `s ^ A = c * s' ^ B`, `(1 - s) ^ A = c' * (1 - s') ^ B` with `c, c' ∈ l` and
`A ≠ 0` in `E`, then `s = s'`. (Taking logarithmic derivatives,
`A / s = B δs' / s'` and `A / (1 - s) = B δs' / (1 - s')`.) -/
theorem eq_of_derivation_of_zpow_eq (δ : Derivation l E E) {s s' : E} (hδ : δ s = 1)
    {A B : ℤ} (hA : (A : E) ≠ 0) (hs0 : s ≠ 0) (hs1 : 1 - s ≠ 0) (hs'0 : s' ≠ 0)
    (hs'1 : 1 - s' ≠ 0) {c c' : l} (h1 : s ^ A = algebraMap l E c * s' ^ B)
    (h2 : (1 - s) ^ A = algebraMap l E c' * (1 - s') ^ B) : s = s' := by
  have d1 := congrArg δ h1
  have d2 := congrArg δ h2
  rw [Derivation.leibniz_zpow, Derivation.leibniz, Derivation.leibniz_zpow,
    Derivation.map_algebraMap, hδ] at d1
  rw [Derivation.leibniz_zpow, Derivation.leibniz, Derivation.leibniz_zpow,
    Derivation.map_algebraMap, map_sub, Derivation.map_one_eq_zero, hδ, map_sub,
    Derivation.map_one_eq_zero] at d2
  simp only [smul_eq_mul, zsmul_eq_mul] at d1 d2
  rw [zpow_sub_one₀ hs0, zpow_sub_one₀ hs'0, h1] at d1
  rw [zpow_sub_one₀ hs1, zpow_sub_one₀ hs'1, h2] at d2
  have hc : algebraMap l E c ≠ 0 := left_ne_zero_of_mul (h1 ▸ zpow_ne_zero A hs0)
  have hc' : algebraMap l E c' ≠ 0 := left_ne_zero_of_mul (h2 ▸ zpow_ne_zero A hs1)
  set u := δ s'
  have f1 : (A : E) * s' = B * u * s := by
    refine mul_left_cancel₀ hc ?_
    field_simp at d1
    linear_combination d1
  have f2 : (A : E) * (1 - s') = B * u * (1 - s) := by
    refine mul_left_cancel₀ hc' ?_
    field_simp at d2
    linear_combination -d2
  have : (A : E) * (s' - s) = 0 := by linear_combination (1 - s) * f1 - s * f2
  exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hA)).symm

end Derivation

section Core

open IntermediateField KaehlerDifferential

variable {l L : Type*} [Field l] [Field L] [Algebra l L]

-- TODO(move): general field theory.
/-- If `y ^ n ∈ F` with `n ≠ 0` in `F` and `y ≠ 0`, then `y` is separable over `F`. -/
theorem isSeparable_of_pow_eq_algebraMap {F : Type*} [Field F] [Algebra F L] {y : L} {n : ℕ}
    (hn : (n : F) ≠ 0) (hy : y ≠ 0) {z : F} (h : y ^ n = algebraMap F L z) : IsSeparable F y := by
  have hz : z ≠ 0 := by
    rintro rfl
    rw [map_zero] at h
    exact hy (pow_eq_zero_iff (by rintro rfl; simp at hn) |>.1 h)
  refine (Polynomial.separable_X_pow_sub_C z hn hz).of_dvd (minpoly.dvd F y ?_)
  simp [h]

-- TODO(move): `Standard/Differentials/Basis.lean`.
omit [Algebra l L] in
/-- If `E` is separable algebraic over `l(x)` with `x` transcendental over `l`, there is an
`l`-derivation `δ` of `E` with `δ x = 1`: the coordinate of `d : E → Ω[E⁄l]` along the basis
`d x` (`MilnorAlgDep.kaehlerBasis`). -/
theorem exists_derivation_apply_eq_one {E : Type*} [Field E] [Algebra l E] {a : Unit → E}
    (hb : AlgebraicIndependent l a) (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) :
    ∃ δ : Derivation l E E, δ (a ()) = 1 := by
  let b := kaehlerBasis hb hsep
  refine ⟨(b.coord ()).compDer (D l E), ?_⟩
  change b.coord () (D l E (a ())) = 1
  rw [← kaehlerBasis_apply hb hsep (), Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same]

/-- **Core of Blueprint Lemma 6.13.** Let `S ∈ L` be transcendental over `l`, `A : ℤ` and
`B : ℕ` non-zero in `L` (i.e. prime to the characteristic exponent), and `c, c' ∈ l` with
`S ^ A = c * S' ^ B` and `(1 - S) ^ A = c' * (1 - S') ^ B`. Then `S = S'`.

As `B` is prime to the characteristic, `S'` is separable algebraic over `l(S)`; in the field `E`
of elements of `L` separable over `l(S)`, `d S` is a basis of `Ω[E⁄l]`, and the coordinate of `d`
along `d S` is a derivation `δ` of `E` with `δ S = 1`, to which
`MilnorAlgDep.eq_of_derivation_of_zpow_eq` applies. -/
theorem eq_of_zpow_eq_of_transcendental {S S' : L} (hS : Transcendental l S) {A : ℤ} {B : ℕ}
    (hA : (A : L) ≠ 0) (hB : (B : L) ≠ 0) {c c' : l}
    (h1 : S ^ A = algebraMap l L c * S' ^ B)
    (h2 : (1 - S) ^ A = algebraMap l L c' * (1 - S') ^ B) : S = S' := by
  have hS0 : S ≠ 0 := by
    rintro rfl
    exact hS isAlgebraic_zero
  have hS1 : 1 - S ≠ 0 := by
    intro h
    rw [← sub_eq_zero.1 h] at hS
    exact hS isAlgebraic_one
  have hB0 : B ≠ 0 := by
    rintro rfl
    simp at hB
  have hS'0 : S' ≠ 0 := by
    rintro rfl
    rw [zero_pow hB0, mul_zero] at h1
    exact zpow_ne_zero A hS0 h1
  have hS'1 : 1 - S' ≠ 0 := by
    intro h
    rw [h, zero_pow hB0, mul_zero] at h2
    exact zpow_ne_zero A hS1 h2
  have hc : algebraMap l L c ≠ 0 := left_ne_zero_of_mul (h1 ▸ zpow_ne_zero A hS0)
  -- `F = l(S)` and `E` = the elements of `L` separable over `F`
  let a : Unit → L := fun _ ↦ S
  let F := adjoin l (Set.range a)
  let E := (separableClosure F L).restrictScalars l
  have hSF : S ∈ F := subset_adjoin _ _ ⟨(), rfl⟩
  have hSE : S ∈ E := mem_separableClosure_adjoin a ()
  have hS'E : S' ∈ E := by
    have hz : (algebraMap l L c)⁻¹ * S ^ A ∈ F :=
      F.mul_mem (F.inv_mem (F.algebraMap_mem c)) (zpow_mem hSF A)
    have : IsSeparable F S' := by
      refine isSeparable_of_pow_eq_algebraMap (n := B) (z := ⟨_, hz⟩) ?_ hS'0 ?_
      · intro h
        apply hB
        simpa using congrArg (algebraMap F L) h
      · change S' ^ B = (algebraMap l L c)⁻¹ * S ^ A
        rw [h1, inv_mul_cancel_left₀ hc]
    exact mem_separableClosure_iff.2 this
  -- the derivation `δ` of `E` with `δ S = 1`
  obtain ⟨δ, hδ⟩ := exists_derivation_apply_eq_one
    (algebraicIndependent_restrictFamily E (mem_separableClosure_adjoin a)
      (algebraicIndependent_unique_type_iff.2 hS))
    (isSeparable_adjoin_restrictFamily_separableClosure a)
  have hcoe : ∀ (x : E) (n : ℤ), ((x ^ n : E) : L) = (x : L) ^ n := fun x n ↦ map_zpow₀ E.val x n
  have hA' : (A : E) ≠ 0 := fun h ↦ hA (by simpa using congrArg (algebraMap E L) h)
  refine congrArg Subtype.val (eq_of_derivation_of_zpow_eq δ hδ (s' := ⟨S', hS'E⟩) (A := A)
    (B := B) (c := c) (c' := c') hA' ?_ ?_ ?_ ?_ ?_ ?_)
  · exact fun h ↦ hS0 (congrArg Subtype.val h)
  · exact fun h ↦ hS1 (by simpa using congrArg Subtype.val h)
  · exact fun h ↦ hS'0 (congrArg Subtype.val h)
  · exact fun h ↦ hS'1 (by simpa using congrArg Subtype.val h)
  · apply Subtype.val_injective
    simpa [hcoe] using h1
  · apply Subtype.val_injective
    simpa [hcoe] using h2

end Core

section Classes

variable {l L : Type*} [Field l] [Field L] [Algebra l L]

-- TODO(move): `Foundations/V.lean`.
/-- (V1) in the form used in Blueprint Lemma 6.13: if `A • [u] = B • [v]` in `V l L` and `l` is
relatively algebraically closed in `L`, then `u ^ A = c * v ^ B` for some `c ∈ l`. -/
theorem V.exists_zpow_eq_mul_pow_of_smul_cls_eq [IsRelAlgClosed l L] {u v : Lˣ} {A : ℤ} {B : ℕ}
    (h : (A : ℚ) • cls (constUnits l L) (.ofMul u) = (B : ℚ) • cls (constUnits l L) (.ofMul v)) :
    ∃ c : l, (u : L) ^ A = algebraMap l L c * (v : L) ^ B := by
  have key : cls (constUnits l L) (.ofMul (u ^ A / v ^ B)) = 0 := by
    rw [cls_div, cls_zpow, cls_pow, ← Int.cast_smul_eq_zsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, h,
      sub_self]
  obtain ⟨c, hc⟩ := (V.cls_eq_zero_iff' _).1 key
  refine ⟨c, ?_⟩
  rw [hc, Units.val_div_eq_div_val, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
    div_mul_cancel₀ _ (pow_ne_zero _ v.ne_zero)]

end Classes

section Frobenius

variable {L : Type*} [Field L]

-- TODO(move): `Foundations/`.
/-- The Frobenius twist on classes: `[Frob^j y] = p ^ j • [y]`, where `p` is the characteristic
exponent of the perfect field `L`. -/
theorem cls_frobeniusEquiv_zpow [PerfectField L] (H : Subgroup Lˣ) (j : ℤ) (y : Lˣ) :
    cls H (.ofMul (Units.map
        (((frobeniusEquiv L (ringExpChar L) ^ j : L ≃+* L) : L →+* L) : L →* L) y)) =
      ((ringExpChar L : ℚ) ^ j) • cls H (.ofMul y) := by
  set p := ringExpChar L
  set σ := frobeniusEquiv L p
  have hnat : ∀ (n : ℕ) (z : Lˣ),
      Units.map (((σ ^ n : L ≃+* L) : L →+* L) : L →* L) z = z ^ p ^ n := by
    intro n z
    ext
    rw [Units.coe_map, Units.val_pow_eq_pow_val, ← iterateFrobeniusEquiv_eq_pow]
    rfl
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (expChar_ne_zero L p)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · rw [zpow_natCast, hnat, cls_pow, zpow_natCast, ← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_pow]
  · set z := Units.map (((σ ^ (-(n : ℤ)) : L ≃+* L) : L →+* L) : L →* L) y
    have hz : Units.map (((σ ^ n : L ≃+* L) : L →+* L) : L →* L) z = y := by
      ext
      simp [z, zpow_neg]
    conv_rhs => rw [← hz, hnat, cls_pow]
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, zpow_neg, zpow_natCast, Nat.cast_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hp), one_smul]

end Frobenius

/-- Every non-zero rational number is `p ^ j * A / B` with `A, B` non-zero in `L` (i.e. prime to
`p`), where `p` is the characteristic exponent of `L`. In characteristic `0`, `j = 0`. -/
theorem exists_eq_zpow_mul_div (L : Type*) [Field L] {q : ℚ} (hq : q ≠ 0) :
    ∃ (j : ℤ) (A : ℤ) (B : ℕ), (A : L) ≠ 0 ∧ (B : L) ≠ 0 ∧
      q = (ringExpChar L : ℚ) ^ j * A / B := by
  generalize hp : ringExpChar L = p
  rcases ringExpChar.of_eq hp with _ | ⟨hprime⟩
  · refine ⟨0, q.num, q.den, ?_, ?_, ?_⟩
    · exact_mod_cast Rat.num_ne_zero.2 hq
    · exact_mod_cast q.den_nz
    · rw [zpow_zero, one_mul, Rat.num_div_den]
  · have hnum : q.num ≠ 0 := Rat.num_ne_zero.2 hq
    have hfin : FiniteMultiplicity (p : ℤ) q.num :=
      Int.finiteMultiplicity_iff.2 ⟨by simpa using hprime.ne_one, hnum⟩
    obtain ⟨A, hA, hAdvd⟩ := hfin.exists_eq_pow_mul_and_not_dvd
    set m := multiplicity (p : ℤ) q.num
    obtain ⟨β, B, hBdvd, hB⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hprime.ne_one
    refine ⟨(m : ℤ) - β, A, B, ?_, ?_, ?_⟩
    · rwa [Ne, CharP.intCast_eq_zero_iff L p]
    · rwa [Ne, CharP.cast_eq_zero_iff L p]
    · have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hprime.ne_zero
      have hB0 : (B : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by rintro rfl; simp at hBdvd)
      conv_lhs => rw [← Rat.num_div_den q, hA, hB]
      rw [zpow_sub₀ hp0, zpow_natCast, zpow_natCast]
      push_cast
      field_simp

variable {K L : Type*} [Field K] [Field L]

/-- **Blueprint Lemma 6.13** (uniqueness in Theorem A), for a perfect field `L`. See
`MilnorAlgDep.theoremA_perfect_unique` for the discussion of the statement, and the module
docstring for the proof. The hypothesis `ψ ≠ 0` replaces the blueprint's `τ⁻¹(l) = τ'⁻¹(l) ≠ K`
and `r, r' ≠ 0`, which it implies. -/
theorem theoremA_perfect_unique_aux [PerfectField L] (l : Subfield L)
    (hl : ∀ x : L, IsAlgebraic l x → x ∈ l)
    (ψ : Additive Kˣ →+ V l L) (hψ : ψ ≠ 0)
    (τ τ' : K →+* L) (r r' : ℚ)
    (h : ∀ x : Kˣ, ψ (.ofMul x) = r • 〚Units.map (τ : K →* L) x〛)
    (h' : ∀ x : Kˣ, ψ (.ofMul x) = r' • 〚Units.map (τ' : K →* L) x〛) :
    ∃ j : ℤ, τ' = ((frobeniusEquiv L (ringExpChar L) ^ j : L ≃+* L) : L →+* L).comp τ ∧
      r' = (ringExpChar L : ℚ) ^ (-j) * r := by
  have : IsRelAlgClosed l L := IsRelAlgClosed.of_subfield hl
  set p := ringExpChar L
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (expChar_ne_zero L p)
  -- (V1): `[a] = 0 ↔ a ∈ l`
  have V1 : ∀ a : Lˣ, cls (constUnits l L) (.ofMul a) = 0 ↔ (a : L) ∈ l := fun a ↦
    (V.cls_eq_zero_iff a).trans mem_constUnits_subfield
  have hrel : ∀ y : Kˣ, r • cls (constUnits l L) (.ofMul (Units.map (τ : K →* L) y)) =
      r' • cls (constUnits l L) (.ofMul (Units.map (τ' : K →* L) y)) :=
    fun y ↦ (h y).symm.trans (h' y)
  -- `ψ ≠ 0`: there is `x₀` with `ψ x₀ ≠ 0`; then `r, r' ≠ 0` and `τ x₀ ∉ l`
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : Kˣ, ψ (.ofMul x₀) ≠ 0 := by
    by_contra! H
    exact hψ (AddMonoidHom.ext fun x ↦ H (Additive.toMul x))
  have hr : r ≠ 0 := by
    rintro rfl
    exact hx₀ (by rw [h, zero_smul])
  have hr' : r' ≠ 0 := by
    rintro rfl
    exact hx₀ (by rw [h', zero_smul])
  have hτx₀ : τ x₀ ∉ l := by
    intro hmem
    exact hx₀ (by rw [h, (V1 _).2 hmem, smul_zero])
  -- write `r / r' = p ^ j * A / B` with `A, B` prime to `p`
  obtain ⟨j, A, B, hA, hB, hAB⟩ := exists_eq_zpow_mul_div L (div_ne_zero hr hr')
  have hB0 : (B : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by rintro rfl; simp at hB)
  have hAB' : (A : ℚ) * (p : ℚ) ^ j * r' = B * r := by
    field_simp at hAB
    linear_combination -hAB
  set f : L →+* L := ((frobeniusEquiv L p ^ j : L ≃+* L) : L →+* L)
  have hfrob : ∀ y : Lˣ, cls (constUnits l L) (.ofMul (Units.map (f : L →* L) y)) =
      ((p : ℚ) ^ j) • cls (constUnits l L) (.ofMul y) :=
    cls_frobeniusEquiv_zpow _ j
  -- `A • [Frob^j τ y] = B • [τ' y]`
  have e : ∀ y : Kˣ,
      (A : ℚ) • cls (constUnits l L) (.ofMul (Units.map (f : L →* L) (Units.map (τ : K →* L) y))) =
        (B : ℚ) • cls (constUnits l L) (.ofMul (Units.map (τ' : K →* L) y)) := by
    intro y
    have : (B : ℚ) • cls (constUnits l L) (.ofMul (Units.map (τ' : K →* L) y)) =
        (B / r') • r' • cls (constUnits l L) (.ofMul (Units.map (τ' : K →* L) y)) := by
      rw [smul_smul, div_mul_cancel₀ _ hr']
    rw [hfrob, smul_smul, this, ← hrel, smul_smul]
    congr 1
    field_simp
    linear_combination hAB'
  -- the main step: `τ' x = Frob^j (τ x)` for `x ∉ k`
  have key : ∀ x : K, τ x ∉ l → τ' x = f (τ x) := by
    intro x hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      exact hx (by rw [map_zero]; exact l.zero_mem)
    have hx1 : 1 - x ≠ 0 := by
      intro h0
      rw [← sub_eq_zero.1 h0, map_one] at hx
      exact hx l.one_mem
    obtain ⟨c, hc⟩ := V.exists_zpow_eq_mul_pow_of_smul_cls_eq (e (Units.mk0 x hx0))
    obtain ⟨c', hc'⟩ := V.exists_zpow_eq_mul_pow_of_smul_cls_eq (e (Units.mk0 (1 - x) hx1))
    have hT : cls (constUnits l L)
        (.ofMul (Units.map (f : L →* L) (Units.map (τ : K →* L) (Units.mk0 x hx0)))) ≠ 0 := by
      rw [hfrob]
      exact smul_ne_zero (zpow_ne_zero j hp) fun h0 ↦ hx ((V1 _).1 h0)
    have htr : Transcendental l (f (τ x)) :=
      IsRelAlgClosed.transcendental fun hm ↦ hT ((V.cls_eq_zero_iff' _).2 hm)
    simp only [Units.coe_map, Units.val_mk0, MonoidHom.coe_ofClass, map_sub, map_one] at hc hc'
    exact (eq_of_zpow_eq_of_transcendental htr hA hB hc hc').symm
  -- hence `τ' = Frob^j ∘ τ` everywhere
  have hτ' : τ' = f.comp τ := by
    ext x
    rw [RingHom.comp_apply]
    by_cases hx : τ x ∈ l
    · have hx' : τ (x + x₀) ∉ l := fun hm ↦ hτx₀ (by simpa using l.sub_mem hm hx)
      have e1 := key _ hx'
      rw [map_add, map_add, map_add, key _ hτx₀] at e1
      exact add_right_cancel e1
    · exact key x hx
  refine ⟨j, hτ', ?_⟩
  -- and then `r = r' * p ^ j`
  have h₀ := hrel x₀
  have hcomp : Units.map ((f.comp τ : K →+* L) : K →* L) x₀ =
      Units.map (f : L →* L) (Units.map (τ : K →* L) x₀) := Units.ext rfl
  rw [hτ', hcomp, hfrob, smul_smul] at h₀
  have hne : cls (constUnits l L) (.ofMul (Units.map (τ : K →* L) x₀)) ≠ 0 :=
    fun h0 ↦ hτx₀ ((V1 _).1 h0)
  have hrr : r = r' * (p : ℚ) ^ j := smul_left_injective ℚ hne h₀
  rw [hrr, zpow_neg, ← mul_assoc, mul_comm _ r', mul_assoc, inv_mul_cancel₀ (zpow_ne_zero j hp),
    mul_one]

end MilnorAlgDep
