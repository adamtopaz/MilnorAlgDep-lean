module

public import MilnorAlgDep.Standard.Differentials.Independence
public import MilnorAlgDep.Standard.Differentials.KernelD

/-!
# `p`-power roots and non-vanishing differentials

This file formalizes the second part of blueprint Lemma 2.3 (`lem:standard`), (S3): if `E` is
separable algebraic over `l(a)` for an algebraically independent family `a`, `l` is perfect of
characteristic `p > 0` and relatively algebraically closed in `E`, then for `y ∈ E` not in `l`
there are unique `j` and `z` with `z ^ p ^ j = y` and `d z ≠ 0`; `j` is the largest integer with
`y ∈ E ^ (p ^ j)` (`MilnorAlgDep.exists_pow_pow_eq_kaehler_D_ne_zero`,
`MilnorAlgDep.existsUnique_pow_pow_eq_kaehler_D_ne_zero`,
`MilnorAlgDep.pow_pow_eq_iff_le_of_kaehler_D_ne_zero`).

## Proof

By the first part (`MilnorAlgDep.kaehler_D_eq_zero_iff_exists_pow_eq`) it suffices to show that
`y` is not a `p ^ j`-th power for all `j` (`MilnorAlgDep.isAlgebraic_of_forall_exists_pow_pow_eq`).
The blueprint uses a discrete valuation; we argue with differentials instead. The perfect core
`P = ⋂ⱼ E ^ (p ^ j)` (`MilnorAlgDep.perfectCore`) is a perfect field on which `d` vanishes, so
`Ω[E⁄l] → Ω[E⁄P]` is injective (its kernel is spanned by `d P`). Hence the `d aᵢ` remain linearly
independent in `Ω[E⁄P]` and `a` is algebraically independent over `P`, by Lemma 4.6 over the
perfect field `P` (`MilnorAlgDep.algebraicIndependent_of_linearIndependent_kaehler_D`). An
element `y ∈ P` transcendental over `l` would make `(y, a)` algebraically independent over `l`,
which is absurd as `y` is algebraic over `l(a)`.
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential IntermediateField

variable {l E : Type*} [Field l] [Field E] [Algebra l E]
variable (p : ℕ) [Fact p.Prime] [CharP E p]
variable {ι : Type*} {a : ι → E}
variable [PerfectField l]

omit [PerfectField l] in
/-- `x ↦ x ^ p ^ j` is injective on `E`. -/
theorem pow_pow_injective (j : ℕ) : Function.Injective fun x : E ↦ x ^ p ^ j := by
  have : ExpChar E p := ExpChar.prime Fact.out
  intro x y h
  exact (iterateFrobenius E p j).injective (by simpa [iterateFrobenius_def] using h)

variable (l E) in
/-- The perfect core `⋂ⱼ E ^ (p ^ j)` of `E`: the elements that are `p ^ j`-th powers for all
`j`. It is a perfect intermediate field. -/
def perfectCore : IntermediateField l E where
  carrier := {x | ∀ j, ∃ z, z ^ p ^ j = x}
  mul_mem' {x y} hx hy j := by
    obtain ⟨z, rfl⟩ := hx j
    obtain ⟨w, rfl⟩ := hy j
    exact ⟨z * w, mul_pow ..⟩
  add_mem' {x y} hx hy j := by
    obtain ⟨z, rfl⟩ := hx j
    obtain ⟨w, rfl⟩ := hy j
    exact ⟨z + w, add_pow_char_pow ..⟩
  algebraMap_mem' c j := by
    have : CharP l p := (Algebra.charP_iff l E p).mpr inferInstance
    obtain ⟨c', rfl⟩ := exists_pow_pow_eq_of_perfectField p c j
    exact ⟨algebraMap l E c', (map_pow _ _ _).symm⟩
  inv_mem' x hx j := by
    obtain ⟨z, rfl⟩ := hx j
    exact ⟨z⁻¹, inv_pow ..⟩

/-- Membership in the perfect core. -/
theorem mem_perfectCore {x : E} : x ∈ perfectCore l E p ↔ ∀ j, ∃ z, z ^ p ^ j = x :=
  Iff.rfl

/-- The perfect core is a perfect ring. -/
theorem perfectRing_perfectCore : PerfectRing (perfectCore l E p) p := by
  have : CharP (perfectCore l E p) p := (Algebra.charP_iff _ E p).mpr inferInstance
  have : ExpChar (perfectCore l E p) p := ExpChar.prime Fact.out
  refine PerfectRing.ofSurjective _ p fun x ↦ ?_
  obtain ⟨z, hz⟩ := x.2 1
  rw [pow_one] at hz
  refine ⟨⟨z, fun j ↦ ?_⟩, ?_⟩
  · obtain ⟨w, hw⟩ := x.2 (j + 1)
    refine ⟨w, pow_pow_injective p 1 ?_⟩
    simp only
    rw [pow_one, hz, ← hw, ← pow_mul, ← pow_succ]
  · apply Subtype.ext
    rw [frobenius_def, SubmonoidClass.coe_pow]
    exact hz

/-- The key step of **blueprint Lemma 2.3 (S3)**: if `E` is separable algebraic over `l(a)`, with
`a` algebraically independent and `l` perfect of characteristic `p`, then an element of `E` which
is a `p ^ j`-th power in `E` for every `j` is algebraic over `l`.

Proof: the perfect core `P = ⋂ⱼ E ^ (p ^ j)` is a perfect field and `d P = 0`, so
`Ω[E⁄l] → Ω[E⁄P]` is injective; hence the `d aᵢ` stay linearly independent in `Ω[E⁄P]`, so `a` is
algebraically independent over `P` (Lemma 4.6 over the perfect field `P`). If `y ∈ P` were
transcendental over `l`, then `(y, a)` would be algebraically independent over `l`, contradicting
that `y` is algebraic over `l(a)`. (This replaces the discrete valuation argument of the
blueprint.) -/
theorem isAlgebraic_of_forall_exists_pow_pow_eq (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E) {y : E}
    (hy : ∀ j, ∃ z, z ^ p ^ j = y) : IsAlgebraic l y := by
  by_contra htr
  set P := perfectCore l E p
  have hyP : y ∈ P := hy
  have : PerfectRing P p := perfectRing_perfectCore p
  have : PerfectField P := PerfectRing.toPerfectField P p
  have hD : ∀ x ∈ P, D l E x = 0 := by
    intro x hx
    obtain ⟨z, rfl⟩ := hx 1
    rw [pow_one]
    exact kaehler_D_pow_char p z
  have hinj : LinearMap.ker (KaehlerDifferential.map l P E E) = ⊥ := by
    rw [← range_mapBaseChange, eq_bot_iff]
    refine (range_mapBaseChange_le l P E).trans ?_
    rw [Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact (hD x x.2 : _)
  have hli : LinearIndependent E fun i ↦ D P E (a i) := by
    have := (linearIndependent_kaehler_D hb hsep).map' _ hinj
    simpa [Function.comp_def] using this
  have hP : AlgebraicIndependent P a := algebraicIndependent_of_linearIndependent_kaehler_D hli
  have h1 : AlgebraicIndependent l fun _ : Unit ↦ y := algebraicIndependent_unique_type_iff.mpr htr
  have h2 := h1.sumElim_of_tower (S := P) (by rintro _ ⟨_, rfl⟩; exact ⟨⟨y, hyP⟩, rfl⟩) hP
  have h3 : AlgebraicIndependent l (Sum.elim (fun _ : Unit ↦ y) a) := by
    refine (algebraicIndependent_equiv' (Equiv.sumComm Unit ι) ?_).mpr h2
    ext (u | i) <;> rfl
  have h4 := (AlgebraicIndependent.sumElim_iff.mp h3).2
  rw [algebraicIndependent_unique_type_iff] at h4
  have h5 : IsAlgebraic (adjoin l (Set.range a)) y := (hsep.isSeparable' y).isIntegral.isAlgebraic
  rw [isAlgebraic_adjoin_iff] at h5
  exact h4 h5


/-- **Blueprint Lemma 2.3 (S3)**: if moreover `l` is relatively algebraically closed in `E`, an
element `y ∉ l` is not a `p ^ j`-th power in `E` for all `j`. -/
theorem not_forall_exists_pow_pow_eq (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E)
    (hl : ∀ x : E, IsAlgebraic l x → x ∈ (algebraMap l E).range) {y : E}
    (hy : y ∉ (algebraMap l E).range) : ¬ ∀ j, ∃ z, z ^ p ^ j = y :=
  fun h ↦ hy (hl y (isAlgebraic_of_forall_exists_pow_pow_eq p hb hsep h))

/-- **Blueprint Lemma 2.3 (S3)**: if `E` is separable algebraic over `l(a)` with `a`
algebraically independent, `l` is perfect of characteristic `p` and relatively algebraically
closed in `E`, then every `y ∈ E` not in `l` is of the form `y = z ^ p ^ j` with `d z ≠ 0`.
(`j` is the largest integer with `y ∈ E ^ (p ^ j)`, and `j`, `z` are unique; see
`pow_pow_eq_iff_le_of_kaehler_D_ne_zero`, `eq_of_pow_pow_eq_of_kaehler_D_ne_zero` and
`existsUnique_pow_pow_eq_kaehler_D_ne_zero`.) -/
theorem exists_pow_pow_eq_kaehler_D_ne_zero (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E)
    (hl : ∀ x : E, IsAlgebraic l x → x ∈ (algebraMap l E).range) {y : E}
    (hy : y ∉ (algebraMap l E).range) : ∃ (j : ℕ) (z : E), z ^ p ^ j = y ∧ D l E z ≠ 0 := by
  classical
  have hex : ∃ j, ¬ ∃ z, z ^ p ^ j = y := by
    by_contra h
    push Not at h
    exact not_forall_exists_pow_pow_eq p hb hsep hl hy h
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    have := Nat.find_spec hex
    rw [h0] at this
    exact this ⟨y, by rw [pow_zero, pow_one]⟩
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  obtain ⟨z, hz⟩ : ∃ z, z ^ p ^ j = y := by
    by_contra h
    exact Nat.find_min hex (by omega : j < Nat.find hex) h
  refine ⟨j, z, hz, fun hDz ↦ ?_⟩
  obtain ⟨w, rfl⟩ := exists_pow_eq_of_kaehler_D_eq_zero p hb hsep hDz
  have := Nat.find_spec hex
  rw [hj] at this
  exact this ⟨w, by rw [← hz, ← pow_mul, ← pow_succ']⟩

omit [PerfectField l] in
/-- In characteristic `p`: if `y = z ^ p ^ j` with `d z ≠ 0` in `Ω[E⁄l]`, then `y` is a `p ^ k`-th
power in `E` exactly for `k ≤ j`. -/
theorem pow_pow_eq_iff_le_of_kaehler_D_ne_zero {y z : E} {j : ℕ} (hz : z ^ p ^ j = y)
    (hDz : D l E z ≠ 0) (k : ℕ) : (∃ w, w ^ p ^ k = y) ↔ k ≤ j := by
  constructor
  · rintro ⟨w, hw⟩
    by_contra hkj
    push Not at hkj
    have h : (w ^ p ^ (k - j)) ^ p ^ j = z ^ p ^ j := by
      rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hkj.le, hw, hz]
    obtain rfl := pow_pow_injective p j h
    exact hDz (kaehler_D_pow_char_pow p w (by omega))
  · intro hkj
    exact ⟨z ^ p ^ (j - k), by rw [← pow_mul, ← pow_add, Nat.sub_add_cancel hkj, hz]⟩

omit [PerfectField l] in
/-- Uniqueness in **blueprint Lemma 2.3 (S3)**: the exponent `j` and the root `z` with
`z ^ p ^ j = y` and `d z ≠ 0` are unique. -/
theorem eq_of_pow_pow_eq_of_kaehler_D_ne_zero {y z z' : E} {j j' : ℕ} (hz : z ^ p ^ j = y)
    (hDz : D l E z ≠ 0) (hz' : z' ^ p ^ j' = y) (hDz' : D l E z' ≠ 0) : j = j' ∧ z = z' := by
  have h1 := (pow_pow_eq_iff_le_of_kaehler_D_ne_zero p hz hDz j').mp ⟨z', hz'⟩
  have h2 := (pow_pow_eq_iff_le_of_kaehler_D_ne_zero p hz' hDz' j).mp ⟨z, hz⟩
  obtain rfl : j = j' := le_antisymm h2 h1
  exact ⟨rfl, pow_pow_injective p j (hz.trans hz'.symm)⟩

/-- **Blueprint Lemma 2.3 (S3)**, existence and uniqueness of `(j, z)` with `z ^ p ^ j = y` and
`d z ≠ 0`. -/
theorem existsUnique_pow_pow_eq_kaehler_D_ne_zero (hb : AlgebraicIndependent l a)
    (hsep : Algebra.IsSeparable (adjoin l (Set.range a)) E)
    (hl : ∀ x : E, IsAlgebraic l x → x ∈ (algebraMap l E).range) {y : E}
    (hy : y ∉ (algebraMap l E).range) :
    ∃! jz : ℕ × E, jz.2 ^ p ^ jz.1 = y ∧ D l E jz.2 ≠ 0 := by
  obtain ⟨j, z, hz, hDz⟩ := exists_pow_pow_eq_kaehler_D_ne_zero p hb hsep hl hy
  refine ⟨(j, z), ⟨hz, hDz⟩, fun ⟨j', z'⟩ ⟨hz', hDz'⟩ ↦ ?_⟩
  obtain ⟨rfl, rfl⟩ := eq_of_pow_pow_eq_of_kaehler_D_ne_zero p hz' hDz' hz hDz
  rfl

end MilnorAlgDep
