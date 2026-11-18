module

public import MilnorAlgDep.CharP.Levels

/-!
# Normalized triples

Blueprint, Section 3.2: Definition 3.4 (normalized triples), Lemma 3.5 and level triples,
element-wise.

Three distinct collinear points `P, Q, R` are given by elements `x ∈ P, y ∈ Q, z ∈ R` which are
pairwise algebraically independent over `l` and jointly dependent
(`MilnorAlgDep.IsCollinearTriple l x y z`). Such a triple is *normalized*
(`MilnorAlgDep.IsNormalized l x y z`) if each of `x, y, z` is separable algebraic over the field
generated over `l` by the other two.

The *level triple* `lt(P, Q, R)`, the diagonal `Γ`-orbit of the levels of normalized triples, is
recorded relative to a given collinear triple `(x, y, z)`: `levelTriple l p x y z = (j, k)` is
the unique pair with `(x, Frob^j y, Frob^k z)` normalized, so that
`(lev x, lev y + j, lev z + k)` is a level triple of `(Q_x, Q_y, Q_z)` (Lemma 3.5,
`isNormalized_levelTriple`, `levelTriple_eq_of_isNormalized`). For example, the integer `c(u, w)`
of blueprint (6.2) is `(levelTriple l p a b d).1` for representatives `a, b, d` of
`ψ(u), ψ(w), ψ(u + w)`.

## Main definitions

* `MilnorAlgDep.IsCollinearTriple l x y z`: `Q_x, Q_y, Q_z` are three distinct collinear points.
* `MilnorAlgDep.IsNormalized l x y z`: Definition 3.4 (including `IsCollinearTriple l x y z`).
* `MilnorAlgDep.levelTriple l p x y z : ℤ × ℤ`: the level triple of `(Q_x, Q_y, Q_z)` relative to
  `(x, y, z)` (`0` if `¬ IsCollinearTriple l x y z`).

## Main statements

* `exists_isNormalized` (Lemma 3.5(a)): `(x, Frob^j y, Frob^k z)` is normalized for some `j, k`.
* `IsNormalized.isNormalized_iff` (Lemma 3.5(b)): if `(x, y, z)` is normalized, then for
  `x', y', z'` in the same points, `(x', y', z')` is normalized iff
  `lev x' - lev x = lev y' - lev y = lev z' - lev z`.
* `IsNormalized.of_sepEquiv` (the "if" part of Lemma 3.5(b)), `IsNormalized.frobZ_iff`.
* `isNormalized_of_linearIndependent_modelD`: elements of a model with pairwise linearly
  independent differentials which are collinear form a normalized triple (the mechanism behind
  Lemma 4.6(d); also the convenient way to check normalization in the proof of Lemma 6.2).
* `isNormalized_mul`: `(x, y, x y)` is normalized (used in the proof of Lemma 6.11).
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential IntermediateField

variable {l L : Type*} [Field l] [Field L] [Algebra l L]

section Defs

variable (l) in
/-- `Q_x, Q_y, Q_z` are three distinct collinear points (blueprint Section 2.1): `x, y, z` are
pairwise algebraically independent over `l` and `z` is algebraic over `l(x, y)`. (This is
symmetric in `x, y, z`, see `IsCollinearTriple.swap₁₂`, `IsCollinearTriple.swap₂₃`.) -/
structure IsCollinearTriple (x y z : L) : Prop where
  indep₁₂ : AlgebraicIndependent l ![x, y]
  indep₁₃ : AlgebraicIndependent l ![x, z]
  indep₂₃ : AlgebraicIndependent l ![y, z]
  isAlgebraic : IsAlgebraic l⟮x, y⟯ z

variable (l) in
/-- **Blueprint Definition 3.4**: for three distinct collinear points `P, Q, R`, a triple
`(x, y, z)` with `x ∈ P \ l`, `y ∈ Q \ l`, `z ∈ R \ l` is *normalized* if each of `x, y, z` is
separable algebraic over the field generated over `l` by the other two. The hypothesis on the
points is part of the definition (`IsNormalized.toIsCollinearTriple`). -/
structure IsNormalized (x y z : L) : Prop extends IsCollinearTriple l x y z where
  isSeparable₁ : IsSeparable l⟮y, z⟯ x
  isSeparable₂ : IsSeparable l⟮x, z⟯ y
  isSeparable₃ : IsSeparable l⟮x, y⟯ z

end Defs

section Collinear

variable {x y z : L}

theorem IsCollinearTriple.transcendental₁ (h : IsCollinearTriple l x y z) : Transcendental l x :=
  (algebraicIndependent_pair_iff.1 h.indep₁₂).1

theorem IsCollinearTriple.transcendental₂ (h : IsCollinearTriple l x y z) : Transcendental l y :=
  (algebraicIndependent_pair_iff.1 h.indep₂₃).1

theorem IsCollinearTriple.transcendental₃ (h : IsCollinearTriple l x y z) : Transcendental l z :=
  (algebraicIndependent_pair_iff.1 (algebraicIndependent_pair_comm.1 h.indep₂₃)).1

theorem IsCollinearTriple.swap₁₂ (h : IsCollinearTriple l x y z) : IsCollinearTriple l y x z := by
  sorry

theorem IsCollinearTriple.swap₂₃ (h : IsCollinearTriple l x y z) : IsCollinearTriple l x z y := by
  sorry

/-- Being three distinct collinear points only depends on the points. -/
theorem IsCollinearTriple.of_samePoint {x' y' z' : L} (h : IsCollinearTriple l x y z)
    (hx : SamePoint l x' x) (hy : SamePoint l y' y) (hz : SamePoint l z' z) :
    IsCollinearTriple l x' y' z' := by
  sorry

theorem IsNormalized.swap₁₂ (h : IsNormalized l x y z) : IsNormalized l y x z := by
  sorry

theorem IsNormalized.swap₂₃ (h : IsNormalized l x y z) : IsNormalized l x z y := by
  sorry

/-- The "if" part of **blueprint Lemma 3.5(b)**: being normalized only depends on the levels, i.e.
on the `≈`-classes of `x, y, z`. -/
theorem IsNormalized.of_sepEquiv {x' y' z' : L} (h : IsNormalized l x y z)
    (hx : SepEquiv l x' x) (hy : SepEquiv l y' y) (hz : SepEquiv l z' z) :
    IsNormalized l x' y' z' := by
  sorry

/-- Normalization via differentials (the mechanism of blueprint Lemma 4.6(d)): if `x, y, z ∈ L_B`
have pairwise linearly independent differentials in `Ω_B` and `z` is algebraic over `l(x, y)`,
then `(x, y, z)` is normalized. (Pairwise algebraic independence follows from Lemma 4.5 and
separability from `isSeparable_of_linearIndependent_modelD_pair`.) -/
theorem isNormalized_of_linearIndependent_modelD [PerfectField l] {ι : Type*} {B : ι → L}
    (hx : x ∈ model l B) (hy : y ∈ model l B) (hz : z ∈ model l B)
    (hxy : LinearIndependent (model l B) ![modelD l B x, modelD l B y])
    (hxz : LinearIndependent (model l B) ![modelD l B x, modelD l B z])
    (hyz : LinearIndependent (model l B) ![modelD l B y, modelD l B z])
    (halg : IsAlgebraic l⟮x, y⟯ z) : IsNormalized l x y z := by
  sorry

/-- `(x, y, x y)` is normalized for `x, y` algebraically independent (used in the proof of blueprint
Lemma 6.11). -/
theorem isNormalized_mul (h : AlgebraicIndependent l ![x, y]) : IsNormalized l x y (x * y) := by
  sorry

end Collinear

section LevelTriples

variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]
variable {x y z : L}

/-- Being normalized is invariant under a diagonal Frobenius twist (blueprint proof of
Lemma 3.5(b)). -/
theorem IsNormalized.frobZ_iff (j : ℤ) :
    IsNormalized l (frobZ L p j x) (frobZ L p j y) (frobZ L p j z) ↔ IsNormalized l x y z := by
  sorry

/-- **Blueprint Lemma 3.5(a)**: normalized triples exist. More precisely, for three distinct
collinear points with elements `x, y, z`, there are `j, k ∈ ℤ` such that `(x, Frob^j y, Frob^k z)`
is normalized (the first entry can be prescribed, by Lemma 3.5(b)). -/
theorem exists_isNormalized (h : IsCollinearTriple l x y z) :
    ∃ j k : ℤ, IsNormalized l x (frobZ L p j y) (frobZ L p k z) := by
  sorry

/-- **Blueprint Lemma 3.5(b)**: if `(x, y, z)` is normalized and `x', y', z'` lie in the points of
`x, y, z`, then `(x', y', z')` is normalized iff there is `j` with `lev x' = lev x + j`,
`lev y' = lev y + j` and `lev z' = lev z + j`. -/
theorem IsNormalized.isNormalized_iff (h : IsNormalized l x y z) {x' y' z' : L}
    (hx : SamePoint l x' x) (hy : SamePoint l y' y) (hz : SamePoint l z' z) :
    IsNormalized l x' y' z' ↔
      levDiff l p x' x = levDiff l p y' y ∧ levDiff l p y' y = levDiff l p z' z := by
  sorry

open Classical in
variable (l) in
/-- **Blueprint Lemma 3.5 and the definition after it** (level triple `lt(P, Q, R)`), relative
to elements `x, y, z` of the points: the unique `(j, k) ∈ ℤ × ℤ` such that `(x, Frob^j y, Frob^k z)`
is normalized (`isNormalized_levelTriple`). Thus `(lev x, lev y + j, lev z + k)` is the level
triple of `(Q_x, Q_y, Q_z)`, and for any normalized triple `(x', y', z')` in these points,
`(j, k) = (lev y' - lev y - (lev x' - lev x), lev z' - lev z - (lev x' - lev x))`
(`levelTriple_eq_of_isNormalized`). It is `0` if no such pair exists, i.e. if
`¬ IsCollinearTriple l x y z`. -/
noncomputable def levelTriple (x y z : L) : ℤ × ℤ :=
  if h : ∃ jk : ℤ × ℤ, IsNormalized l x (frobZ L p jk.1 y) (frobZ L p jk.2 z) then h.choose else 0

/-- **Blueprint Lemma 3.5**: `(x, Frob^j y, Frob^k z)` is normalized for
`(j, k) = levelTriple l p x y z`. -/
theorem isNormalized_levelTriple (h : IsCollinearTriple l x y z) :
    IsNormalized l x (frobZ L p (levelTriple l p x y z).1 y)
      (frobZ L p (levelTriple l p x y z).2 z) := by
  sorry

/-- **Blueprint Lemma 3.5(b)**: the level triple can be computed from any normalized triple
`(x', y', z')` in the points of `x, y, z`. -/
theorem levelTriple_eq_of_isNormalized {x' y' z' : L} (h : IsNormalized l x' y' z')
    (hx : SamePoint l x' x) (hy : SamePoint l y' y) (hz : SamePoint l z' z) :
    levelTriple l p x y z =
      (levDiff l p y' y - levDiff l p x' x, levDiff l p z' z - levDiff l p x' x) := by
  sorry

end LevelTriples

end MilnorAlgDep
