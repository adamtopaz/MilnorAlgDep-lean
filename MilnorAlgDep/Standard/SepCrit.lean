module

public import MilnorAlgDep.Standard.Differentials
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Derivation.MapCoeffs
public import Mathlib.RingTheory.Polynomial.SeparableDegree
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Polynomial.Eval.Subring

/-!
# A differential separability criterion

Blueprint Lemma 3.1 (`lem:sepcrit`) describes separability of `yᵢ` over `l(yⱼ : j ≠ i)` through the
partial derivatives of the irreducible relation `f` of `(y₁, …, y_m)`. In the blueprint it is used
in two ways: to read off separability from a linear relation `∑ f_{Yᵢ} d yᵢ = 0` (Lemmas 3.2, 3.5,
4.6 and 6.2), and to know that some `f_{Yᵢ}` is non-zero. We replace it by the following criterion,
which avoids multivariate polynomials altogether:

* `MilnorAlgDep.isSeparable_adjoin_of_linearIndependent_kaehler_D`: let `l` be perfect and
  `x : ι → E`; if the differentials `d xᵢ` are linearly independent in `Ω[E⁄l]` and `y ∈ E` is
  algebraic over `l(x)`, then `y` is separable over `l(x)`.

Proof sketch: otherwise the minimal polynomial `f = ∑ cᵢ Xⁱ` of `y` over `K = l(x)` has `f' = 0`,
so `0 = d (f(y)) = ∑ᵢ yⁱ d cᵢ = ∑ₖ (∑ᵢ ∂ₖ(cᵢ) yⁱ) d xₖ` in `Ω[E⁄l]`, where `∂ₖ` are the coordinate
derivations of `K` for the basis `(d xₖ)` of `Ω[K⁄l]` (Lemma 2.1 (S2)). Hence each polynomial
`∑ᵢ ∂ₖ(cᵢ) Xⁱ`, of degree `< deg f`, vanishes at `y`, so is zero; so `d cᵢ = 0` in `Ω[K⁄l]` and
`cᵢ ∈ K ^ p` (Lemma 2.1 (S3), `MilnorAlgDep.kaehler_D_eq_zero_iff_exists_pow_eq`). Then `f` is a
`p`-th power, contradicting irreducibility.

We also record (`MilnorAlgDep.exists_isSeparable_pow_pow`) that in characteristic `p` some
`p ^ n`-th power of an algebraic element is separable.
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential IntermediateField

variable {l E : Type*} [Field l] [Field E] [Algebra l E]

/-- In characteristic `p`, if `y` is algebraic over `K` then `y ^ p ^ n` is separable over `K`
for some `n`. -/
theorem exists_isSeparable_pow_pow {K : Type*} [Field K] [Algebra K E] (p : ℕ) [ExpChar K p]
    {y : E} (hy : IsAlgebraic K y) : ∃ n : ℕ, IsSeparable K (y ^ p ^ n) := by
  obtain ⟨g, hg, n, hgf⟩ := (minpoly.irreducible hy.isIntegral).hasSeparableContraction p
  refine ⟨n, hg.of_dvd (minpoly.dvd K _ ?_)⟩
  rw [← Polynomial.expand_aeval, hgf, minpoly.aeval]

namespace SepCrit

variable {ι : Type*}

/-- Linear functionals dual to a linearly independent family of a vector space. -/
theorem exists_linearMap_eq_ite [DecidableEq ι] {V : Type*} [AddCommGroup V] [Module E V]
    {v : ι → V} (hv : LinearIndependent E v) (k : ι) :
    ∃ φ : V →ₗ[E] E, ∀ j, φ (v j) = if j = k then 1 else 0 := by
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend ((Module.Basis.span hv).coord k)
  refine ⟨φ, fun j ↦ ?_⟩
  have h := congrArg (fun f ↦ f ⟨v j, Submodule.subset_span (Set.mem_range_self j)⟩) hφ
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at h
  rw [h, ← Module.Basis.span_apply hv j, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_apply]

variable [PerfectField l]

/-- The characteristic `p` case of `isSeparable_adjoin_of_linearIndependent_kaehler_D`. -/
theorem isSeparable (p : ℕ) [Fact p.Prime] [CharP l p] {x : ι → E}
    (h : LinearIndependent E fun i ↦ D l E (x i)) {y : E}
    (hy : IsAlgebraic (adjoin l (Set.range x)) y) : IsSeparable (adjoin l (Set.range x)) y := by
  classical
  set K := adjoin l (Set.range x)
  have : CharP E p := (Algebra.charP_iff l E p).mp inferInstance
  have : CharP K p := (Algebra.charP_iff l K p).mp inferInstance
  have hxK : ∀ i, x i ∈ K := fun i ↦ subset_adjoin _ _ ⟨i, rfl⟩
  have hb : AlgebraicIndependent l x := algebraicIndependent_of_linearIndependent_kaehler_D h
  have hb' := algebraicIndependent_restrictFamily K hxK hb
  have hsep' := isSeparable_adjoin_restrictFamily K hxK fun z hz ↦
    isSeparable_algebraMap (⟨z, hz⟩ : K)
  set bK := kaehlerBasis hb' hsep'
  set dK := coordDerivation hb' hsep'
  -- the derivations `δ k : E → E` with `δ k (x j) = δⱼₖ`
  choose φ hφ using exists_linearMap_eq_ite (V := Ω[E⁄l]) h
  set δ : ι → Derivation l E E := fun k ↦ (φ k).compDer (D l E)
  -- `δ k` restricts to the coordinate derivation `dK k` on `K`
  have hA : ∀ k (c : K), Algebra.linearMap K E (dK k c) = δ k (algebraMap K E c) := by
    intro k
    have hlift : ((δ k).compAlgebraMap K).liftKaehlerDifferential =
        ((Algebra.linearMap K E).compDer (dK k)).liftKaehlerDifferential := by
      refine bK.ext fun j ↦ ?_
      rw [kaehlerBasis_apply, Derivation.liftKaehlerDifferential_comp_D,
        Derivation.liftKaehlerDifferential_comp_D]
      change φ k (D l E (x j)) = Algebra.linearMap K E (dK k (restrictFamily K x hxK j))
      rw [hφ k j, coordDerivation_gen]
      split_ifs <;> simp
    intro c
    have := congrArg (fun F : Ω[K⁄l] →ₗ[K] E ↦ F (D l K c)) hlift
    simp only [Derivation.liftKaehlerDifferential_comp_D] at this
    exact this.symm
  -- the minimal polynomial
  set f := minpoly K y
  have hint := hy.isIntegral
  have hirr : Irreducible f := minpoly.irreducible hint
  have hmonic : f.Monic := minpoly.monic hint
  by_contra hns
  have hder : Polynomial.derivative f = 0 := by
    by_contra hd
    exact hns ((Polynomial.separable_iff_derivative_ne_zero hirr).2 hd)
  -- all coefficients of `f` are killed by the `dK k`
  have hcoeff : ∀ k i, dK k (f.coeff i) = 0 := by
    intro k
    set g := PolynomialModule.equivPolynomial ((dK k).mapCoeffs f)
    have hgcoeff : ∀ i, g.coeff i = dK k (f.coeff i) := fun i ↦ rfl
    have hgy : Polynomial.aeval y g = 0 := by
      have := Derivation.apply_aeval_eq' (dK k) (δ k) (Algebra.linearMap K E) (hA k) y f
      rw [minpoly.aeval, map_zero, hder, map_zero, zero_smul, add_zero] at this
      rw [PolynomialModule.aeval_equivPolynomial, ← this]
    have hg : g = 0 := by
      by_contra hg0
      have h1 := minpoly.degree_le_of_ne_zero K y hg0 hgy
      have h2 : g.degree < f.natDegree := by
        rw [Polynomial.degree_lt_iff_coeff_zero]
        intro m hm
        rw [hgcoeff]
        rcases hm.lt_or_eq with hm | rfl
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hm, map_zero]
        · rw [hmonic.coeff_natDegree, Derivation.map_one_eq_zero]
      rw [Polynomial.degree_eq_natDegree hmonic.ne_zero] at h1
      exact absurd (h1.trans_lt h2) (lt_irrefl _)
    intro i
    rw [← hgcoeff, hg, Polynomial.coeff_zero]
  -- hence all coefficients of `f` are `p`-th powers
  have hpow : ∀ i, f.coeff i ∈ (frobenius K p).range := by
    intro i
    have hD : D l K (f.coeff i) = 0 :=
      (kaehler_D_eq_zero_iff_forall_coordDerivation hb' hsep' _).2 fun k ↦ hcoeff k i
    obtain ⟨e, he⟩ := exists_pow_eq_of_kaehler_D_eq_zero p hb' hsep' hD
    exact ⟨e, he⟩
  -- so `f` is a `p`-th power, contradicting irreducibility
  have hrange : Polynomial.contract p f ∈ (Polynomial.mapRingHom (frobenius K p)).range := by
    rw [Polynomial.mem_map_range]
    intro n
    rw [Polynomial.coeff_contract (Fact.out : p.Prime).ne_zero]
    exact hpow _
  obtain ⟨g, hg⟩ := hrange
  have hfg : f = g ^ p := calc
    f = Polynomial.expand K p (Polynomial.contract p f) :=
      (Polynomial.expand_contract p hder (Fact.out : p.Prime).ne_zero).symm
    _ = Polynomial.expand K p (Polynomial.map (frobenius K p) g) := by
      rw [← hg, Polynomial.coe_mapRingHom]
    _ = Polynomial.map (frobenius K p) (Polynomial.expand K p g) := Polynomial.map_expand.symm
    _ = g ^ p := Polynomial.map_frobenius_expand p g
  have hp1 : p - 1 + 1 = p := Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le
  have hfg' : f = g * g ^ (p - 1) := by rw [← pow_succ', hp1, hfg]
  rcases hirr.isUnit_or_isUnit hfg' with hu | hu
  · exact hirr.not_isUnit (hfg ▸ hu.pow p)
  · have hp0 : p - 1 ≠ 0 := by have := (Fact.out : p.Prime).two_le; omega
    exact hirr.not_isUnit (hfg ▸ ((isUnit_pow_iff hp0).1 hu).pow p)

end SepCrit

/-- **Separability criterion** (replacing blueprint Lemma 3.1(c)): over a perfect field `l`, if
the differentials `d xᵢ` are linearly independent in `Ω[E⁄l]` and `y` is algebraic over `l(x)`,
then `y` is separable over `l(x)`. -/
theorem isSeparable_adjoin_of_linearIndependent_kaehler_D [PerfectField l] {ι : Type*}
    {x : ι → E} (h : LinearIndependent E fun i ↦ D l E (x i)) {y : E}
    (hy : IsAlgebraic (adjoin l (Set.range x)) y) : IsSeparable (adjoin l (Set.range x)) y := by
  obtain ⟨q, hq⟩ := ExpChar.exists l
  rcases hq with _ | ⟨hp⟩
  · have : CharZero (adjoin l (Set.range x)) :=
      charZero_of_injective_algebraMap (algebraMap l _).injective
    exact (minpoly.irreducible hy.isIntegral).separable
  · have : Fact q.Prime := ⟨hp⟩
    exact SepCrit.isSeparable q h hy

end MilnorAlgDep
