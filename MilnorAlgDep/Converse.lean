module

public import MilnorAlgDep.Milnor.PrimeField
public import MilnorAlgDep.TheoremA
public import Mathlib.FieldTheory.PrimeField
public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# The converse of Theorem A, and non-vacuity of its hypotheses

Blueprint, Section 1.1, the sentence after Theorem A: "Conversely, every pair `(τ, r)` as in the
theorem defines a homomorphism `ψ = r[τ]` satisfying (A1) and (A2)."

The encodings of (A1)–(A4) are exactly those of `theoremA_perfect` (see `MilnorAlgDep.TheoremA`).

## Main statements

* `theoremA_converse`: for a field embedding `τ : K → L`, `l ⊆ L` relatively algebraically closed
  and `r ∈ ℚ^×`, the homomorphism `ψ = r[τ] : Kˣ → V_{L|l}` satisfies (A1) with `k = τ⁻¹(l)`, and
  (A2).
* `theoremA_converse_perfectClosure`: the same for the conclusion of `theoremA` (arbitrary `L`,
  `τ : K → L^i`, `ψ(x) = r[τ x]` after the comparison map `V_{L|l} → V_{L^i|l^i}`).
* `theoremA_perfect_hypotheses`: non-vacuity. If the perfect field `L` contains `d` elements
  algebraically independent over the relatively algebraically closed subfield `l` (`d` as in
  (A3)), then `K = L`, `k = l`, `ψ = [·]` satisfy all hypotheses of `theoremA_perfect`; the
  conclusion is literally their conjunction (`theoremA_perfect_of_hypotheses` feeds it to
  `theoremA_perfect`).
* `theoremA_perfect_hypotheses_ratFunc`: an explicit case, `L = ℚ(X₀, X₁)` (the fraction field of
  `MvPolynomial (Fin 2) ℚ`) and `l` the algebraic closure of `ℚ` in `L`, so that the hypotheses of
  `theoremA_perfect` are jointly satisfiable unconditionally.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

variable {K L : Type*} [Field K] [Field L]

/-- If `x + y = 1` in `L`, then `[x], [y]` are algebraically dependent over any `l`: `y = 1 - x`
is algebraic over `l(x)`. -/
theorem not_vAlgIndep_cls_of_add_eq_one {l : Type*} [Field l] [Algebra l L] {x y : Lˣ}
    (hxy : (x : L) + y = 1) :
    ¬ VAlgIndep l ![cls (constUnits l L) (.ofMul x), cls (constUnits l L) (.ofMul y)] := by
  have hv : ![cls (constUnits l L) (.ofMul x), cls (constUnits l L) (.ofMul y)] =
      fun i ↦ cls (constUnits l L) (.ofMul (![x, y] i)) := by
    ext i
    fin_cases i <;> rfl
  rw [hv, VAlgIndep.cls_iff]
  intro h
  have h' : AlgebraicIndependent l ![(x : L), (y : L)] := by
    convert h using 1
    ext i
    fin_cases i <;> rfl
  refine (algebraicIndependent_pair_iff.1 h').2 ?_
  have hy : (y : L) = 1 - x := eq_sub_of_add_eq' hxy
  rw [hy]
  exact (isAlgebraic_one.sub
    (isAlgebraic_algebraMap (⟨x, IntermediateField.mem_adjoin_simple_self l (x : L)⟩ :
      IntermediateField.adjoin l {(x : L)})))

/-- **Blueprint, converse of Theorem A** (Section 1.1, after Theorem A). Let `l ⊆ L` be a
relatively algebraically closed subfield, `τ : K → L` a field embedding and `r ∈ ℚ`, `r ≠ 0`.
Then every homomorphism `ψ : Kˣ → V_{L|l}` with `ψ(x) = r • [τ x]` for all `x` (for instance
`r • (cls _).comp (Units.map τ).toAdditive`) satisfies (A1) with `k = τ⁻¹(l)` and (A2), encoded as
in `theoremA_perfect`. (In (A2) the hypothesis `x ∉ k` is not needed.) -/
theorem theoremA_converse (l : Subfield L) (hl : ∀ x : L, IsAlgebraic l x → x ∈ l)
    (τ : K →+* L) (r : ℚ) (hr : r ≠ 0) (ψ : Additive Kˣ →+ V l L)
    (hψ : ∀ x : Kˣ, ψ (.ofMul x) = r • 〚Units.map (τ : K →* L) x〛) :
    (∀ x : Kˣ, ψ (.ofMul x) = 0 ↔ (x : K) ∈ l.comap τ) ∧
      (∀ x y : Kˣ, (x : K) + y = 1 → (x : K) ∉ l.comap τ →
        ¬ VAlgIndep l ![ψ (.ofMul x), ψ (.ofMul y)]) := by
  have : IsRelAlgClosed l L := IsRelAlgClosed.of_subfield hl
  refine ⟨fun x ↦ ?_, fun x y hxy _ ↦ ?_⟩
  · rw [hψ, smul_eq_zero, or_iff_right hr, V.cls_eq_zero_iff, mem_constUnits_subfield,
      Subfield.mem_comap]
    rfl
  · have hv : ![ψ (.ofMul x), ψ (.ofMul y)] = fun i ↦ (fun _ ↦ r) i •
        ![cls (constUnits l L) (.ofMul (Units.map (τ : K →* L) x)),
          cls (constUnits l L) (.ofMul (Units.map (τ : K →* L) y))] i := by
      ext i
      fin_cases i
      · exact hψ x
      · exact hψ y
    rw [hv, VAlgIndep.smul_iff fun _ ↦ hr]
    refine not_vAlgIndep_cls_of_add_eq_one ?_
    simp only [Units.coe_map, MonoidHom.coe_ofClass]
    rw [← map_add, hxy, map_one]

/-- **Blueprint, converse of Theorem A**, for arbitrary `L`, in the form of the conclusion of
`theoremA`: let `M` be a perfect closure of `L`, `l^i = perfectClosureIn l M p`, `τ : K → M` a
field embedding and `r ≠ 0`. If `ψ : Kˣ → V_{L|l}` satisfies `ψ(x) = r • [τ x]` after the
comparison map `V.toPerfectClosure : V_{L|l} → V_{M|l^i}`, then `ψ` satisfies (A1) with
`k = τ⁻¹(l^i)` and (A2). -/
theorem theoremA_converse_perfectClosure (l : Subfield L) (hl : ∀ x : L, IsAlgebraic l x → x ∈ l)
    (p : ℕ) (M : Type*) [Field M] [Algebra L M] [ExpChar M p] [PerfectRing M p]
    [IsPerfectClosure (algebraMap L M) p] (τ : K →+* M) (r : ℚ) (hr : r ≠ 0)
    (ψ : Additive Kˣ →+ V l L)
    (hψ : ∀ x : Kˣ, V.toPerfectClosure l M p (ψ (.ofMul x)) = r • 〚Units.map (τ : K →* M) x〛) :
    (∀ x : Kˣ, ψ (.ofMul x) = 0 ↔ (x : K) ∈ (perfectClosureIn l M p).comap τ) ∧
      (∀ x y : Kˣ, (x : K) + y = 1 → (x : K) ∉ (perfectClosureIn l M p).comap τ →
        ¬ VAlgIndep l ![ψ (.ofMul x), ψ (.ofMul y)]) := by
  let ψ' := (V.toPerfectClosure l M p).toAddMonoidHom.comp ψ
  obtain ⟨A1, A2⟩ := theoremA_converse (perfectClosureIn l M p)
    (perfectClosureIn_isRelAlgClosed l M p hl) τ r hr ψ' hψ
  have hinj := (V.toPerfectClosure_bijective l M p).1
  refine ⟨fun x ↦ ?_, fun x y hxy hx ↦ ?_⟩
  · rw [← A1 x]
    exact (map_eq_zero_iff _ hinj).symm
  · rw [← V.vAlgIndep_toPerfectClosure_iff l M p]
    have hv : (fun i ↦ V.toPerfectClosure l M p (![ψ (.ofMul x), ψ (.ofMul y)] i)) =
        ![ψ' (.ofMul x), ψ' (.ofMul y)] := by
      ext i
      fin_cases i <;> rfl
    rw [hv]
    exact A2 x y hxy hx

/-- **Non-vacuity of Theorem A.** Let `L` be a perfect field, `l ⊆ L` a relatively algebraically
closed subfield, and assume that `L` contains `d` elements algebraically independent over `l`,
with `d = 2` if `char L = 0` and `d = 3` otherwise (as in (A3)). Then `K = L`, `k = l` and the
class map `ψ = [·] : Lˣ → V_{L|l}` satisfy all hypotheses of `theoremA_perfect`: the conclusion is
literally the conjunction of `[PerfectField L]`, `hl`, (A1), (A2), (A3), (A4) for these data
(`theoremA_perfect_of_hypotheses` applies `theoremA_perfect` to it). -/
theorem theoremA_perfect_hypotheses [PerfectField L] (l : Subfield L)
    (hl : ∀ x : L, IsAlgebraic l x → x ∈ l)
    (hd : ∃ y : Fin (if ringChar L = 0 then 2 else 3) → L, AlgebraicIndependent l y) :
    PerfectField L ∧ (∀ x : L, IsAlgebraic l x → x ∈ l) ∧
      (∀ x : Lˣ, cls (constUnits l L) (.ofMul x) = 0 ↔ (x : L) ∈ l) ∧
      (∀ x y : Lˣ, (x : L) + y = 1 → (x : L) ∉ l →
        ¬ VAlgIndep l ![cls (constUnits l L) (.ofMul x), cls (constUnits l L) (.ofMul y)]) ∧
      (∃ x : Fin (if ringChar L = 0 then 2 else 3) → Lˣ,
        VAlgIndep l fun i ↦ cls (constUnits l L) (.ofMul (x i))) ∧
      (ringChar L ≠ 0 → ringChar L ≠ 0) := by
  have : IsRelAlgClosed l L := IsRelAlgClosed.of_subfield hl
  obtain ⟨y, hy⟩ := hd
  refine ⟨inferInstance, hl, fun x ↦ ?_, fun x y hxy _ ↦ not_vAlgIndep_cls_of_add_eq_one hxy,
    ⟨fun i ↦ Units.mk0 (y i) (hy.ne_zero i), VAlgIndep.cls_iff.2 hy⟩, id⟩
  rw [V.cls_eq_zero_iff, mem_constUnits_subfield]

/-- The hypotheses produced by `theoremA_perfect_hypotheses` are accepted by `theoremA_perfect`
(here `K = L`, `k = l`, `ψ = [·]`, and the conclusion is that of `theoremA_perfect`). -/
theorem theoremA_perfect_of_hypotheses [PerfectField L] (l : Subfield L)
    (hl : ∀ x : L, IsAlgebraic l x → x ∈ l)
    (hd : ∃ y : Fin (if ringChar L = 0 then 2 else 3) → L, AlgebraicIndependent l y) :
    ringChar L = ringChar L ∧ (∀ x : L, IsAlgebraic l x → x ∈ l) ∧
      ∃ (τ : L →+* L) (r : ℚ), r ≠ 0 ∧ (∀ x : L, τ x ∈ l ↔ x ∈ l) ∧
        ∀ x : Lˣ, cls (constUnits l L) (.ofMul x) = r • 〚Units.map (τ : L →* L) x〛 := by
  obtain ⟨-, hl, A1, A2, A3, A4⟩ := theoremA_perfect_hypotheses l hl hd
  exact theoremA_perfect l l hl (cls (constUnits l L)) A1 A2 A3 A4

/-- An explicit case of `theoremA_perfect_hypotheses`: `L = ℚ(X₀, X₁)`, the fraction field of
`MvPolynomial (Fin 2) ℚ`, with `l` the algebraic closure of `ℚ` in `L` (`primeAlgClosure L`).
So the hypotheses of `theoremA_perfect` are jointly satisfiable. -/
theorem theoremA_perfect_hypotheses_ratFunc :
    let L := FractionRing (MvPolynomial (Fin 2) ℚ)
    let l := primeAlgClosure L
    PerfectField L ∧ (∀ x : L, IsAlgebraic l x → x ∈ l) ∧
      (∀ x : Lˣ, cls (constUnits l L) (.ofMul x) = 0 ↔ (x : L) ∈ l) ∧
      (∀ x y : Lˣ, (x : L) + y = 1 → (x : L) ∉ l →
        ¬ VAlgIndep l ![cls (constUnits l L) (.ofMul x), cls (constUnits l L) (.ofMul y)]) ∧
      (∃ x : Fin (if ringChar L = 0 then 2 else 3) → Lˣ,
        VAlgIndep l fun i ↦ cls (constUnits l L) (.ofMul (x i))) ∧
      (ringChar L ≠ 0 → ringChar L ≠ 0) := by
  intro L l
  have hX : AlgebraicIndependent ℚ (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) ℚ) :=
    MvPolynomial.algebraicIndependent_X (Fin 2) ℚ
  -- the variables are algebraically independent over the prime field `⊥ ≅ ℚ` of `L`
  have hbot : AlgebraicIndependent (⊥ : Subfield L)
      (algebraMap (MvPolynomial (Fin 2) ℚ) L ∘ MvPolynomial.X) :=
    (algebraicIndependent_ringHom_iff_of_comp_eq (Subfield.botEquivRat (K := L)).symm
      (algebraMap (MvPolynomial (Fin 2) ℚ) L) (IsFractionRing.injective _ _)
      (Subsingleton.elim _ _)).2 hX
  have hchar : ringChar L = 0 := ringChar.eq_zero
  refine theoremA_perfect_hypotheses _ isRelAlgClosed_primeAlgClosure ?_
  rw [hchar, ite_eq_left rfl]
  exact ⟨_, (algebraicIndependent_bot_iff fun _ ↦ mem_primeAlgClosure).1 hbot⟩

end MilnorAlgDep
