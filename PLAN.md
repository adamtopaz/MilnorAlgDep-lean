# Formalization plan

Source: `blueprint/milnor-k-fields.tex`. Section and lemma numbers below refer to it.
Goal: Theorems A, B, C, D in Lean 4 with Mathlib, no `sorry`, no extra axioms, plus a Verso
companion text published on GitHub Pages.

This file is the shared source of truth. The supervisor keeps the status table current.

## Architecture

### Strategy

1. **Theorem A is proved separately in characteristic 0 and characteristic p.** The blueprint
   is written uniformly (`Γ = 0` or `ℤ`, `L_A = L` in characteristic 0), but in Lean the
   uniform treatment would force `p = 1` case splits through the whole theory of levels.
   So: Sections 3–5 and Step A (6.2) are formalized for `p` prime only, and the characteristic
   0 proof uses `Ω[L⁄l]` directly. The final `theoremA` is a case split on `ringChar L`.
2. **Step B is abstract.** Lemmas 6.6–6.8 and Proposition 6.9 only use: a field `K₀`, a field
   `F`, an `F`-vector space `Ω`, and a homomorphism `Δ : K₀ˣ → Ω` with three properties. This is
   proved once (`StepB/Abstract.lean`) and used by both characteristics.
3. **Milnor K-theory is defined rationally and relatively in one go.** `𝒦(L|l)` is the
   quotient of the tensor algebra over `ℚ` of `V_{L|l}` by the Steinberg relations
   `[a] ⊗ [1 - a]`; the absolute ring `𝒦(L)` is the same construction with `L^× ⊗ ℚ`.
   (This is canonically isomorphic to the blueprint's `ℚ ⊗ K^M_*(L)` modulo the ideal generated
   by `l^×`; proving that comparison is a stretch goal, not on the critical path.)
4. **Theorems B, C, D are proved from the statement of Theorem A**, in parallel with its proof.

### Module map

```
MilnorAlgDep/
  Foundations/          setting l ⊆ L, the group V_{L|l}, classes [a], (V1)-(V3),
                        points Q_a, algebraic (in)dependence in V            (Section 2.1-2.3)
  Standard/             (S1)-(S3), Lemma 2.2 (eigenvalue lemma), Lemma 3.1   (Sections 2.4, 3)
  StepB/Abstract.lean   abstract Step B: Lemmas 6.6-6.8, Prop 6.9
  Char0/                Theorem A when char L = 0
  CharP/
    Levels.lean         Lemma 3.2, levels, normalized triples, Lemma 3.5
    Models.lean         Section 4: models, Lemmas 4.2-4.6
    Quadrangle.lean     Lemma 5.1
    StepA.lean          Section 6.1-6.2: eq (sum), gauge, cocycle, Prop 6.1
    AdaptedModel.lean   Section 6.3: W, dlog_A, K₀, Lemmas 6.4, 6.5
    StepC.lean          Section 6.6: Lemmas 6.10, 6.11, Prop 6.12
    Main.lean           reduction to perfect fields, end of proof (6.7)
  Uniqueness.lean       Lemma 6.13
  TheoremA.lean         statement and final assembly of Theorem A
  Milnor/
    Defs.lean           𝒦(L|l), 𝒦(L), grading, degree one, functoriality, r^deg
    Tame.lean           Lemma 7.1 (tame symbol), extension of valuations
    Symbols.lean        Lemma 7.2
    TheoremB.lean, TheoremC.lean, TheoremD.lean
docs site (Verso)       see WP-V
```

### Frozen interface

Once WP0 is merged, the following may only change with the supervisor's approval:

- the definitions in `Foundations/` that the main theorems mention
  (`V`, the class map `[·]`, algebraic independence in `V`);
- the definition of the rational Milnor ring and its grading in `Milnor/Defs.lean`;
- the statements `theoremA`, `theoremA_perfect`, `theoremB`, `theoremC`, `theoremD`.

### Design notes

- Internal theory is developed for `(l L : Type*) [Field l] [Field L] [Algebra l L]`, so that
  Mathlib's `AlgebraicIndependent l`, `IsSeparable l`, `IntermediateField l L`, `Ω[L⁄l]` apply
  directly. The top-level theorems take `l : Subfield L` and `k : Subfield K`.
- "Relatively algebraically closed" is spelled out in top-level statements
  (`∀ x : L, IsAlgebraic l x → x ∈ l`).
- `V_{L|l}` is an additive `ℚ`-vector space. The homomorphism `ψ` is `Additive Kˣ →+ V`
  (or an equivalent bundling chosen in WP0 and then used everywhere).
- Perfect closures: `theoremA_perfect` assumes `L` perfect and produces `τ : K →+* L`.
  `theoremA` is for arbitrary `L` and produces `τ` into a perfect closure of `L`.
- Characteristic p code uses `(p : ℕ) [Fact p.Prime] [CharP L p]` and `Γ = ℤ`.

## Work packages

Status: `todo`, `active`, `review`, `done`.

| WP | Content | Depends on | Status |
|----|---------|------------|--------|
| WP0 | Foundations + frozen statements (with `sorry`) | — | done |
| WP-B | Abstract Step B | — | done |
| WP-S | Standard facts: S1–S3, Lemma 2.2, Lemma 3.1 | — | done |
| WP-V1 | Verso site infrastructure + GitHub Pages | — | done |
| WP-R | Eigenvalue lemma (Lemma 2.2), `Standard/Eigenvalue.lean` | — | done |
| WP-K0 | Existence of valuations, `Milnor/ValuationExt.lean` | — | done |
| WP-K1 | `Milnor/Defs`: grading, degree one, functoriality | WP0 | done |
| WP-K2 | Tame symbol, Lemma 7.2 | WP-K1 | done |
| WP-K3 | Theorems B, C, D from Theorem A | WP-K2 | active |
| WP-U | Uniqueness, Lemma 6.13 | WP0 | done |
| WP-A0 | Theorem A in characteristic 0 | WP0, WP-B, WP-S | done |
| WP-P1 | Levels and normalized triples (Section 3) | WP0, WP-S | active |
| WP-P2 | Models (Section 4) | WP-P1 | todo |
| WP-P3 | Quadrangle (Section 5) | WP-P2 | todo |
| WP-P4 | Step A (6.1–6.2) | WP-P3 | todo |
| WP-P5 | Adapted model (6.3) | WP-P2, WP-P4 | todo |
| WP-P6 | Step C in characteristic p (6.6) | WP-P5, WP-B | todo |
| WP-P7 | Reduction to perfect fields, assembly of Theorem A | WP-P6, WP-A0, WP-U | done |
| WP-V2 | Verso companion text | all | todo |
| WP-Z | Final audit: no `sorry`, `#print axioms`, statement review | all | todo |

### Stub files and wiring (supervisor)

`TheoremA.lean` is frozen and only forwards to:

- `Reduction.lean`: `theoremA_perfect_aux` (from the two cases below), `theoremA_aux` (WP-P7);
- `Uniqueness.lean`: `theoremA_perfect_unique_aux` (WP-U);
- `Char0/Main.lean`: `theoremA_perfect_of_charZero` (WP-A0);
- `CharP/Main.lean`: `theoremA_core_charP`, for perfect `K`, `L` (WP-P6);
- `Milnor/Symbols.lean`: Lemma 7.2 (WP-K2).

The statements in these stub files are frozen too.

## Log

- 2026-11-18: all files use the Lean module system (see `CLAUDE.md`).
- 2026-11-18: WP-S proves (S3)(b) via the perfect core instead of a discrete valuation, and
  Lemma 4.6 for arbitrary families over a perfect field. WP-R proves Lemma 2.2 from the minimal
  polynomial, without Gauss's lemma. WP-B needed no hypothesis beyond (H0)-(H3).

(The supervisor records decisions, deviations from the blueprint and discovered gaps here.)
- 2026-11-18: Theorem A is proved when `char L = 0`; uniqueness (Lemma 6.13), the reductions,
  Lemmas 7.1 and 7.2 and the `GradedAlgebra` instance are proved. Remaining `sorry`s:
  `CharP/Main.lean` (the characteristic p core) and Theorems B, C, D (WP-K3 in progress).
- Possible strengthening for the final audit: drop `hφsymm` from `theoremD` (redundant given
  `MilnorKQ.gradedAlgebra`), and note that Lemma 7.2(a) does not use `IsRelAlgClosed`.
