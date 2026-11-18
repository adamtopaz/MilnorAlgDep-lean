import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite

set_option pp.rawOnError true

#doc (Manual) "The formalization" =>
%%%
tag := "sec:formalization"
%%%

The Lean development lives in the library `MilnorAlgDep` of the
[repository](https://github.com/adamtopaz/MilnorAlgDep-lean), on top of Mathlib.
Its goal is Theorems A–D with no `sorry` and no axioms beyond the standard ones.
This chapter describes how it is organized, how to read its statements, and where it deviates
from the blueprint.

# Organization

The modules follow the structure of the proof:

```
MilnorAlgDep/
  Foundations/         the group V, classes [a], (V1)-(V3), points    Chapter 2
  Standard/            (S1)-(S3), eigenvalue lemma, Lemma 3.1         Chapters 2, 3
  StepB/Abstract.lean  Step B for an abstract Δ : K₀ˣ → Ω             Section 6.4
  Char0/               Theorem A in characteristic 0
  CharP/               levels, models, quadrangle, Steps A and C       Chapters 3-6
  Uniqueness.lean      Lemma 6.13                                      Section 6.7
  TheoremA.lean        statement and assembly of Theorem A
  Milnor/              rational Milnor K-theory, tame symbols,
                       Theorems B, C, D                                Chapter 7
```

Every Lean declaration that formalizes a numbered statement of the blueprint has a docstring
naming it, such as "Blueprint Lemma 2.2 (Eigenvalue lemma)"; the text shows these declarations
with their signatures right after the informal statements, as in {cref "lem:R"}[].
Hovering over a name shows its type and documentation; clicking it jumps to its documentation.

# Reading the statements

* Internal results are stated for `(l L : Type*) [Field l] [Field L] [Algebra l L]`, so that
  Mathlib's notions ({name}`AlgebraicIndependent`, {name}`KaehlerDifferential`,
  {name}`PerfectClosure`, ...) apply directly; the main theorems take `l : Subfield L`.
* "Relatively algebraically closed" is spelled out: `∀ x : L, IsAlgebraic l x → x ∈ l`.
* $`V_{L|l}` is an additive $`\QQ`-vector space, and $`\psi` is an additive homomorphism
  `Additive Kˣ →+ V`.
* Valuations are Mathlib's valuation subrings, with multiplicative valuations: $`v(b) > 0`
  becomes `A.valuation b < 1`.
* Characteristic $`p` arguments use `(p : ℕ) [Fact p.Prime] [CharP L p]` and $`\Gamma = \ZZ`.

# Deviations from the blueprint

* *Theorem A is proved separately in characteristic 0 and in characteristic p.*
  The blueprint is uniform in the characteristic, at the price of a characteristic exponent
  $`p = 1` and $`\Gamma = 0` in characteristic $`0`; in Lean that would force case distinctions
  through the whole theory of levels.
  {ref "sec:levels"}[Chapters 3]–{ref "sec:quadrangle"}[5] and Step A are formalized for $`p`
  prime only, and the characteristic $`0` proof uses $`\Omega_{L|l}` directly.
* *Step B is abstract.* Lemmas 6.6–6.8 and Proposition 6.9 only use a field $`K_0`, a field
  $`F`, an $`F`-vector space $`\Omega` and a homomorphism $`\Delta \colon K_0^\times \to \Omega`
  with three properties; this is proved once and used in both characteristics.
* *Milnor K-theory is defined rationally and relatively in one go:* $`\Kr_*(L|l)` is the
  quotient of the tensor algebra over $`\QQ` of $`V_{L|l}` by the Steinberg relations.
  The comparison with the blueprint's $`\QQ \otimes \KM_*(L)` modulo $`l^\times` is not on the
  critical path.
* Theorem A is stated twice: `theoremA_perfect` for perfect $`L`, and `theoremA` for arbitrary
  $`L`, with $`\tau` taking values in a perfect closure of $`L`.

_Status (placeholder):_ the list of formalized statements, and of remaining `sorry`s, will be
kept here.
