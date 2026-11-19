# MilnorAlgDep

A Lean 4 / Mathlib formalization of

> *Steinberg-compatible homomorphisms of multiplicative groups and the reconstruction of
> fields from Milnor K-theory* (working draft, `blueprint/milnor-k-fields.tex`).

Status: **complete**. The library `MilnorAlgDep/` contains no `sorry`, and the main theorems
depend only on the standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

Theorem A: a homomorphism `ψ : Kˣ → (Lˣ/lˣ) ⊗ ℚ` which is injective modulo constants, sends `x`
and `1 - x` to algebraically dependent classes, and has enough algebraically independent values,
is a rational multiple of the map induced by a field embedding of `K` into the perfect closure of
`L`. Consequently homomorphisms of rational Milnor K-rings that are injective in degree one come
from field embeddings (Theorems B, C, D).

All statements are in the namespace `MilnorAlgDep`:

| Blueprint | Lean | File |
|-----------|------|------|
| Theorem A, `L` perfect | `theoremA_perfect` | `MilnorAlgDep/TheoremA.lean` |
| Theorem A, any `L` | `theoremA` | `MilnorAlgDep/TheoremA.lean` |
| Theorem A, uniqueness (Lemma 6.13) | `theoremA_perfect_unique`, `theoremA_unique` | `MilnorAlgDep/TheoremA.lean` |
| Converse of Theorem A | `theoremA_converse`, `theoremA_converse_perfectClosure` | `MilnorAlgDep/Converse.lean` |
| Hypotheses of Theorem A are satisfiable | `theoremA_perfect_hypotheses`, `theoremA_perfect_hypotheses_ratFunc` | `MilnorAlgDep/Converse.lean` |
| Theorem B (relative) | `theoremB`, `theoremB_unique` | `MilnorAlgDep/Milnor/TheoremB.lean` |
| Theorem C (absolute) | `theoremC`, `theoremC_unique` | `MilnorAlgDep/Milnor/TheoremC.lean` |
| Theorem D (isomorphisms) | `theoremD` | `MilnorAlgDep/Milnor/TheoremD.lean` |
| `ℚ ⊗ K^M_*(L) ≅ 𝒦_*(L)`, and `𝒦_*(L\|l)` as a quotient of `𝒦_*(L)` | `MilnorK.ratEquiv`, `MilnorKQ.relQuotEquiv` | `MilnorAlgDep/Milnor/Comparison/` |

The encodings (the group `V l L`, algebraic independence `VAlgIndep`, the rational Milnor ring
`MilnorKQ`, perfect closures) are explained in the module docstrings of these files and in the
companion text. The rational Milnor rings are defined by generators and relations; the last row
of the table relates them to the blueprint's definitions.

The blueprint is an unrefereed draft. The formalization found no error in it; the places where
the formal proofs differ from the blueprint's (mostly simplifications) are listed in Chapter 9 of
the companion text.

## Building

The toolchain is pinned in `lean-toolchain`. With [elan](https://github.com/leanprover/elan)
installed:

```bash
lake exe cache get   # download the Mathlib build cache
lake build           # builds every file under MilnorAlgDep/
```

## Checking the axioms

Compile a scratch file such as

```lean
import MilnorAlgDep

#print axioms MilnorAlgDep.theoremA
#print axioms MilnorAlgDep.theoremA_perfect
#print axioms MilnorAlgDep.theoremA_perfect_unique
#print axioms MilnorAlgDep.theoremA_unique
#print axioms MilnorAlgDep.theoremB
#print axioms MilnorAlgDep.theoremC
#print axioms MilnorAlgDep.theoremD
```

with `lake env lean -DmaxSynthPendingDepth=3 Scratch.lean`. Each line should report
`[propext, Classical.choice, Quot.sound]`.

## More

- Companion text (Verso): https://adamtopaz.github.io/MilnorAlgDep-lean/, an exposition of the
  blueprint in which each numbered statement is followed by its Lean counterpart. Source in
  `site/`; build with `site/build.sh` (see `site/README.md`).
- `PLAN.md`: architecture, work packages, and the log of decisions and deviations from the
  blueprint.
- `CLAUDE.md`: conventions for the agents that did the formalization.
