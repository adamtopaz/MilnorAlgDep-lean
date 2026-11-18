# MilnorAlgDep

A Lean 4 / Mathlib formalization of

> *Steinberg-compatible homomorphisms of multiplicative groups and the reconstruction of
> fields from Milnor K-theory* (working draft, `blueprint/milnor-k-fields.tex`).

The main results: a homomorphism `ψ : Kˣ → (Lˣ/lˣ) ⊗ ℚ` which is injective modulo constants,
sends `x` and `1 - x` to algebraically dependent classes, and has enough algebraically
independent values, is a rational multiple of the map induced by a field embedding of `K` into
the perfect closure of `L` (Theorem A). Consequently homomorphisms of rational Milnor K-rings
that are injective in degree one come from field embeddings (Theorems B, C, D).

- `PLAN.md` — architecture, work packages and status.
- `CLAUDE.md` — conventions for the agents doing the formalization.
- Companion text (Verso): https://adamtopaz.github.io/MilnorAlgDep-lean/, source in `site/`
  (build with `site/build.sh`; see `site/README.md`).

Status: in progress.
