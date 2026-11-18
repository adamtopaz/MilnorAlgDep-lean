# MilnorAlgDep — agent guide

Lean 4 / Mathlib formalization of `blueprint/milnor-k-fields.tex` ("Steinberg-compatible
homomorphisms of multiplicative groups and the reconstruction of fields from Milnor K-theory").
Read `PLAN.md` first: it has the architecture, the work packages and their status.

GitHub: `adamtopaz/MilnorAlgDep-lean` (remote `origin`, default branch `main`).

## Working in a worktree

Work-package agents run in their own git worktree. First thing, from the worktree root:

```bash
git fetch origin && git checkout -b <your-branch> origin/main   # branch name given in your brief
/home/adam/projects/autoformalization/MilnorAlgDep/scripts/setup-worktree.sh
```

The script symlinks `.lake/packages` to the main checkout so Mathlib is never downloaded or
rebuilt. Never run `lake update`, `lake exe cache get`, or `lake clean`, and never edit
`lakefile.toml`, `lake-manifest.json` or `lean-toolchain` unless your brief says so.
If a build starts compiling Mathlib files, stop it immediately and report.

## Building

- `lake build MilnorAlgDep.Foo.Bar` builds one module and its imports. Use this while iterating.
- `lake build` builds every file under `MilnorAlgDep/` (the library uses a glob). Run it before
  every push.
- Run at most one `lake` command at a time; the machine is shared with other agents.
- Do not edit `MilnorAlgDep.lean` (the root import file); the supervisor regenerates it.
- Prefer narrow imports (`import Mathlib.RingTheory.Kaehler.Basic`, ...) over `import Mathlib`
  once a file is stable. `import Mathlib` is fine while exploring.
- Mathlib source is in `.lake/packages/mathlib/Mathlib/`; grep it before proving a standard
  fact from scratch. `#loogle` and `#leansearch` work (network is available).

## Rules

1. **No cheating.** No `axiom`, no `native_decide`, no `sorry` hidden behind `opaque`/`unsafe`,
   no weakening a statement to make it provable, no changing a hypothesis so the conclusion
   becomes vacuous. `sorry` is allowed only as an explicit, documented placeholder, and each one
   must be listed in the PR description.
2. **Frozen statements.** The statements of the main theorems and the definitions they mention
   (listed in `PLAN.md` under "Frozen interface") may not be changed without the supervisor's
   approval. If you think one is wrong or awkward, say so in your report with a concrete
   proposal. Internal lemmas are yours to restate, split or reorganize.
3. **The blueprint is an unrefereed draft.** Its proofs are a guide, not a script: any correct
   proof is fine, and a different route is welcome when it is easier in Lean. If a blueprint
   statement looks false, or a proof step has a gap you cannot close, stop and report it
   precisely (what fails, a counterexample if you have one, what would repair it). Do not paper
   over it.
4. **Stay in scope.** Touch only the files your brief assigns. If you need a lemma that belongs
   to another package, put it in your own file under a `-- TODO(move)` comment and mention it
   in the report.
5. **Commit often**, push to your branch, and open a PR against `main` when the brief's
   acceptance criteria are met (or when you are stopping with partial progress: say so in the
   PR title with `[WIP]`). PR description: what was done, what was changed relative to the
   blueprint and why, and the list of remaining `sorry`s. Do not merge PRs yourself.
6. **Report faithfully.** Your final message is read by the supervisor only. State what
   compiles, what does not, and what is still `sorry`. Give the PR URL.

## Style

- Namespace `MilnorAlgDep`. Mathlib naming conventions and style (100-column lines,
  `fun x ↦ _`, `theorem foo_bar`, structure fields in `camelCase`).
- Every file starts with a module docstring saying which part of the blueprint it formalizes;
  every definition and every theorem corresponding to a numbered blueprint statement gets a
  docstring that names it (for example "Blueprint Lemma 4.5 (Trichotomy)"). The Verso
  companion text links to these.
- Keep proofs readable: name intermediate facts, avoid 200-line tactic blocks, split lemmas.
- No `set_option maxHeartbeats` above 400000 without a comment explaining why.
- Commit messages end with: `Co-Authored-By: Claude <noreply@anthropic.com>`
- PR descriptions end with: `🤖 Generated with [Claude Code](https://claude.com/claude-code)`
