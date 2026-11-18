# The companion text (Verso)

This directory holds the source of the companion text published at
<https://adamtopaz.github.io/MilnorAlgDep-lean/>: an exposition of
`blueprint/milnor-k-fields.tex` in which each numbered statement is followed by the Lean
declaration that formalizes it, rendered from the Lean sources (signature, docstring, hovers,
links). It is written in [Verso](https://github.com/leanprover/verso)'s `Manual` genre and pinned
to Verso `v4.36.0`, the tag that matches the project's Lean version.

## Build and preview

```bash
site/build.sh                                            # build and render (from any directory)
python3 -m http.server --directory site/_out/html-multi 8000   # then open http://localhost:8000
```

`build.sh` does the following:

1. `check-deps.py`: checks that the dependency pins agree with the root package (see below).
2. `lake build`: elaborates the document, including every `lean` block, `{docstring}` and
   `{name}`. This is where almost all errors are reported, with file and line.
3. `lake run versoMain SiteMain.lean --output _out`: renders HTML into `site/_out/html-multi`
   (about 3 seconds). Extra arguments to `build.sh` are passed on, e.g. `site/build.sh --verbose`.
4. `check-math.js`: renders every formula with the bundled KaTeX and fails on a TeX error (Verso
   does not report these; the browser would just show red text). Skipped if `node` is missing.
5. `check-links.py`: checks every internal link and anchor as served under `/MilnorAlgDep-lean/`.

The first build compiles Verso (about 2 minutes on the development machine, 32 cores); after
that a rebuild takes a few seconds plus the time to elaborate the chapters you changed.
Open the HTML through a web server, not as a file: hovers are fetched from a JSON file.

While writing, open the chapter file in VS Code with `site/` as the workspace folder; the
document is checked as you type, like any Lean file. The editor starts Lake too, so after pulling
changes to any `lake-manifest.json`, run `python3 site/check-deps.py` before opening site files.

Do not run `lake update` (or `lake exe cache get`) in `site/`; see "Updating dependencies".

## Layout

```
site/
  lakefile.toml, lake-manifest.json, lean-toolchain    the Lake package `MilnorAlgDepSite`
  SiteMain.lean               renders the document (run by `lake run versoMain`)
  MilnorAlgDepSite.lean       front page; includes the chapters in order
  MilnorAlgDepSite/Chapters/  one file per chapter (Introduction, ..., Formalization, References)
  MilnorAlgDepSite/Support/   Statements.lean  theorem/lemma environments, `cref`
                              Bibliography.lean references, cited as `Bib.BT`, `Bib.T`
                              Mathlib.lean      Mathlib files the text refers to
                              Config.lean       KaTeX macros, page layout, repository links
  build.sh, check-deps.py, check-math.js, check-links.py
```

### Why a separate package

`site/` is a Lake package of its own that requires the root package by path (`require
MilnorAlgDep from ".."`) and Verso from git. So `lake build` at the repository root never sees
Verso and stays exactly as fast as before.

The site package sets `packagesDir = "../.lake/packages"`: it uses the root's dependency checkout,
so Mathlib and its build cache are shared, never downloaded twice and never rebuilt. Verso and its
dependencies (`verso`, `subverso`, `MD4Lean`, `illuminate`) are cloned into the same directory
next to Mathlib; nothing else uses them. In a git worktree set up with
`scripts/setup-worktree.sh` this is the main checkout's `.lake/packages`, so Verso is also built
only once per machine. The `MilnorAlgDep` modules imported by the text are built into the root's
`.lake/build`, exactly as a root `lake build` would build them.

The price: Lake checks out every package at the revision recorded in `site/lake-manifest.json`.
If that disagreed with `../lake-manifest.json`, a site build would move the shared Mathlib
checkout and the next root build would rebuild Mathlib. `check-deps.py` refuses to continue in
that case. Run it (or `build.sh`) before any `lake` command in `site/`.

### Why `versoMain` and not `lake exe`

A Verso document is usually rendered by a `lean_exe`. Linking an executable that imports Mathlib
would compile all of the imported Mathlib C code (the Mathlib cache has no object files).
`lake run versoMain SiteMain.lean` runs `main` in the Lean interpreter instead. Verso itself is
precompiled (shared libraries), so rendering stays fast.

## Writing

### Adding a chapter

1. Create `MilnorAlgDepSite/Chapters/Foo.lean` with the same header as the other chapters:

   ```lean
   import VersoManual
   import MilnorAlgDepSite.Support
   import MilnorAlgDep

   open Verso.Genre Manual
   open Verso.Genre.Manual.InlineLean
   open MilnorAlgDepSite

   set_option pp.rawOnError true

   #doc (Manual) "Chapter title" =>
   %%%
   tag := "sec:foo"
   %%%

   Text...

   # A section

   More text...
   ```

2. Import it in `MilnorAlgDepSite.lean` and add `{include 1 MilnorAlgDepSite.Chapters.Foo}` at the
   right place. Chapters are numbered in include order; the blueprint's numbering is kept by
   keeping its order (Introduction is Chapter 1). `number := false` in the metadata makes a
   chapter unnumbered (see `References.lean`).

Inside a chapter, `#` starts a section (numbered 6.1, 6.2, ...) and `##` a subsection. Each
chapter is one HTML page (`htmlDepth := 1` in `Support/Config.lean`). Use one sentence per
line: it keeps diffs readable.

### Imports and the module system

The `MilnorAlgDep` library uses the Lean module system. Chapters are deliberately *not* modules:

* A non-module file that imports a module sees everything, including docstrings, transitively.
  So `import MilnorAlgDep` (once the root file imports all modules) gives every docstring.
* A module would only see docstrings of modules it imports with `import all M`, one by one;
  `import all` is not transitive.

Until the supervisor regenerates `MilnorAlgDep.lean`, a chapter must import the specific modules
it shows (`import MilnorAlgDep.Standard.Eigenvalue`, marked as redundant in a comment).

Never import Mathlib directly in a chapter: Mathlib warns about every non-module file that
imports it. Add the Mathlib file to `Support/Mathlib.lean` (a module) instead. The files in
`Support/` are modules.

### Mathematics

Inline math is `` $`x^2` ``, display math is `` $$`\sum_i x_i` ``, both rendered by KaTeX.
The blueprint's macros (`\QQ`, `\ZZ`, `\FF`, `\Frob`, `\lev`, `\lt`, `\hgt`, `\rk`, `\trdeg`,
`\dlog`, `\chr`, `\sm`, `\la`, `\ra`, `\KM`, `\Kr`, ...) are defined, so formulas can be copied from
the `.tex` file; add more in `Support/Config.lean`. As in the blueprint, `\lt` is the level
triple, not `<`. Math can contain anything except a backtick.

Never write `_` or `*` outside math: they are emphasis and bold in Verso (`_emph_`, `*bold*`).

### Statements

```
:::thm "A" (tag := "thm:A")
Let $`K` and $`L` be fields ...
:::

:::lem "4.6" (title := "Trichotomy") (tag := "lem:trichotomy")
Let $`P, Q, R` be distinct collinear points ...
:::
```

Environments: `thm`, `prop`, `lem`, `cor`, `defn`, `rmk`, `ex` (all take a label, and optionally
`title` and `tag`) and `proof` (no arguments). The label is the blueprint's number; use the
blueprint's `\label` as the tag. (`:::lemma` is not available: `lemma` is already a Mathlib name.)
A directive nested inside another needs more colons on the outer one (`::::thm` ... `::::`).

### Cross-references

* `{cref "lem:trichotomy"}[]` renders "Lemma 4.6" as a link, on any page. It also works for
  chapter and section tags: `{cref "sec:stepA"}[]` renders "Section 6.2". With text,
  `{cref "lem:trichotomy"}[the trichotomy]`.
* `{ref "sec:levels"}[Chapters 3–5]` links to a tagged chapter or section with the given text.
  The text is required: `{ref "x"}[]` renders an empty, invisible link.
* Tags are set with `%%% tag := "sec:foo" %%%` right after a heading. Statement and section tags
  share one namespace. Unknown tags are errors.

### The pattern: informal statement, then Lean

Every numbered statement is followed by its formal counterpart. Chapter 2 (Lemma 2.2) and
Chapter 7 (the standard fact on valuations) show the pattern with real declarations:

```
:::lem "2.2" (title := "Eigenvalue lemma") (tag := "lem:R")
Let $`E \supset l` be fields, ...
:::

{docstring MilnorAlgDep.eigenvalue_mem_primeField}

In Lean the prime field is `⊥`, so {name}`MilnorAlgDep.eigenvalue_mem_primeField` concludes ...
```

* `{docstring Name}` renders the signature and the docstring of a declaration, with hovers. The
  declaration must have a docstring, and its module must be imported. Options:
  `{docstring Name (allowMissing := true)}`, `(hideFields := true)`,
  `(hideStructureConstructor := true)`, `(label := "lemma")`.
* `` {name}`Name` `` is an inline reference with a hover; it links to the `{docstring}` block of
  that name if there is one in the document. For a name that is not in scope, or to show a
  shorter text: `` {name (full := MilnorAlgDep.foo)}`foo` ``.
* `` {lean}`term` `` elaborates and highlights a term.
* A `lean` code block (three backticks followed by `lean`) is elaborated in the document,
  highlighted, with hovers (see "The idea" in Chapter 1). Errors are build errors unless the
  block is marked as expected to fail (`lean +error`).
* For a declaration that does not exist yet, write the intended name as plain code
  (`` `MilnorAlgDep.theoremA` ``) and mark the paragraph as a placeholder, as the stubs do. Do not
  use `{name}` or `{docstring}` for it: that is a build error.

If a declaration is renamed in `MilnorAlgDep`, the site build fails with an error pointing at the
reference. Fix the reference in the text.

### Citations

`{citep Bib.BT}[]` gives "(Bogomolov and Tschinkel, 2009)", `{citet Bib.BT}[]` gives
"Bogomolov and Tschinkel (2009)"; both add the full reference as a margin note.
`{citehere Bib.BT}[]` prints the full reference in place (used in the References chapter).
New references go in `Support/Bibliography.lean` (`Article`, `ArXiv`, `InProceedings`, `Thesis`).

### Other markup

Lists (`*` or `1.`), links (`[text](url)`), inline code, emphasis, tables (`:::table`) and margin
notes (`{margin}[...]`) work as in Verso's manual genre; see the
[Verso user's guide](https://verso.lean-lang.org/) and the Lean reference manual's sources for
examples. Verso markup has no comments.

## Pitfalls

* `cc` not found when building MD4Lean: MD4Lean (a Verso dependency) compiles C with `cc` from
  `PATH`. `build.sh` falls back to the `cc` shipped next to `lean` in the toolchain (as on the
  development machine); elsewhere install a C compiler.
* Headings may contain math, but the URL slug becomes ugly; prefer Unicode (Γ, ψ) in headings.
* Fragment-only links (`[see](#foo)`) are wrong: every page has `<base href>` pointing at the site
  root, so they resolve against the front page. Use `cref`/`ref`. `check-links.py` catches this.
* Absolute links (`/foo`) leave `/MilnorAlgDep-lean/`; Verso rewrites its own links, but not
  hand-written ones. `check-links.py` catches this too.
* Section and statement tags must be distinct (`sec:...`, `ss:...` versus `thm:`, `lem:`, ...).
* In `Support/` (modules): Verso expanders must be `meta def`, argument parsers `meta instance`;
  `block_extension` must not be in an `@[expose]` section; `inlines!` needs
  `import Verso.Doc.Concrete.InlineString`.

## Updating dependencies

The site follows the root package. When Mathlib (and with it Lean) is bumped at the root:

1. Set `rev` of `verso` in `site/lakefile.toml` to the Verso tag of the new Lean version
   (`git ls-remote --tags https://github.com/leanprover/verso`).
2. In `site/`, run `lake update verso`. Mathlib and the other packages of the root manifest are
   inherited through the path dependency `MilnorAlgDep`, and Lake takes their revisions from
   `../lake-manifest.json` (which must already be updated); it also updates
   `site/lean-toolchain`. Only do this after the root's `.lake/packages` is at the new revisions,
   i.e. after a root `lake build`. `MilnorAlgDep` must stay the first `[[require]]` in
   `site/lakefile.toml`, so that `plausible` and `Cli`, which Verso also requires, come from the
   root manifest.
3. Run `python3 site/check-deps.py`, then `site/build.sh`. Commit `site/lakefile.toml`,
   `site/lake-manifest.json` and `site/lean-toolchain`.

Until then CI's site job fails at `check-deps.py`, with a message saying what differs.

## CI and deployment

`.github/workflows/lean_action_ci.yml` has three jobs:

* `build`: the Lean library (`leanprover/lean-action`), unchanged.
* `site`: `check-deps.py`, `lake exe cache get` at the root (the only Mathlib download), then
  `site/build.sh`; uploads `site/_out/html-multi` as the Pages artifact. Verso's build and the
  project build are cached. Runs on every push and pull request.
* `deploy`: on `main` only (push or manual run), publishes the artifact to GitHub Pages.

The site therefore deploys on every push to `main` whose site build succeeds. On a pull request
the rendered site can be downloaded from the run's `github-pages` artifact.
