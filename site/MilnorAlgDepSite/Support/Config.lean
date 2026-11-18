module

public import VersoManual

/-!
# Site configuration

The rendering configuration used by `SiteMain.lean`, and the TeX macros available in math.

Math (`` $`...` `` and `` $$`...` ``) is rendered in the browser by the KaTeX bundled with Verso.
`katexMacros` makes the blueprint's macros (`\QQ`, `\Frob`, `\lev`, `\Kr`, ...) available, so
formulas can be copied from `blueprint/milnor-k-fields.tex` unchanged. To add a macro, add a pair
here. (Implementation: an inline script registers the macros with `katex.__defineMacro` on
`DOMContentLoaded`; it runs before Verso's own math rendering, which is registered later by a
deferred script.)
-/

open Lean
open Verso.Genre.Manual

public section

namespace MilnorAlgDepSite

/-- TeX macros from the preamble of `blueprint/milnor-k-fields.tex`. -/
def katexMacros : List (String × String) := [
  ("\\GG", "\\mathbb{G}"),
  ("\\ZZ", "\\mathbb{Z}"),
  ("\\QQ", "\\mathbb{Q}"),
  ("\\FF", "\\mathbb{F}"),
  ("\\acl", "\\operatorname{acl}"),
  ("\\trdeg", "\\operatorname{trdeg}"),
  ("\\rk", "\\operatorname{rk}"),
  ("\\Frob", "\\operatorname{Frob}"),
  ("\\lev", "\\operatorname{lev}"),
  ("\\hgt", "\\operatorname{ht}"),
  -- Overrides KaTeX's `\lt` (which is `<`), as the blueprint does.
  ("\\lt", "\\operatorname{lt}"),
  ("\\chr", "\\operatorname{char}"),
  ("\\dlog", "\\operatorname{dlog}"),
  ("\\sep", "\\mathrm{sep}"),
  ("\\sm", "\\smallsetminus"),
  ("\\la", "\\langle"),
  ("\\ra", "\\rangle"),
  ("\\KM", "K^{M}"),
  ("\\Kr", "\\mathcal{K}")
]

/-- The script that registers `katexMacros` with KaTeX. -/
def katexMacrosJs : String :=
  let table := (Json.mkObj (katexMacros.map fun (k, v) => (k, Json.str v))).compress
  "document.addEventListener('DOMContentLoaded', () => {\n" ++
  "  const k = window.katex;\n" ++
  "  if (!k || typeof k.__defineMacro !== 'function') return;\n" ++
  s!"  for (const [name, body] of Object.entries({table})) k.__defineMacro(name, body);\n" ++
  "});\n"

/-- The repository, linked from every page. -/
def repoUrl : String := "https://github.com/adamtopaz/MilnorAlgDep-lean"

/-- Rendering configuration. Command-line flags of `SiteMain.lean` (e.g. `--output`) override it. -/
def siteConfig : RenderConfig where
  emitTeX := false
  emitHtmlSingle := .no
  emitHtmlMulti := .immediately
  -- One HTML page per chapter; sections are anchors within the chapter's page.
  htmlDepth := 1
  sourceLink := some repoUrl
  issueLink := some (repoUrl ++ "/issues")
  extraJs := ({} : Std.HashSet Verso.Genre.Manual.JS).insert ⟨katexMacrosJs⟩

end MilnorAlgDepSite

end
