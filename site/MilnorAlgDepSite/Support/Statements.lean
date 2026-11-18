module

public import VersoManual
public meta import VersoManual

/-!
# Numbered statement environments

LaTeX-style environments for the companion text:

```
:::lem "4.6" (title := "Trichotomy") (tag := "lem:trichotomy")
Let $`P, Q, R` be distinct collinear points ...
:::
```

renders as a box headed **Lemma 4.6 (Trichotomy).** The label is given explicitly: use the
blueprint's numbering. The optional `tag` registers the statement as a cross-reference target
(use the blueprint's `\label`), and `{cref "lem:trichotomy"}[]` anywhere in the document, on any
page, renders as a link with the text "Lemma 4.6"; `{cref "lem:trichotomy"}[the trichotomy]` uses
the given text instead. Tagged statements also appear in the page's local table of contents.

`cref` also accepts the tag of a chapter or section (`tag := "sec:stepA"` in its `%%%` metadata)
and then generates "Chapter 6" or "Section 6.2". Statement tags and section tags share one
namespace, so they must be distinct.

Directive names and headings:

| directive | heading     |
|-----------|-------------|
| `thm`     | Theorem     |
| `prop`    | Proposition |
| `lem`     | Lemma       |
| `cor`     | Corollary   |
| `defn`    | Definition  |
| `rmk`     | Remark      |
| `ex`      | Example     |
| `proof`   | Proof (unnumbered, takes no arguments) |

Short names are used because `lemma` already names a declaration in the root namespace (Mathlib's
`lemma` command), which would make `:::lemma` ambiguous.
-/

open Lean
open Verso Doc Elab ArgParse
open Verso.Genre Manual
open Verso.Output Html
open Verso.Multi (Link)

public section

namespace MilnorAlgDepSite

/-- The cross-reference domain of tagged statements. -/
def statementDomain : Name := `MilnorAlgDepSite.statement

/-- Everything a statement box needs to know. Serialized into the block's data. -/
structure StatementData where
  /-- `theorem`, `lemma`, ... (lower case); used for the heading and the CSS class. -/
  kind : String
  /-- The number or letter, e.g. `"4.6"` or `"A"`. Empty for unnumbered environments. -/
  label : String
  title : Option String := none
  tag : Option String := none
  /-- Set during traversal once the tag has been registered. -/
  assignedTag : Option Tag := none
deriving ToJson, FromJson, Repr, Inhabited

/-- The heading word: `"Lemma"` for `kind = "lemma"`. -/
def StatementData.kindName (d : StatementData) : String :=
  d.kind.capitalize

/-- The text of a reference to the statement, e.g. `"Lemma 4.6"`. -/
def StatementData.refText (d : StatementData) : String :=
  if d.label.isEmpty then d.kindName else s!"{d.kindName} {d.label}"

block_extension Block.statement (data : StatementData) where
  data := toJson data
  init st := st
    |>.setDomainTitle statementDomain "Statements"
    |>.setDomainDescription statementDomain "Numbered theorems, lemmas and definitions"
  traverse id json contents := do
    match fromJson? (α := StatementData) json with
    | .error e => reportError s!"Malformed statement data: {e}"; pure none
    | .ok d =>
      match d.tag, d.assignedTag with
      | some tag, none =>
        let path ← (·.path) <$> read
        let some t ← Verso.Genre.Manual.providedTag id path tag
          | pure none
        modify fun st => st
          |>.saveDomainObject statementDomain tag id
          |>.saveDomainObjectData statementDomain tag (json%{"text": $(d.refText)})
        pure <| some <| Verso.Doc.Block.other
          {Block.statement {d with assignedTag := some t} with id := some id} contents
      | _, _ => pure none
  localContentItem _ json _ := do
    let d ← fromJson? (α := StatementData) json
    if d.tag.isNone then return #[]
    let txt := d.refText ++ (d.title.map (s!" ({·})") |>.getD "")
    return #[(txt, Lean.Html.ofString true txt)]
  toTeX := none
  toHtml :=
    open Verso.Doc.Html in
    some <| fun _goI goB id json contents => do
      let .ok (d : StatementData) := fromJson? json
        | reportError "Malformed statement data"; pure .empty
      let st ← HtmlT.state
      let attrs := st.htmlId id
      let titleHtml : Html := match d.title with
        | some t => html%{<span class="statement-title">{s!" ({t})"}</span>}
        | none => .empty
      -- A permalink. Not a bare `#id`: pages have a `<base>` pointing at the site root, so
      -- fragment-only links would resolve against the front page.
      let head : Html :=
        if let some link := st.resolveId id then
          html%{<a class="statement-label" href={link.link}>{d.refText}</a>}
        else html%{<span class="statement-label">{d.refText}</span>}
      pure html%{
        <div class={s!"statement statement-{d.kind}"} {...attrs}>
          <div class="statement-head">{head}{titleHtml}{"."}</div>
          <div class="statement-body">{← contents.mapM goB}</div>
        </div>
      }
  extraCss := [r#"
.statement {
  margin: 1.25em 0;
  padding: 0.6em 1em;
  border-left: 3px solid var(--verso-structure-color, #888);
  background: color-mix(in srgb, var(--verso-structure-color, #888) 6%, transparent);
}
.statement-head { font-weight: bold; margin-bottom: 0.3em; }
.statement-head .statement-title { font-weight: normal; font-style: italic; }
.statement-head a.statement-label { color: inherit; text-decoration: none; }
.statement-head a.statement-label:hover { text-decoration: underline; }
.statement-theorem .statement-body, .statement-proposition .statement-body,
.statement-lemma .statement-body, .statement-corollary .statement-body { font-style: italic; }
.statement-body > p:first-child { margin-top: 0; }
.statement-body > p:last-child { margin-bottom: 0; }
.statement-proof { border-left-style: dotted; background: none; }
.statement-proof .statement-head { font-weight: normal; font-style: italic; }
.statement:target { outline: 2px solid var(--verso-selected-color, #fd0); }
a.statement-ref { text-decoration: underline dotted; }
"#]

/-- Arguments of a numbered environment: `"4.6" (title := "...") (tag := "...")`. -/
structure StatementConfig where
  label : String
  title : Option String
  tag : Option String

section
variable {m : Type → Type} [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
  [MonadError m]

meta instance : FromArgs StatementConfig m where
  fromArgs := StatementConfig.mk <$> .positional `label .string <*>
    .named `title .string true <*> .named `tag .string true
end

/-- Shared implementation of the environment directives. -/
meta def statementExpander (kind : String) (label : String) (title tag : Option String)
    (contents : Array VersoBlock) : DocElabM Term := do
  let blocks ← contents.mapM elabBlock
  ``(Verso.Doc.Block.other
      (Block.statement (StatementData.mk $(quote kind) $(quote label) $(quote title)
        $(quote tag) none))
      #[$[$blocks],*])

/-- `:::thm "A" (title := "Relative version") (tag := "thm:B")` -/
@[directive] meta def thm : DirectiveExpanderOf StatementConfig
  | c, b => statementExpander "theorem" c.label c.title c.tag b
/-- `:::prop "6.1" (tag := "prop:levels")` -/
@[directive] meta def prop : DirectiveExpanderOf StatementConfig
  | c, b => statementExpander "proposition" c.label c.title c.tag b
/-- `:::lem "4.6" (title := "Trichotomy") (tag := "lem:trichotomy")` -/
@[directive] meta def lem : DirectiveExpanderOf StatementConfig
  | c, b => statementExpander "lemma" c.label c.title c.tag b
/-- `:::cor "7.4" (tag := "...")` -/
@[directive] meta def cor : DirectiveExpanderOf StatementConfig
  | c, b => statementExpander "corollary" c.label c.title c.tag b
/-- `:::defn "3.3" (title := "Levels")` -/
@[directive] meta def defn : DirectiveExpanderOf StatementConfig
  | c, b => statementExpander "definition" c.label c.title c.tag b
/-- `:::rmk "8.1" (title := "The hypotheses")` -/
@[directive] meta def rmk : DirectiveExpanderOf StatementConfig
  | c, b => statementExpander "remark" c.label c.title c.tag b
/-- `:::ex "2.3"` -/
@[directive] meta def ex : DirectiveExpanderOf StatementConfig
  | c, b => statementExpander "example" c.label c.title c.tag b
/-- `:::proof` (no arguments): an unnumbered proof box. -/
@[directive] meta def proof : DirectiveExpanderOf Unit
  | (), b => statementExpander "proof" "" none none b

/-! ## References to statements -/

/-- The link and the saved data of the object with this tag in a domain, once it has a link. -/
def resolveTag? (st : TraverseState) (domain : Name) (tag : String) : Option (Link × Json) := do
  let obj ← st.getDomainObject? domain tag
  let id ← obj.ids.toArray[0]?
  let link ← st.resolveId id
  return (link, obj.data)

/--
The text of a reference to a section, from the data Verso saves for it: "Chapter 6" for
`"6."`, "Section 6.2" for `"6.2."`, and the title for unnumbered parts.
-/
def sectionRefText (data : Json) : Option String :=
  match data.getObjValAs? String "sectionNum" with
  | .ok num =>
    let parts := (num.splitOn ".").filter (!·.isEmpty)
    if parts.length ≤ 1 then some s!"Chapter {".".intercalate parts}"
    else some s!"Section {".".intercalate parts}"
  | .error _ => (data.getObjValAs? String "title").toOption

-- A reference to a tagged statement or section; resolved during traversal.
inline_extension Inline.statementRef (tag : String) (resolved : Option (Link × String) := none)
    where
  data := toJson (tag, resolved)
  traverse _ json content := do
    match fromJson? (α := String × Option (Link × String)) json with
    | .error e => reportError s!"Malformed statement reference: {e}"; pure none
    | .ok (_, some _) => pure none
    | .ok (tag, none) =>
      let st ← get
      let resolved : Option (Link × String) :=
        if let some (link, data) := resolveTag? st statementDomain tag then
          some (link, (data.getObjValAs? String "text").toOption.getD tag)
        else if let some (link, data) := resolveTag? st sectionDomain tag then
          some (link, (sectionRefText data).getD tag)
        else none
      match resolved with
      | some r => pure <| some <| .other (Inline.statementRef tag (some r)) content
      | none => pure none
  toTeX := none
  toHtml :=
    open Verso.Doc.Html in
    some <| fun goI _id json content => do
      match fromJson? (α := String × Option (Link × String)) json with
      | .ok (_, some (link, linkText)) =>
        let body ← if content.isEmpty then pure (Lean.Html.ofString true linkText)
          else content.mapM goI
        pure html%{<a class="statement-ref" href={link.link}>{body}</a>}
      | .ok (tag, none) =>
        let known :=
          ((← HtmlT.state).domains[statementDomain]?.map (·.canonicalNames)).getD #[]
        reportError s!"Unknown statement or section tag '{tag}'. Statement tags: {known.toList}"
        if content.isEmpty then pure (Lean.Html.ofString true tag) else content.mapM goI
      | .error e =>
        reportError s!"Malformed statement reference: {e}"; content.mapM goI

/-- Arguments of `cref`: the tag of a statement. -/
structure CrefConfig where
  tag : String

section
variable {m : Type → Type} [Monad m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
  [MonadError m]

meta instance : FromArgs CrefConfig m where
  fromArgs := CrefConfig.mk <$> .positional `tag .string
end

/--
`{cref "lem:trichotomy"}[]` links to the statement with that tag, with link text such as
"Lemma 4.6". For the tag of a chapter or section (`tag := "sec:stepA"` in its `%%%` metadata) the
text is "Chapter 6" or "Section 6.2". Non-empty content replaces the generated text.
-/
@[role] meta def cref : RoleExpanderOf CrefConfig
  | {tag}, content => do
    let inls ← content.mapM elabInline
    ``(Verso.Doc.Inline.other (Inline.statementRef $(quote tag)) #[$[$inls],*])

end MilnorAlgDepSite

end
