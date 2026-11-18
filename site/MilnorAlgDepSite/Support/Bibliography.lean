module

public import VersoManual
-- `inlines!` is not re-exported by `VersoManual` to modules.
import Verso.Doc.Concrete.InlineString

/-!
# Bibliography

One value per reference; cite with `{citep Bib.BT}[]` (parenthetical, "(Bogomolov and
Tschinkel, 2009)"), `{citet Bib.BT}[]` (textual) or `{citehere Bib.BT}[]` (the full reference in
place). The full reference also appears as a margin note next to `citep`/`citet`. Available types
include `Article`, `ArXiv`, `InProceedings` and `Thesis` (see `VersoManual.Bibliography`).
The names follow the blueprint's `\bibitem` keys.
-/

open Verso.Genre.Manual

public section

namespace MilnorAlgDepSite.Bib

/-- `\bibitem{BT}` -/
def BT : Article where
  title := inlines!"Milnor $`K_2` and field homomorphisms"
  authors := #[inlines!"F. Bogomolov", inlines!"Yu. Tschinkel"]
  journal := inlines!"Surveys in Differential Geometry"
  year := 2009
  month := none
  volume := inlines!"13"
  number := .concat #[]
  pages := some (223, 244)

/-- `\bibitem{T}` -/
def T : ArXiv where
  title := inlines!"Algebraic dependence and Milnor K-theory"
  authors := #[inlines!"A. Topaz"]
  year := 2022
  id := "2211.14665"

end MilnorAlgDepSite.Bib

end
