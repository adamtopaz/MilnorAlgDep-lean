import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDepSite.Chapters.Introduction
import MilnorAlgDepSite.Chapters.Conventions
import MilnorAlgDepSite.Chapters.Levels
import MilnorAlgDepSite.Chapters.Models
import MilnorAlgDepSite.Chapters.Quadrangle
import MilnorAlgDepSite.Chapters.TheoremA
import MilnorAlgDepSite.Chapters.MilnorK
import MilnorAlgDepSite.Chapters.Remarks
import MilnorAlgDepSite.Chapters.Formalization
import MilnorAlgDepSite.Chapters.References

open Verso.Genre Manual
open MilnorAlgDepSite

set_option pp.rawOnError true

#doc (Manual) "Milnor K-theory and field embeddings" =>
%%%
shortTitle := "Milnor K-theory and field embeddings"
%%%

*Steinberg-compatible homomorphisms of multiplicative groups and the reconstruction of fields
from Milnor $`K`-theory.*
A companion to the Lean 4 / Mathlib formalization
[`MilnorAlgDep`](https://github.com/adamtopaz/MilnorAlgDep-lean).

Let $`K` and $`L` be fields and let $`\psi` be a homomorphism from $`K^\times` to the rational
multiplicative group of $`L` modulo constants.
If $`\psi` is injective modulo constants, if $`\psi(x)` and $`\psi(1-x)` are always
algebraically dependent, and if the image of $`\psi` contains two (in positive characteristic:
three) algebraically independent elements, then $`\psi` is a rational multiple of the map induced
by an embedding of $`K` into the perfect closure of $`L` ({cref "thm:A"}[]).
The proof is elementary: it uses Kähler differentials, separability and, in positive
characteristic, a bookkeeping of Frobenius twists.

As a consequence, every homomorphism between rational Milnor $`K`-rings of fields which is
injective in degree one and non-degenerate comes from an embedding of fields
({cref "thm:B"}[], {cref "thm:C"}[]).
In particular a field of absolute transcendence degree at least $`3` (at least $`2` in
characteristic $`0`) is determined up to purely inseparable extensions by $`\QQ \otimes \KM_*`
({cref "thm:D"}[]).

The text follows the blueprint `blueprint/milnor-k-fields.tex`, chapter by chapter and with the
same numbering, and gives the proofs as they were formalized.
Each numbered statement is followed by the Lean declaration that formalizes it, rendered from
the Lean sources; {ref "sec:formalization"}[the last chapter] explains how the formalization is
organized and where it deviates from the blueprint.

The blueprint is an unrefereed draft.
Its proofs are now machine-checked in full: Theorems A, B, C and D are formalized in all
characteristics, with no `sorry` and no axioms beyond the standard ones
({ref "ss:status"}[Section 1.5]).
The formalization found no error in the statements and proofs of the blueprint; where the formal
proofs are simpler or differ from it, the text says so, and {ref "ss:deviations"}[Section 9.4]
collects these places.

{include 1 MilnorAlgDepSite.Chapters.Introduction}

{include 1 MilnorAlgDepSite.Chapters.Conventions}

{include 1 MilnorAlgDepSite.Chapters.Levels}

{include 1 MilnorAlgDepSite.Chapters.Models}

{include 1 MilnorAlgDepSite.Chapters.Quadrangle}

{include 1 MilnorAlgDepSite.Chapters.TheoremA}

{include 1 MilnorAlgDepSite.Chapters.MilnorK}

{include 1 MilnorAlgDepSite.Chapters.Remarks}

{include 1 MilnorAlgDepSite.Chapters.Formalization}

{include 1 MilnorAlgDepSite.Chapters.References}
