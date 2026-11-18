import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite

set_option pp.rawOnError true

#doc (Manual) "Remarks" =>
%%%
tag := "sec:remarks"
%%%

:::rmk "8.1" (title := "The hypotheses")
(A1) cannot be dropped: if $`v` is a valuation of $`K` and $`\chi \colon \Gamma_v \to V_{L|l}` is
any homomorphism, then $`\psi = \chi \circ v` satisfies the dependence condition (A2) trivially.
(A3) excludes the homomorphisms whose image lies in a single point, and (A4) is used only to know
that $`K^\times` has no non-zero homomorphism to $`\ZZ` when $`\chr L > 0`.
:::

:::rmk "8.2" (title := "Open points")
It is not known whether {cref "thm:A"}[] holds with $`d = 2` in positive characteristic, nor
whether there is a homomorphism satisfying (A1)–(A3) with $`\chr K = 0 < \chr L`.
:::

:::rmk "8.3" (title := "On formalization")
Outside {ref "sec:levels"}[Chapters 3]–{ref "sec:quadrangle"}[5], which concern a single
extension in characteristic $`p`, the proof only needs that algebraically dependent elements have
proportional differentials and that $`da = 0` implies $`a \in l`.
{cref "sec:formalization"}[] describes how the formalization is organized.
:::
