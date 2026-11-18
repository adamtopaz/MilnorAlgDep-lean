import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite

set_option pp.rawOnError true

#doc (Manual) "The quadrangle lemma" =>
%%%
tag := "sec:quadrangle"
%%%

The quadrangle lemma produces consistent levels on a configuration of seven points; it is the
geometric input of Step A ({cref "sec:stepA"}[]).

:::lem "5.1" (title := "Quadrangle") (tag := "lem:quadrangle")
Let $`A, B, C` be non-collinear points, $`D \neq A, B` a point on $`\la A, B \ra`,
$`E \neq B, C` a point on $`\la B, C \ra`, $`G` a point on $`\la D, C \ra` and on
$`\la A, E \ra`, and $`H` a point on $`\la A, C \ra` and on $`\la B, G \ra`.
Then there are levels $`\alpha_X \in \Lambda(X)` for $`X \in \{A, B, C, D, E, G, H\}` such that
for each of the six collinear triples
$$`(A,B,D),\ (B,C,E),\ (D,C,G),\ (A,E,G),\ (A,C,H),\ (B,H,G)`
the corresponding triple of levels is its level triple.
:::

_Formal counterpart (placeholder):_ `MilnorAlgDep/CharP/Quadrangle.lean` (work package WP-P3).
