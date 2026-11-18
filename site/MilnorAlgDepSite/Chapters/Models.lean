import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite

set_option pp.rawOnError true

#doc (Manual) "Models and the lax differential map" =>
%%%
tag := "sec:models"
%%%

A transcendence basis $`A` of $`L|l` determines a non-perfect subfield, the _model_
$$`L_A = \{ y \in L : y \text{ is separable algebraic over } l(A) \},`
whose Kähler differentials $`\Omega_A = \Omega_{L_A|l}` see exactly one level of each point.
This chapter relates levels to lines in $`\Omega_A`.

:::lem "4.6" (title := "Trichotomy") (tag := "lem:trichotomy")
Let $`P, Q, R` be distinct collinear points and let $`(i, j, k) \in \Gamma^3` be the heights of
a level triple of $`(P, Q, R)`.
If $`i < j`, then $`k = i` and $`\omega_A(R) = \omega_A(P)`; if $`i = j` and
$`\omega_A(P) \neq \omega_A(Q)`, then $`k = i` and $`\omega_A(R)` is a third line in the plane
$`\omega_A(P) + \omega_A(Q)`; if $`i = j` and $`\omega_A(P) = \omega_A(Q)`, then $`k \geq i`.
Conversely, if the three lines are pairwise distinct, then $`i = j = k`.
:::

_Formal counterpart (placeholder):_ `MilnorAlgDep/CharP/Models.lean` (work package WP-P2).
