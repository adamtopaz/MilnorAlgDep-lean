import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite

set_option pp.rawOnError true

#doc (Manual) "Levels and normalized triples" =>
%%%
tag := "sec:levels"
%%%

In {ref "sec:levels"}[Chapters 3]–{ref "sec:quadrangle"}[5], $`L` is a perfect field of
characteristic exponent $`p`, and $`l \subset L` a relatively algebraically closed subfield.
Two transcendental elements of a point are compared by how far apart they are in the Frobenius
direction: this is their level.
These chapters are only needed in positive characteristic.

# Levels

For $`s, t` in a point $`P` write $`s \approx t` if each of $`s, t` is separable algebraic over
$`l` adjoined the other.

:::lem "3.2" (tag := "lem:levels")
The relation $`\approx` is an equivalence relation on $`P \sm l`, and for all
$`s, t \in P \sm l` there is a unique $`j \in \Gamma` with $`s \approx \Frob^j(t)`.
:::

_Formal counterpart (placeholder):_ `MilnorAlgDep/CharP/Levels.lean` (work package WP-P1).

# Normalized triples

:::lem "3.5" (title := "Normalized triples") (tag := "lem:normalized")
Let $`P, Q, R` be distinct collinear points.
Normalized triples exist, and their levels form a single orbit of the diagonal action of
$`\Gamma` on $`\Lambda(P) \times \Lambda(Q) \times \Lambda(R)`, the _level triple_
$`\lt(P, Q, R)`.
:::

_Formal counterpart (placeholder):_ `MilnorAlgDep/CharP/Levels.lean` (work package WP-P1).
