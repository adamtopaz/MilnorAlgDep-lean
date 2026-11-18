import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep
-- Redundant once the supervisor regenerates `MilnorAlgDep.lean` to import every module.
import MilnorAlgDep.Standard.Eigenvalue

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite

set_option pp.rawOnError true

#doc (Manual) "Conventions and standard facts" =>
%%%
tag := "sec:conv"
%%%

This chapter fixes the language of points and flats, the bookkeeping of Frobenius twists, and
the group $`V_{L|l}`, and collects the standard facts from field theory that the proof uses.

# Points and flats

Let $`L` be a field and $`l \subset L` a relatively algebraically closed subfield.
A _flat_ of $`L|l` is a relatively algebraically closed subfield of $`L` containing $`l`; its
_rank_ is its transcendence degree over $`l`.
A _point_ is a flat of rank $`1` and a _line_ is a flat of rank $`2`.
For $`a \in L \sm l` we write $`Q_a` for the point containing $`a`, the relative algebraic
closure of $`l(a)` in $`L`.

# Frobenius and the group Γ

For a perfect field $`L` let $`p` be its characteristic exponent and $`\Frob \colon x \mapsto x^p`
its Frobenius automorphism.
We put $`\Gamma = \ZZ` if $`p > 1` and $`\Gamma = \{0\}` if $`p = 1`; all integers measuring
Frobenius twists are elements of $`\Gamma`.

# The group V
%%%
tag := "ss:V"
%%%

Let $`L` be perfect, $`l \subset L` relatively algebraically closed, and $`V = V_{L|l}`.
Then $`[a] = 0` in $`V` if and only if $`a \in l^\times` (V1); every $`v \in V \sm 0` has a
_representative_ $`(N, a)` with $`N \geq 1` prime to $`p` and $`Nv = [a]` (V2); and the point
$`Q_v = Q_a` depends only on $`v` (V3).
Algebraic independence of elements of $`V` is algebraic independence of representatives, which
in Lean is Mathlib's {name}`AlgebraicIndependent`.

# Standard facts

:::lem "2.1" (title := "Standard facts") (tag := "lem:standard")
Let $`l` be a perfect field of characteristic exponent $`p`.
(S1) A polynomial over $`l` all of whose partial derivatives vanish is constant or, if $`p > 1`,
a $`p`-th power.
(S2) If $`E \supset l` is separable algebraic over $`l(A)` for an algebraically independent set
$`A`, then $`\{da : a \in A\}` is a basis of $`\Omega_{E|l}`.
(S3) If moreover $`l` is relatively algebraically closed in $`E` and $`y \in E \sm l`, there is
a largest $`j \in \Gamma_{\geq 0}` with $`\Frob^{-j}(y) \in E`, and $`d(\Frob^{-j} y) \neq 0`.
:::

_Formal counterpart (placeholder):_ `MilnorAlgDep/Standard/` (work package WP-S).

The following lemma shows the intended pattern for every numbered statement: the informal
statement, then the Lean declaration that formalizes it.

:::lem "2.2" (title := "Eigenvalue lemma") (tag := "lem:R")
Let $`E \supset l` be fields, $`a \in E` transcendental over $`l`, and $`\delta` a derivation of
$`E` with $`\delta(l) = 0` and $`\delta(a) = a`.
Let $`b \in E^\times` be separable algebraic over $`l(a)` with $`\delta(b) = \kappa b` for some
$`\kappa \in l`.
Then $`\kappa` lies in the prime field $`\FF` of $`l`.
:::

{docstring MilnorAlgDep.eigenvalue_mem_primeField}

In Lean the prime field of $`l` is the bottom element of the lattice of subfields, so the
conclusion of {name}`MilnorAlgDep.eigenvalue_mem_primeField` reads `κ ∈ (⊥ : Subfield l)`.
The derivation is an $`l`-linear derivation `δ : Derivation l E E`, which encodes
$`\delta(l) = 0`.
