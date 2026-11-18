import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep
-- Redundant once the supervisor regenerates `MilnorAlgDep.lean` to import every module.
import MilnorAlgDep.Milnor.ValuationExt

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite

set_option pp.rawOnError true

#doc (Manual) "Milnor K-theory" =>
%%%
tag := "sec:K"
%%%

Theorems B, C and D follow from {cref "thm:A"}[] together with one family of homomorphisms out
of $`\Kr_2`, the tame symbols.
In this chapter $`K` and $`L` are perfect fields, and the product in $`\Kr_*` is written
$`\{\cdot, \cdot\}`.

# A tame symbol

:::lem "7.1" (tag := "lem:tame")
Let $`v` be a valuation of $`L` with valuation ring $`O`, residue field $`\kappa` and value
group $`\Gamma_v`.
There is a $`\QQ`-linear map
$$`T_v \colon \Kr_2(L) \to \Gamma_{v,\QQ} \otimes_\QQ \kappa^\times_\QQ
  \qquad\text{with}\qquad T_v\{c, b\} = -v(b) \otimes [\bar c]`
for all $`c \in O^\times` and $`b \in L^\times`.
:::

_Formal counterpart (placeholder):_ `MilnorAlgDep/Milnor/Tame.lean` (work package WP-K2).

The tame symbols are applied to valuations provided by the following standard fact: if
$`M \subset L` is a subfield and $`b \in L` is transcendental over $`M`, there is a valuation
$`v` of $`L` which is trivial on $`M` and satisfies $`v(b) > 0`.
In Lean a valuation is a {name}`ValuationSubring`, and $`v(b) > 0` becomes `A.valuation b < 1`,
because Mathlib's valuations are written multiplicatively:

{docstring MilnorAlgDep.exists_valuationSubring_of_transcendental}

:::lem "7.2" (tag := "lem:symbols")
Let $`l \subset L` be relatively algebraically closed.
If $`a, b \in L` are algebraically independent over $`l`, then $`\{a, b\} \neq 0` in
$`\Kr_2(L|l)`.
If $`c \in L^\times` is algebraic over the prime field and not a root of unity, and $`b \in L` is
transcendental over the prime field, then $`\{c, b\} \neq 0` in $`\Kr_2(L)`.
:::

_Formal counterpart (placeholder):_ `MilnorAlgDep/Milnor/Symbols.lean` (work package WP-K2).

# Proof of Theorem B

By {cref "lem:symbols"}[], $`\psi = \varphi_1 \circ [\,\cdot\,]` satisfies (A1)–(A4), and
{cref "thm:A"}[] applies; two homomorphisms of algebras generated in degree $`1` that agree in
degree $`1` are equal.

# Proof of Theorem C

The kernel of $`\psi` together with $`0` is a subfield $`k'` of $`K` (Lemma 7.3), so
{cref "thm:A"}[] applies with $`k = k'`; the tame symbols then lift the identity from
$`V_{L|l_0}` to $`\Kr_1(L)`.

# Proof of Theorem D

Apply {cref "thm:C"}[] to $`\varphi` and to $`\varphi^{-1}`; the uniqueness part of
{cref "thm:A"}[] shows that the two embeddings are mutually inverse up to Frobenius.
