import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite
open MilnorAlgDep

set_option pp.rawOnError true

#doc (Manual) "The quadrangle lemma" =>
%%%
tag := "sec:quadrangle"
%%%

The quadrangle lemma produces consistent levels on a configuration of seven points; it is the
geometric input of Step A ({cref "sec:stepA"}[]).
We keep the assumptions of {ref "sec:levels"}[Chapter 3].

:::lem "5.1" (title := "Quadrangle") (tag := "lem:quadrangle")
Let $`A, B, C` be non-collinear points, let $`D` be a point on $`\la A, B \ra` different from
$`A, B`, and $`E` a point on $`\la B, C \ra` different from $`B, C`.
Let $`G` be a point lying on both $`\la D, C \ra` and $`\la A, E \ra`, and let $`H` be a point lying
on both $`\la A, C \ra` and $`\la B, G \ra`.
Then there are levels $`\alpha_X \in \Lambda(X)` for $`X \in \{A, B, C, D, E, G, H\}` such that
for each of the six collinear triples
$$`(A,B,D),\ (B,C,E),\ (D,C,G),\ (A,E,G),\ (A,C,H),\ (B,H,G)`
the corresponding triple of levels $`\alpha_X` is its level triple.
:::

In Lean the seven points are given by transcendental elements $`a_0, \dots, h_0`, and the
hypotheses are translated with the dictionary of {cref "ss:elementwise"}[]: "$`A, B, C` are not
collinear" is the algebraic independence of $`(a_0, b_0, c_0)`; "$`D` lies on $`\la A, B \ra` and
differs from $`A` and $`B`" is {name}`IsCollinearTriple` `l a₀ b₀ d₀`; "$`G` lies on
$`\la D, C \ra`" is "$`g_0` is algebraic over $`l(d_0, c_0)`".
Levels $`\alpha_X` with the required property are elements $`a \in A, \dots, h \in H` such that
the six triples are normalized: then $`\alpha_X = \lev(x)`.

{docstring MilnorAlgDep.quadrangle}

Step A uses the lemma through the first entries of three of the level triples.
With the elements $`a, b, c, d, e, h` of the lemma, {cref "lem:normalized"}[] (b) computes
{name}`levelTriple` `l p a₀ b₀ d₀` as
$`(\lev b - \lev b_0 - (\lev a - \lev a_0),\ \dots)`, and similarly for $`(B, C, E)` and
$`(A, C, H)`; so the first entries add up:

{docstring MilnorAlgDep.levelTriple_fst_add_levelTriple_fst}

This is the cocycle relation $`c(u, z) = c(u, w) + c(w, z)` of {cref "lem:cocycle"}[], when
$`a_0, b_0, c_0` represent $`\psi(u), \psi(w), \psi(z)` and $`d_0, e_0, g_0, h_0` represent
$`\psi(u + w), \psi(w + z), \psi(u + w + z), \psi(u + z)`.

_Proof of {cref "lem:quadrangle"}[] (as formalized)._
The proof follows the blueprint, in coordinates.

1. _Choice of a model._
   Choose a normalized triple $`(a, b, d)` for $`(A, B, D)` with $`a = a_0`, then a normalized
   triple $`(b, c, e)` for $`(B, C, E)` with the same $`b`; both exist by
   {cref "lem:normalized"}[] (a), whose formal version keeps the first entry
   ({name}`exists_isNormalized`).
   The elements $`a, b, c` are algebraically independent; extend them to a transcendence basis
   $`\mathcal B` of $`L|l` and work in the model $`L_{\mathcal B}`, writing $`\omega` for the lines.
   Let $`f_a, f_b, f_c` be the coordinate functions of the basis $`(d\beta)_{\beta \in \mathcal B}`
   of $`\Omega_{\mathcal B}` ({name}`modelBasis`) at $`a, b, c`.
   The elements $`a, b, c` are model generators, and $`\omega(A), \omega(B), \omega(C)` are spanned
   by $`da, db, dc`.
2. _The points $`D` and $`E`._
   By {cref "lem:trichotomy"}[] (b), $`d` and $`e` are model generators, and
   $$`dd = d_a\, da + d_b\, db, \qquad de = e_b\, db + e_c\, dc, \qquad d_a, d_b, e_b, e_c \neq 0`
   ({name}`IsNormalized.coord_modelD`).
3. _The point $`G`._
   Let $`g` be the canonical model generator of $`G`.
   The lines $`\omega(D)` and $`\omega(C)` differ (look at $`f_c`), and so do $`\omega(A)` and
   $`\omega(E)` (look at $`f_a`).
   By propagation, in the form of {name}`omega_le_sup_of_isAlgebraic`,
   $`dg = s\, dd + t\, dc = s'\, da + t'\, de` for some coefficients.
   Comparing coordinates, $`s d_a = s'`, $`s d_b = t' e_b` and $`t = t' e_c`.
   If $`s = 0`, then $`t' = 0` and $`s' = 0`, so $`dg = 0`, which is impossible; so $`s \neq 0`, then
   $`t' \neq 0`, and all three coordinates $`s d_a`, $`s d_b`, $`t' e_c` of $`dg` are non-zero
   ({name}`coord_ne_zero_of_mem_sup_of_mem_sup`).
4. _The point $`H`._
   Let $`h` be the canonical model generator of $`H`.
   The lines $`\omega(A), \omega(C)` differ, and so do $`\omega(B), \omega(G)` (look at $`f_a`).
   By propagation, $`dh = s\, da + t\, dc = s'\, db + t'\, dg`.
   So $`f_b(dh) = 0`, and $`t' \neq 0`, as otherwise $`dh = s'\, db` would have
   $`s' = f_b(dh) = 0`; hence $`f_a(dh) = t' f_a(dg)` and $`f_c(dh) = t' f_c(dg)` are non-zero
   ({name}`coord_of_mem_sup_of_mem_sup`).
5. _The four remaining triples._
   For each of $`(D, C, G)`, $`(A, E, G)`, $`(A, C, H)`, $`(B, H, G)`, the three lines are pairwise
   distinct, because for each pair one of $`f_a, f_b, f_c` vanishes on exactly one of the two
   spanning vectors:

   :::table +header
   *
     * Triple
     * Pairs of lines and the coordinate that separates them
   *
     * $`(D, C, G)`
     * $`D, C`: $`f_c`; $`D, G`: $`f_c`; $`C, G`: $`f_a`
   *
     * $`(A, E, G)`
     * $`A, E`: $`f_a`; $`A, G`: $`f_b`; $`E, G`: $`f_a`
   *
     * $`(A, C, H)`
     * $`A, C`: $`f_a`; $`A, H`: $`f_c`; $`C, H`: $`f_a`
   *
     * $`(B, H, G)`
     * $`B, G`: $`f_a`; $`B, H`: $`f_b`; $`H, G`: $`f_b`
   :::

   Points with distinct lines are distinct ({name}`algebraicIndependent_pair_of_omega_ne`), so each
   of the four triples consists of three distinct collinear points
   ({name}`isCollinearTriple_of_omega_ne`), and {cref "lem:trichotomy"}[] (d)
   ({name}`isNormalized_of_hgt_eq_zero`) shows that its model generators form a normalized
   triple.

So $`\alpha_X = \lambda_{\mathcal B}(X)` has the required property.
The main step, inside the model, is:

{docstring MilnorAlgDep.quadrangle_of_isTranscendenceBasis}

Two differences from the blueprint's proof.
The blueprint first shows that $`G \notin \{A, C, D, E\}` and $`H \notin \{A, B, C, G\}`, using the
non-collinearity of $`A, B, C`.
The formal proof does not prove these incidences separately: they come out of step 5, since
distinct lines belong to distinct points (and $`G \neq B` from $`\omega(B) \neq \omega(G)` in step
4).
And the blueprint computes the lines $`\omega(G)` and $`\omega(H)` as intersections of planes,
spanned by
$$`d_a\, da + d_b\, db + \frac{d_b e_c}{e_b}\, dc \qquad \text{and} \qquad
  d_a\, da + \frac{d_b e_c}{e_b}\, dc;`
the formal proof only uses the inclusion half of propagation and the vanishing pattern of the
coordinates, so it never needs the planes to be distinct.
