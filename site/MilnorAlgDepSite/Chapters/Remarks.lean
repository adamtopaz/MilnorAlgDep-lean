import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite
open MilnorAlgDep

set_option pp.rawOnError true

#doc (Manual) "Remarks" =>
%%%
tag := "sec:remarks"
%%%

The blueprint ends with remarks on its hypotheses and on open questions; they are reproduced
here, followed by what the formalization has found about the hypotheses of individual statements.
The blueprint's third remark, on formalization, is superseded by
{ref "sec:formalization"}[Chapter 9].
It says that the characteristic $`0` proof only needs two facts about differentials
({cref "ss:lax-general"}[]); the formal proof needs one more, (S2) for a point $`Q_a`, which
gives $`\mu(x) \in Q_x` and the derivation to which the eigenvalue lemma is applied
({cref "ss:model0"}[]), as in the blueprint's own proofs of {cref "lem:K0"}[] and
{cref "lem:tauinQ"}[].

# The hypotheses of Theorem A
%%%
tag := "ss:hypotheses"
%%%

:::rmk "8.1" (title := "The hypotheses")
(A1) cannot be dropped: if $`v` is a valuation of $`K` and $`\chi \colon \Gamma_v \to V_{L|l}` is
any homomorphism, then $`\psi = \chi \circ v` satisfies $`\psi(1-x) \in \{0, \psi(x)\}` whenever
$`\psi(x) \neq 0`, so the dependence condition in (A2) holds trivially.
More generally one expects that without injectivity $`\psi` is governed by a place of $`K` rather
than an embedding; this is not treated here.
(A3) excludes the homomorphisms whose image lies in a single point.
Hypothesis (A4) is used only to know that $`K^\times` has no non-zero homomorphism to $`\ZZ` when
$`\chr L > 0`.
:::

For the example: $`\psi(x) \neq 0` forces $`v(x) \neq 0`; if $`v(x) > 0` then $`v(1-x) = 0`, and if
$`v(x) < 0` then $`v(1-x) = v(x)`.
In the formal statement of (A2), "dependent" includes the case that one of the two elements is
$`0` ({cref "ss:reading"}[]), so such a $`\psi` satisfies the formal (A2) as well.

When $`\chr L = 0`, (A4) is vacuous.
The blueprint's use of (A4), "every homomorphism $`K^\times \to \ZZ` is trivial", is (eq:nohom) in
Step A ({name}`nohom`); the formal proof uses it once, to show that the function $`\nu` of
{cref "lem:gauge"}[] vanishes ({name}`CharPHyp.ν_eq_zero`).
The formal reduction to a perfect field $`K` also uses (A4), to know that the characteristic of
$`K` is a prime $`q` when $`\chr L > 0` ({name}`theoremA_perfect_aux`); this use comes from the
way the formal proof is organized and could be avoided by a case split on $`\chr K`.

# Open points
%%%
tag := "ss:open"
%%%

:::rmk "8.2" (title := "Open points")
* *(1)* In positive characteristic the proof needs three $`\psi`-independent elements, for the
  seven-point configuration of {cref "lem:quadrangle"}[] in the proof of Lemma 6.3.
  It is not known whether {cref "thm:A"}[] holds with $`d = 2` in positive characteristic.
* *(2)* It is not known whether there is a homomorphism $`\psi` satisfying (A1)–(A3) with
  $`\chr K = 0 < \chr L`.
  Hypothesis (A4) enters only through the triviality of homomorphisms $`K^\times \to \ZZ`.
* *(3)* {cref "thm:C"}[] assumes $`K \neq k_0`.
  For fields algebraic over the prime field, $`\Kr_*` vanishes in positive degrees in positive
  characteristic, and in characteristic $`0` the question is of a different nature.
:::

The formal statements keep these hypotheses: $`d` is `if ringChar L = 0 then 2 else 3` in (A3),
(A4) is `ringChar L ≠ 0 → ringChar K ≠ 0`, and {name}`theoremC` assumes an element of $`K`
transcendental over the prime field.

# What the formalization adds
%%%
tag := "ss:formalAdds"
%%%

The formalization found no false statement and no gap in the blueprint.
Every numbered statement is formalized, except Lemma 3.1, whose uses are replaced by a different
argument ({cref "ss:sepcrit"}[]), and every proof was checked, in both characteristics.
It did find hypotheses that are not needed, steps that can be shortened, and standard tools that
can be avoided.

_Hypotheses that are not needed._

* {cref "lem:trichotomy"}[] (c): $`i \leq j` implies $`k \geq i`; neither $`i = j` nor
  $`\omega_A(P) = \omega_A(Q)` is needed ({name}`IsNormalized.hgt_le_of_hgt_le`).
  Apart from a missing "distinct" in the example after {cref "lem:lax"}[] ({cref "ss:lax"}[]),
  this is the only inaccuracy found in Chapters 3–5.
* {cref "lem:lax"}[]: the lines of the points of any algebraically dependent family of
  transcendental elements are linearly dependent; the points need not be distinct
  ({name}`not_linearIndependent_modelD_of_not_algebraicIndependent`).
  In its general form the lax property holds for any extension of a perfect field, without models
  ({name}`algebraicIndependent_of_linearIndependent_kaehler_D`).
  So propagation needs no distinctness of the point $`X`.
* {cref "lem:quadrangle"}[]: the incidences $`G \notin \{A, C, D, E\}` and
  $`H \notin \{A, B, C, G\}`, which the blueprint proves first, and $`G \neq B`, which the line
  $`\la B, G \ra` requires and which the blueprint proves in {cref "lem:cocycle"}[], are
  consequences of the proof; only the inclusion half of propagation is used.
  Accordingly, the proof of {cref "lem:cocycle"}[] uses (eq:sum) only in the form "$`Q_{x+y}` lies
  on $`\la Q_x, Q_y \ra`", which holds without hypotheses
  ({name}`CharPHyp.isAlgebraic_ρ_add`).
* {cref "lem:symbols"}[] (a) does not need $`l` to be relatively algebraically closed
  ({name}`symbol_ne_zero_of_algebraicIndependent`; the hypothesis is part of the frozen
  statement).
* {cref "thm:D"}[]: the hypothesis that the inverse of $`\varphi` is graded (`hφsymm` in
  {name}`theoremD`) follows from the others, because the rational Milnor rings are direct sums
  of their homogeneous parts ({name}`MilnorKQ.gradedAlgebra`), so a bijective graded
  homomorphism maps each $`\Kr_n(K)` onto $`\Kr_n(L)`; the formal statement still has it.
* The uniqueness statements need less than the blueprint assumes: {name}`theoremA_perfect_unique`
  only needs $`\psi \neq 0`, and $`r' \neq 0` is not used in {name}`theoremB_unique` and
  {name}`theoremC_unique`.
* In characteristic $`0` the proof of {cref "thm:A"}[] needs no reduction to a perfect field
  $`K` ({name}`theoremA_perfect_of_charZero` holds for any field $`K`).
* Step B needs no hypothesis beyond (H0)–(H3) ({ref "ss:stepB"}[Section 6.4]).

_Steps that can be shortened._

* {cref "prop:levels"}[]: the blueprint shows that $`\nu(-s) - \nu(s)` is a constant and then that
  the constant vanishes; it suffices to show that it vanishes at each pair of $`\psi`-independent
  elements separately ({name}`CharPHyp.ν_mul`).
* {cref "lem:K0"}[] (c): four monomials $`x_1, x_2, x_3, x_1 x_2 x_3` suffice, instead of
  $`p^2 + p + 1` lines ({name}`exists_notMem_span_four`).
* {cref "prop:rational"}[]: the integers $`r_j` need not be compatible; of the factorization of the
  norm only one valuation is needed, and the degree (the order at $`\infty`) will do; and the
  factorization $`MN = p^\beta n'` is unnecessary ({ref "ss:stepCP"}[Section 6.6.2]).
* Representatives "with a common $`N`" are only needed in {cref "lem:gauge"}[]; in
  {cref "lem:K0"}[], {cref "lem:tauinQ"}[] and {cref "lem:theta"}[] the formal proofs use the
  chosen representatives, with different denominators.

_Tools that are avoided._

* Lemma 3.1, and with it unique factorization and Gauss' lemma in the proofs of Chapters 3–5: the
  separability criterion of {cref "ss:sepcrit"}[] replaces it.
* Gauss' lemma in the eigenvalue lemma ({cref "lem:R"}[]), which uses the minimal polynomial
  instead.
* The discrete valuation in the proof of (S3), replaced by the perfect core.
* The relative algebraic closure of $`l(a)` in the proof of {cref "lem:symbols"}[] (a).
* Unique factorization in $`l[s]` in the proof of {cref "prop:rational"}[]: the degree of a
  rational function replaces the order at $`s` ({name}`exists_dvd_sub_of_forall_pow_eq`).
* The irreducible polynomial relation of a triple in the proof of {cref "lem:gauge"}[]: normality
  is checked by the determinants of the differentials in the model of two elements
  ({name}`isNormalized_of_coords`).

So no formal proof argues with Gauss' lemma, unique factorization or the irreducible polynomial
relation of several elements; the norm of a finite extension is used once, in
{cref "prop:rational"}[].
