import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite
open MilnorAlgDep

set_option pp.rawOnError true

#doc (Manual) "Levels and normalized triples" =>
%%%
tag := "sec:levels"
%%%

In {ref "sec:levels"}[Chapters 3]–{ref "sec:quadrangle"}[5], $`L` is a perfect field of
characteristic exponent $`p`, $`l \subset L` is a relatively algebraically closed (hence perfect)
subfield, and $`\Gamma = \Gamma(L)`.
"Point" and "line" refer to $`L|l` as in {cref "ss:points"}[].
Two transcendental elements of a point are compared by how far apart they are in the Frobenius
direction: this is their level.
These chapters are only needed in positive characteristic.

All results of these three chapters except Lemma 3.1 are formalized, for $`p` prime; so
$`\Gamma = \ZZ`, and $`\Frob^j` is {name}`frobZ` `L p j`.
The Lean files `MilnorAlgDep/CharP/*.lean` work with two fields `l`, `L` and `[Algebra l L]`, and
assume `(p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]` when the
characteristic matters; statements that do not involve $`p` assume `[PerfectField l]` instead.

{docstring MilnorAlgDep.frobZ}

{docstring MilnorAlgDep.IsRelAlgClosed.perfectField}

_Proof._
If $`c \in l`, its $`p`-th root in $`L` is algebraic over $`l`, hence lies in $`l`.

Every point is stable under $`\Frob^{\pm 1}`: $`Q_{\Frob^j s} = Q_s` ({name}`point_frobZ`), and
$`\Frob^j` maps $`l` onto itself ({name}`frobZ_algebraMap_mem_range`).

The formalization reformulates these chapters in two ways.
First, levels and level triples are not defined as sets: everything is said in terms of
elements, as explained in {cref "ss:elementwise"}[].
Second, Lemma 3.1, which describes separability through the partial derivatives of an irreducible
polynomial relation, is not formalized; a criterion in terms of differentials replaces it
({cref "ss:sepcrit"}[]).
No multivariate polynomial occurs in the formal proofs of Chapters 3–5.

# The element-wise formulation
%%%
tag := "ss:elementwise"
%%%

The blueprint attaches to each point $`P` the set $`\Lambda(P)` of its levels, a
$`\Gamma`-torsor, and to three distinct collinear points the level triple, an orbit of $`\Gamma` on
$`\Lambda(P) \times \Lambda(Q) \times \Lambda(R)`; Chapter 4 adds the model level
$`\lambda_A(P) \in \Lambda(P)`.
Each use of these objects compares two levels of one point, so the formalization works with
elements and integers only.

* A point is given by any of its transcendental elements $`s`, and $`Q_s` is {name}`point` `l s`.
  Two transcendental elements lie in the same point when they are algebraically dependent
  ({name}`SamePoint`).
* Instead of the level $`\lev(s) \in \Lambda(P)` there is the _level difference_
  $`\lev(s) - \lev(t) \in \ZZ` of two elements of the same point, {name}`levDiff` `l p s t`,
  characterized by $`s \approx \Frob^{\lev(s) - \lev(t)}(t)` (Lemma 3.2).
  Fixing $`t \in P \sm l`, the map $`\lev(s) \mapsto \lev(s) - \lev(t)` is a bijection
  $`\Lambda(P) \to \ZZ` compatible with the action of $`\Gamma`, so nothing is lost.
* Three distinct collinear points are given by elements $`x, y, z`
  ({name}`IsCollinearTriple`), and a normalized triple is a property of elements
  ({name}`IsNormalized`).
  The level triple $`\lt(Q_x, Q_y, Q_z)` is an orbit of the diagonal action of $`\ZZ`, so it
  contains exactly one triple of the form $`(\lev x, \lev y + j, \lev z + k)`; the pair
  $`(j, k)` is {name}`levelTriple` `l p x y z`.
* In a model $`L_B` ({ref "sec:models"}[Chapter 4]) the height of an element,
  $`\hgt(y) = \lev(y) - \lambda_B(Q_y)`, is defined directly ({name}`hgt`), and the model level
  $`\lambda_B(P)` is not defined: it is the level of the elements of height $`0`, the model
  generators.
  The line of a point is defined through one model generator, $`\Frob^{-\hgt(y)}(y)`
  ({name}`omega`).

The following table is the complete dictionary for
{ref "sec:levels"}[Chapters 3]–{ref "sec:quadrangle"}[5].
Here $`s, t, x, y, z` are transcendental elements of $`L` and $`B` is a family of elements of $`L`.

:::table +header
*
  * Blueprint
  * Formalization
*
  * $`s, t \in P \sm l` for one point $`P`
  * {name}`SamePoint` `l s t`
*
  * $`s \approx t`
  * {name}`SepEquiv` `l s t`
*
  * $`\lev(s) - \lev(t) \in \Gamma`
  * {name}`levDiff` `l p s t`
*
  * $`\lev(s) \geq \lev(t)`
  * `0 ≤ levDiff l p s t`, equivalently: $`s` is separable algebraic over $`l(t)`
*
  * $`\lev(\Frob^j s) = \lev(s) + j`
  * {name}`levDiff_frobZ_left`
*
  * $`P, Q, R` distinct and collinear, $`x \in P \sm l`, $`y \in Q \sm l`, $`z \in R \sm l`
  * {name}`IsCollinearTriple` `l x y z`
*
  * $`(x, y, z)` is normalized
  * {name}`IsNormalized` `l x y z`
*
  * $`(\lev x, \lev y + j, \lev z + k) \in \lt(Q_x, Q_y, Q_z)`
  * `levelTriple l p x y z = (j, k)`
*
  * model $`L_A`, $`\Omega_A = \Omega_{L_A|l}` ($`A` a transcendence basis)
  * {name}`model` `l B`, `Ω[model l B⁄l]` ($`B` any family)
*
  * $`dy \in \Omega_A` for $`y \in L_A`
  * {name}`modelD` `l B y` (it is $`0` if $`y \notin L_B`)
*
  * $`\hgt_A(\lev y) = \lev(y) - \lambda_A(Q_y)`
  * {name}`hgt` `l p B y`
*
  * $`y` is a model generator of $`Q_y`, i.e. $`\lev(y) = \lambda_A(Q_y)`
  * `hgt l p B y = 0`
*
  * $`\omega_A(Q_y)`
  * {name}`omega` `l p B y`
*
  * $`Q_x` lies on $`\la Q_y, Q_z \ra`
  * `IsAlgebraic l⟮y, z⟯ x`
*
  * $`Q_x, Q_y, Q_z` are not collinear
  * `AlgebraicIndependent l ![x, y, z]`
:::

In the proofs below we use whichever language is clearer.
The definitions with junk values ({name}`levDiff` outside one point, {name}`hgt` for an
algebraic element, {name}`modelD` outside the model) are only used with the hypotheses that make
them meaningful.

# Lemma 3.1 and a separability criterion
%%%
tag := "ss:sepcrit"
%%%

:::lem "3.1" (tag := "lem:sepcrit")
Let $`m \geq 2` and let $`y_1, \dots, y_m \in L` be algebraically dependent over $`l`, any
$`m - 1` of them being algebraically independent.
Then:

* *(a)* The ideal of polynomial relations among $`(y_1, \dots, y_m)` over $`l` is generated by an
  irreducible $`f \in l[Y_1, \dots, Y_m]` in which every variable occurs.
* *(b)* At least one partial derivative of $`f` is non-zero.
* *(c)* For each $`i` the following are equivalent: $`y_i` is separable over
  $`l(y_j : j \neq i)`; $`\partial f / \partial Y_i \neq 0`;
  $`(\partial f / \partial Y_i)(y_1, \dots, y_m) \neq 0`.
:::

_This lemma is not formalized._
The blueprint proves it with unique factorization and Gauss' lemma, and uses it to decide
separability from the linear relation
$$`f_{Y_1}(y)\, dy_1 + \dots + f_{Y_m}(y)\, dy_m = 0`
given by (S2): part (b) says that the relation is non-trivial, and part (c) says that the
coefficient of $`dy_i` is non-zero exactly when $`y_i` is separable over the others.
The formal proofs only need the consequences of this for differentials, and these have direct
proofs.
"Separable implies $`f_{Y_i}(y) \neq 0`" is replaced by (S2): if $`y_i` is separable over
$`l(y_j : j \neq i)`, then $`dy_i` lies in the span of the other differentials
({name}`kaehler_D_mem_span_range_of_isSeparable`).
The converse, together with (b), is replaced by the following criterion.

:::prop "" (title := "Separability criterion") (tag := "prop:sepcrit")
Let $`l` be a perfect field, $`E \supset l` a field, $`(x_k)_{k}` a family of elements of $`E`
whose differentials $`dx_k` are linearly independent in $`\Omega_{E|l}`, and $`y \in E` algebraic
over $`l(x_k : k)`.
Then $`y` is separable over $`l(x_k : k)`.
:::

{docstring MilnorAlgDep.isSeparable_adjoin_of_linearIndependent_kaehler_D}

The family $`x` is arbitrary; it is algebraically independent by the lax property
({cref "ss:lax-general"}[]).

_Proof (as formalized)._
In characteristic $`0` every irreducible polynomial is separable.
Let $`p > 1` and $`F = l(x_k : k)`, and suppose that $`y` is not separable over $`F`.
Then its minimal polynomial $`f = \sum_i c_i X^i \in F[X]` has $`f' = 0`.

1. By the lax property the $`x_k` are algebraically independent, so by (S2) the $`dx_k` form a
   basis of $`\Omega_{F|l}`; let $`\partial_k` be the coordinate derivations of $`F`
   ({name}`coordDerivation`).
   Choose $`E`-linear forms $`\varphi_k` on $`\Omega_{E|l}` with
   $`\varphi_k(dx_j) = \delta_{jk}`, which is possible because the $`dx_j` are linearly
   independent.
   The derivation $`\delta_k = \varphi_k \circ d` of $`E` restricts to $`\partial_k` on $`F`:
   both are $`l`-derivations $`F \to E` with the same values on the $`x_j`.
2. Applying $`\delta_k` to $`f(y) = 0` gives
   $`\sum_i \partial_k(c_i)\, y^i + f'(y)\, \delta_k(y) = 0`, and $`f' = 0`.
   So the polynomial $`\sum_i \partial_k(c_i) X^i \in F[X]` vanishes at $`y`; its degree is less
   than $`\deg f`, because $`f` is monic and $`\partial_k(1) = 0`.
   Hence it is zero: $`\partial_k(c_i) = 0` for all $`i` and $`k`.
3. So $`dc_i = 0` in $`\Omega_{F|l}`, and $`c_i \in F^p` by the kernel statement of (S3) for
   $`E = F` ({name}`exists_pow_eq_of_kaehler_D_eq_zero`).
4. Since $`f' = 0`, $`f(X) = h(X^p)` for some $`h \in F[X]`, and the coefficients of $`h` are
   $`p`-th powers; so $`f = g^p` for some $`g \in F[X]`, contradicting the irreducibility of
   $`f`.

In the applications $`E` is a model, the field $`L_B` of elements of $`L` separable algebraic
over $`l(B)` for a family $`B`, with $`\Omega_B = \Omega_{L_B|l}`
({cref "defn:model"}[]); for $`B` algebraically independent the $`dB_i` form a basis of $`\Omega_B`
by (S2).
The proofs of this chapter use the models of one or two elements, for instance the field of
"elements separable algebraic over $`l(x, y)`" in the blueprint's proof of {cref "lem:normalized"}[],
which is the model of $`(x, y)`.
In a model the criterion reads:

{docstring MilnorAlgDep.isSeparable_of_linearIndependent_modelD}

The case of two elements is {name}`isSeparable_of_linearIndependent_modelD_pair`.
Together with the lax property it gives the following test for normalized triples (defined in
{cref "ss:normalized"}[]), which is used in {cref "lem:normalized"}[] and
{cref "lem:trichotomy"}[]:

{docstring MilnorAlgDep.isNormalized_of_linearIndependent_modelD}

# Levels
%%%
tag := "ss:levels"
%%%

Let $`P` be a point.
For $`s, t \in P \sm l` write $`s \approx t` if $`s` is separable algebraic over $`l(t)` and $`t`
is separable algebraic over $`l(s)`.

{docstring MilnorAlgDep.SamePoint}

{docstring MilnorAlgDep.SepEquiv}

:::lem "3.2" (tag := "lem:levels")
The relation $`\approx` is an equivalence relation on $`P \sm l`, and for all
$`s, t \in P \sm l` there is a unique $`j \in \Gamma` with $`s \approx \Frob^j(t)`.
:::

{docstring MilnorAlgDep.existsUnique_sepEquiv_frobZ}

_Proof (as formalized)._
Reflexivity and symmetry are clear ({name}`SepEquiv.refl`, {name}`SepEquiv.symm`).
Transitivity ({name}`SepEquiv.trans`) is transitivity of separability: if $`u` is separable over
$`l(s)` and $`s` over $`l(t)`, then $`l(s)` is contained in the model $`L_{(t)}` of the
one-element family $`(t)`, and an element separable over a subfield of a model lies in the model
({cref "lem:model"}[] (b)); so $`u` is separable over $`l(t)`
({name}`isSeparable_adjoin_simple_trans`).

_Existence._
Let $`E = L_{(t)}` be the field of elements separable algebraic over $`l(t)`; by (S2),
$`\Omega_{E|l}` has basis $`dt`, and $`l` is relatively algebraically closed in $`E`.
Since $`s` is algebraic over $`l(t)`, some $`s^{p^m}` lies in $`E` ({cref "lem:model"}[] (c)),
and it is not in $`l`.
By (S3) for $`E`, $`s^{p^m} = z^{p^k}` with $`z \in E` and $`dz \neq 0`.
Then $`z` is separable over $`l(t)`, it is transcendental over $`l` (as $`dz \neq 0`), and it lies
in the point $`Q_t`; so $`t` is algebraic over $`l(z)`, and the separability criterion, applied in
$`E` to the one-element family $`(z)`, shows that $`t` is separable over $`l(z)`.
Thus $`z \approx t`.
Since $`z = \Frob^{m-k}(s)` and $`\approx` is invariant under the automorphism $`\Frob^{k-m}` of
$`L`, which preserves $`l` ({name}`sepEquiv_frobZ_iff`), we get $`s \approx \Frob^{k-m}(t)`.

_Uniqueness._
If $`s \approx \Frob^j(t)` and $`s \approx \Frob^{j'}(t)`, then
$`t \approx \Frob^{n}(t)` with $`n = j' - j`, and also $`\Frob^{-n}(t) \approx t`.
If $`n \neq 0`, one of these says that a transcendental element $`u` is separable over
$`l(u^{p^{|n|}})`, which the following lemma excludes ({name}`eq_zero_of_sepEquiv_frobZ`).

{docstring MilnorAlgDep.not_isSeparable_adjoin_pow_pow}

Indeed, if $`u` were separable over $`l(u^{p^n})`, then by (S2), in the model $`L_{(u)}`,
$`du` would be a multiple of $`d(u^{p^n}) = 0`, while $`du` is a basis vector.
(The blueprint argues that $`u` is purely inseparable of degree $`p^n` over $`l(u^{p^n})`, and it
obtains existence from the irreducible relation of $`(s, t)` and Lemma 3.1.)

:::defn "3.3" (title := "Levels") (tag := "def:levels")
The set $`\Lambda(P) = (P \sm l)/{\approx}` is the set of _levels_ of $`P`.
The class of $`s` is denoted $`\lev(s)`.
The group $`\Gamma` acts on $`\Lambda(P)` by $`\lev(s) + j = \lev(\Frob^j s)`, and by
{cref "lem:levels"}[] this makes $`\Lambda(P)` a $`\Gamma`-torsor.
For $`\alpha, \beta \in \Lambda(P)` we write $`\alpha - \beta \in \Gamma` for the element with
$`\alpha = \beta + (\alpha - \beta)`, and $`\alpha \geq \beta` if $`\alpha - \beta \geq 0`.
:::

As explained in {cref "ss:elementwise"}[], the formalization defines only the
differences $`\lev(s) - \lev(t)`:

{docstring MilnorAlgDep.levDiff}

{docstring MilnorAlgDep.levDiff_eq_iff}

From {cref "lem:levels"}[] one gets the calculus of level differences:
$`\lev(s) = \lev(t)` if and only if $`s \approx t` ({name}`levDiff_eq_zero_iff`);
$`\lev(s) - \lev(s) = 0` ({name}`levDiff_self`);
antisymmetry ({name}`levDiff_swap`);
$`(\lev(s) - \lev(t)) + (\lev(t) - \lev(u)) = \lev(s) - \lev(u)`
({name}`levDiff_add_levDiff`);
$`\lev(\Frob^j s) = \lev(s) + j` ({name}`levDiff_frobZ_left`,
{name}`levDiff_frobZ_right`);
and the level of an element only depends on its $`\approx`-class
({name}`SepEquiv.levDiff_left`, {name}`SepEquiv.levDiff_right`).
For the levels of elements of $`V_{L|l}` ({cref "ss:reductions"}[]) one also needs
$`\lev(cs) = \lev(s)` for $`c \in l^\times`, $`\lev(s^N) = \lev(s)` for $`N` prime to $`p`, and
$`\lev(s^{-1}) = \lev(s)` ({name}`levDiff_algebraMap_mul_left`,
{name}`levDiff_pow_left`, {name}`levDiff_inv_left`): in each case the two elements are
$`\approx`-equivalent.

The order on levels has a direct description, which the blueprint states in the proof of
Lemma 6.2:

{docstring MilnorAlgDep.levDiff_nonneg_iff}

_Proof._
If $`\lev(s) - \lev(t) = n \geq 0`, then $`s \approx \Frob^n(t) = t^{p^n}`, so $`s` is separable
over $`l(t^{p^n}) \subset l(t)`.
If $`\lev(s) - \lev(t) = -n < 0` and $`s` is separable over $`l(t)`, put
$`u = \Frob^{-n}(t)`; then $`u \approx s`, so $`u` is separable over $`l(t) = l(u^{p^n})`, which
{name}`not_isSeparable_adjoin_pow_pow` excludes.

# Normalized triples
%%%
tag := "ss:normalized"
%%%

:::defn "3.4" (title := "Normalized triples") (tag := "def:normalized")
Let $`P, Q, R` be three distinct collinear points.
A triple $`(x, y, z)` with $`x \in P \sm l`, $`y \in Q \sm l`, $`z \in R \sm l` is _normalized_
if each of $`x, y, z` is separable algebraic over the field generated over $`l` by the other two.
:::

In Lean the hypothesis on the points is part of the definition, so that a normalized triple
determines its points:

{docstring MilnorAlgDep.IsCollinearTriple +hideFields +hideStructureConstructor}

{docstring MilnorAlgDep.IsNormalized +hideFields +hideStructureConstructor}

The fields of {name}`IsCollinearTriple` `l x y z` are `indep₁₂ : AlgebraicIndependent l ![x, y]`,
`indep₁₃` and `indep₂₃` (the same for the pairs $`(x, z)` and $`(y, z)`), and
`isAlgebraic : IsAlgebraic l⟮x, y⟯ z`; {name}`IsNormalized` `l x y z` extends it by
`isSeparable₁ : IsSeparable l⟮y, z⟯ x`, `isSeparable₂ : IsSeparable l⟮x, z⟯ y` and
`isSeparable₃ : IsSeparable l⟮x, y⟯ z`.
Since the three points are distinct, they span a line, so "collinear" just says that $`z` is
algebraic over $`l(x, y)`.
The definition is symmetric ({name}`IsCollinearTriple.swap₁₂`,
{name}`IsCollinearTriple.swap₂₃`, by the exchange property of the algebraic matroid, and
{name}`IsNormalized.swap₁₂`, {name}`IsNormalized.swap₂₃`), and
{name}`IsCollinearTriple` only depends on the points
({name}`IsCollinearTriple.of_samePoint`).

:::lem "3.5" (title := "Normalized triples") (tag := "lem:normalized")
Let $`P, Q, R` be distinct collinear points.

* *(a)* Normalized triples exist.
* *(b)* If $`(x, y, z)` is normalized, then $`(x', y', z')` is normalized if and only if there is
  $`j \in \Gamma` with $`\lev(x') = \lev(x) + j`, $`\lev(y') = \lev(y) + j` and
  $`\lev(z') = \lev(z) + j`.
:::

Thus the levels of normalized triples form a single orbit of the diagonal action of $`\Gamma` on
$`\Lambda(P) \times \Lambda(Q) \times \Lambda(R)`.
The blueprint calls this orbit, or any of its elements, the _level triple_ of $`(P, Q, R)` and
denotes it by $`\lt(P, Q, R)`.

{docstring MilnorAlgDep.exists_isNormalized}

{docstring MilnorAlgDep.IsNormalized.isNormalized_iff}

In (b) the condition reads
$`\lev(x') - \lev(x) = \lev(y') - \lev(y) = \lev(z') - \lev(z)`.
The level triple is recorded relative to elements $`x, y, z` of the three points, as the shifts
$`(j, k)` such that $`(\lev x, \lev y + j, \lev z + k)` is in the orbit:

{docstring MilnorAlgDep.levelTriple}

{docstring MilnorAlgDep.isNormalized_levelTriple}

{docstring MilnorAlgDep.levelTriple_eq_of_isNormalized}

For example, the integer $`c(u, w)` of Step A is the first entry of
{name}`levelTriple` `l p a b d`, where $`a, b, d` represent $`\psi(u)`, $`\psi(w)`,
$`\psi(u + w)`.

_Proof of (b) (as formalized)._
"If": being normalized is invariant under a diagonal twist by $`\Frob^j`
({name}`IsNormalized.frobZ_iff`), and it only depends on the $`\approx`-classes:

{docstring MilnorAlgDep.IsNormalized.of_sepEquiv}

Indeed, if $`y' \approx y` and $`z' \approx z`, then $`y, z` lie in the model of $`(y', z')`
({name}`SepEquiv.mem_model`), hence so does $`x`, which is separable over $`l(y, z)`, and
then so does $`x' \approx x`; that is, $`x'` is separable over $`l(y', z')`.

"Only if": let $`E` be the model of $`(x, y)`; by (S2), $`dx, dy` is a basis of $`\Omega_E`, and
$`z \in E`.
Since each of $`x, y, z` is separable over the field generated by the other two, (S2) gives
$`dx \in E\,dy + E\,dz` and $`dy \in E\,dx + E\,dz`
({name}`modelD_mem_span_pair_of_isSeparable`), so
$$`dx,\ dy,\ dz \text{ are pairwise linearly independent in } \Omega_E. \qquad \text{(eq:pairwise)}`
Let $`(x', y', z')` be normalized, with level differences $`a, b, c` with respect to
$`x, y, z`.
By the "if" part, $`(\Frob^a x, \Frob^b y, \Frob^c z)` is normalized, and after a diagonal twist
we may assume $`a, b, c \geq 0` and $`\min(a, b, c) = 0`; we must show $`a = b = c = 0`.
The three elements $`x^{p^a}, y^{p^b}, z^{p^c}` lie in $`E`, and by (S2) the differential of each
lies in the span of the differentials of the other two.
The differential of $`x^{p^a}` is $`dx` if $`a = 0` and $`0` if $`a > 0`, and similarly for the
others.
If exactly one of $`a, b, c` is zero, a non-zero differential lies in the span of two zeros; if
exactly two are zero, two of $`dx, dy, dz` are proportional, contradicting (eq:pairwise)
({name}`eq_zero_of_isNormalized_pow_pow`).
This is the blueprint's argument, with the partial derivatives of the irreducible relation
replaced by the span statements of (S2).

_Proof of (a) (as formalized)._
The blueprint takes the irreducible relation $`f` of $`(x, y, z)` and writes
$`f = g(X^{p^a}, Y^{p^b}, Z^{p^c})` with $`a, b, c` maximal.
The formal proof works in models instead.
Let $`x, y, z` be elements of the three points and let $`E` be the model of $`(x, y)`, with basis
$`dx, dy` of $`\Omega_E`.
Since $`z` is algebraic over $`l(x, y)`, some $`z_0 = \Frob^k(z)` lies in $`E` and has
$`dz_0 \neq 0` ({name}`exists_frobZ_mem_model_modelD_ne_zero`, from {cref "lem:model"}[] (c) and
(S3)).
Write $`dz_0 = \alpha\, dx + \beta\, dy` with $`\alpha, \beta \in E`.

* If $`\alpha \neq 0` and $`\beta \neq 0`, then $`dx, dy, dz_0` are pairwise linearly independent,
  and $`(x, y, z_0)` is normalized by {name}`isNormalized_of_linearIndependent_modelD`.
* If $`\beta = 0`, then $`\alpha \neq 0`, and we twist $`y` instead.
  Let $`E' \subset E` be the model of $`(x, z_0)` and $`y_0 = \Frob^c(y)` a model generator of
  $`Q_y` in $`E'`, so $`dy_0 = \gamma\, dx + \delta\, dz_0 \neq 0` in $`\Omega_{E'}`.
  Pushed forward to $`\Omega_E`, where $`dz_0 = \alpha\, dx`, this gives
  $`dy_0 = (\gamma + \delta\alpha)\, dx`.
  Now $`c > 0`: for $`c = 0` this would put $`dy` in $`E\,dx`, and for $`c < 0` we would have
  $`y = y_0^{p^{-c}}`, so $`dy = 0`; both contradict the fact that $`dy` is a basis vector of
  $`\Omega_E`.
  So $`y_0 = y^{p^c}` has $`dy_0 = 0` in $`\Omega_E`, that is, $`\gamma + \delta\alpha = 0`.
  As $`(\gamma, \delta) \neq 0` and $`\alpha \neq 0`, both $`\gamma` and $`\delta` are non-zero, so
  $`dx, dz_0, dy_0` are pairwise linearly independent in $`\Omega_{E'}`, and $`(x, y_0, z_0)` is
  normalized ({name}`exists_isNormalized_of_modelD_mem_span`).
* If $`\alpha = 0`, the previous case with the roles of $`x` and $`y` exchanged gives a normalized
  triple $`(\Frob^c x, y, z_0)`, and a diagonal twist by $`\Frob^{-c}` restores $`x`.

No injectivity of $`\Omega_{E'} \to \Omega_E` is needed.

Chapter 6 also uses that $`(x, y, xy)` is normalized for algebraically independent $`x, y`
({name}`isNormalized_mul`): $`xy` lies in $`l(x, y)`, $`x` in $`l(y, xy)` and $`y` in
$`l(x, xy)`.
