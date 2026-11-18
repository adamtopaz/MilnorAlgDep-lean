import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite
open MilnorAlgDep

set_option pp.rawOnError true

#doc (Manual) "Models and the lax differential map" =>
%%%
tag := "sec:models"
%%%

We keep the assumptions of {ref "sec:levels"}[Chapter 3].
A transcendence basis $`A` of $`L|l` determines a non-perfect subfield, the model $`L_A`, whose
Kähler differentials $`\Omega_A` see exactly one level of each point.
This chapter relates levels to lines in $`\Omega_A`.
In the language of {cref "ss:elementwise"}[], the model level $`\lambda_A(P)` is replaced by the
height of an element, $`\hgt(y) = \lev(y) - \lambda_A(Q_y)`.

# Models
%%%
tag := "ss:models"
%%%

:::defn "4.1" (title := "Models") (tag := "defn:model")
Let $`A` be a transcendence basis of $`L|l`.
The _model_ attached to $`A` is the field
$$`L_A = \{ y \in L : y \text{ is separable algebraic over } l(A) \},`
and we put $`\Omega_A = \Omega_{L_A|l}`.
:::

The formal definition allows any family $`B`, because the proofs in
{ref "sec:levels"}[Chapter 3] use the models of one and two elements; each result assumes what it
needs (`AlgebraicIndependent l B` or `IsTranscendenceBasis l B`).

{docstring MilnorAlgDep.model}

The differential $`d \colon L_B \to \Omega_B` is extended to a total function on $`L`:

{docstring MilnorAlgDep.modelD}

Statements about {name}`modelD` therefore also assume $`y \in L_B` when they need it.
On $`L_B` it satisfies the usual rules ({name}`modelD_add`, {name}`modelD_mul`), and
$`d(y^p) = 0` ({name}`modelD_pow_char`).

:::lem "4.2" (tag := "lem:model")
* *(a)* $`\{ da : a \in A \}` is a basis of the $`L_A`-vector space $`\Omega_A`, and (S3) applies
  to $`E = L_A`.
* *(b)* If $`j \in \Gamma_{\geq 0}` and $`y \in L` is separable algebraic over $`\Frob^j(L_A)`, then
  $`y \in \Frob^j(L_A)`.
* *(c)* $`L = \bigcup_{j \in \Gamma_{\geq 0}} \Frob^{-j}(L_A)`.
:::

{docstring MilnorAlgDep.modelBasis}

{docstring MilnorAlgDep.mem_model_of_isSeparable}

{docstring MilnorAlgDep.exists_pow_pow_mem_model}

_Proof._
(a) $`L_B` is separable algebraic over $`l(B)` by definition, so (S2) applies to $`E = L_B` and
the family $`B` viewed in $`L_B` ({name}`algebraicIndependent_restrictFamily_model`,
{name}`isSeparable_adjoin_restrictFamily_model`); and $`l` is relatively algebraically closed
in $`L_B` because it is so in $`L`, so (S3) applies as well.
(b) If $`y` is separable over a subfield $`K \subset L_B`, then it is separable over $`L_B`, and
$`L_B` is separable over $`l(B)`, so $`y` is separable over $`l(B)`.
The formal statement takes any intermediate field $`K \subset L_B`, which also covers the use of
(b) in the proof of {cref "lem:pointsmodel"}[]; the case $`j > 0` follows by applying
$`\Frob^{-j}`.
(c) If $`y` is algebraic over $`l(B)`, the separable contraction of its minimal polynomial shows
that $`y^{p^n}` is separable over $`l(B)` for some $`n`
({name}`exists_isSeparable_pow_pow`).
For a transcendence basis this is (c), in the form $`\Frob^{-j}(y) \in L_B` for some $`j`
({name}`exists_frobZ_neg_mem_model`).

Two facts about differentials in a model hold for any family $`B`: the separability criterion
({cref "ss:sepcrit"}[]) and the lax property in its general form ({cref "lem:lax"}[] below).

# Points in a model
%%%
tag := "ss:pointsmodel"
%%%

:::lem "4.3" (title := "Points in a model") (tag := "lem:pointsmodel")
Let $`P` be a point.
There is a unique level $`\lambda_A(P) \in \Lambda(P)` such that for $`y \in P \sm l`:

* *(a)* $`y \in \Frob^j(L_A)` if and only if $`\lev(y) \geq \lambda_A(P) + j` ($`j \in \Gamma`);
* *(b)* $`y \in L_A` and $`dy \neq 0` in $`\Omega_A` if and only if $`\lev(y) = \lambda_A(P)`;
* *(c)* the line $`L_A\, dy \subset \Omega_A` is the same for all $`y` as in (b).
:::

:::defn "4.4" (title := "Model level, height, line") (tag := "defn:height")
For a point $`P` we call $`\lambda_A(P)` the _model level_ of $`P`, an element $`y \in P` with
$`\lev(y) = \lambda_A(P)` a _model generator_ of $`P`, and
$$`\omega_A(P) = L_A\, dy \subset \Omega_A \qquad (y \text{ a model generator of } P)`
the _line of_ $`P`.
For $`\alpha \in \Lambda(P)` the element $`\hgt_A(\alpha) = \alpha - \lambda_A(P) \in \Gamma` is the
_height_ of $`\alpha`.
:::

So an element of $`P \sm l` of height $`j` is $`\Frob^j` of a model generator, up to the
relation $`\approx`.

The formalization reverses the order: it defines the height of an element first, by the property
(a), and derives the rest.
From now on $`B` is a transcendence basis of $`L|l`.

{docstring MilnorAlgDep.hgt}

{docstring MilnorAlgDep.frobZ_neg_mem_model_iff}

{docstring MilnorAlgDep.hgt_eq_zero_iff}

{docstring MilnorAlgDep.span_modelD_eq_of_hgt_eq_zero}

The relation with levels is:

{docstring MilnorAlgDep.hgt_sub_hgt}

In other words, $`\lev(y) - \hgt(y)` does not depend on the choice of $`y \in P \sm l`: this
common value is the model level $`\lambda_B(P)`, and its uniqueness in {cref "lem:pointsmodel"}[]
is automatic.
A model generator is an element of height $`0`, and every point has the canonical model generator
$`\Frob^{-\hgt(y)}(y)` ({name}`hgt_frobZ_neg_hgt`); the line of the point is defined with it:

{docstring MilnorAlgDep.omega}

{docstring MilnorAlgDep.omega_eq_of_samePoint}

The line is spanned by a non-zero vector ({name}`omega_ne_bot`), it is $`L_B\, dy` for every model
generator $`y` ({name}`omega_eq_span_of_hgt_eq_zero`), and the elements of $`B` are model
generators ({name}`hgt_apply`, {name}`omega_apply`).

_Proof of {cref "lem:pointsmodel"}[] (as formalized)._

1. _The height._
   For $`y \in L` let $`S(y) = \{ j \in \ZZ : \Frob^{-j}(y) \in L_B \}`.
   This set is downward closed, because $`L_B` is stable under $`\Frob`
   ({name}`frobZ_neg_mem_model_of_le`), and non-empty by {cref "lem:model"}[] (c).
   If $`y` is transcendental, it is bounded above ({name}`bddAbove_frobZ_neg_mem_model`): pick
   $`j_0 \in S(y)`; by (S3) for $`L_B` the element $`\Frob^{-j_0}(y) \in L_B \sm l` is not a
   $`p^n`-th power in $`L_B` for some $`n` ({name}`not_forall_exists_pow_pow_eq`), so
   $`j_0 + n \notin S(y)`.
   Hence $`\hgt(y) = \max S(y)`, and (a) holds by definition.
2. _Part (b)._
   By the kernel statement of (S3) for $`L_B`, an element $`y \in L_B` has $`dy = 0` if and only if
   $`y = w^p` with $`w \in L_B`, that is, if and only if $`1 \in S(y)`.
   So $`y \in L_B` and $`dy \neq 0` if and only if $`\max S(y) = 0`.
3. _Heights and levels._
   Two facts replace the blueprint's case analysis.
   The height is constant on $`\approx`-classes ({name}`hgt_eq_of_sepEquiv`): if $`s \approx t`
   then $`\Frob^{-j}(s) \approx \Frob^{-j}(t)`, and if one of two $`\approx`-equivalent elements
   lies in $`L_B`, so does the other, by {cref "lem:model"}[] (b).
   And $`\hgt(\Frob^j y) = \hgt(y) + j` directly from the definition ({name}`hgt_frobZ`).
   For $`y, y'` in one point, $`y \approx \Frob^{\lev(y) - \lev(y')}(y')` by {cref "lem:levels"}[],
   so $`\hgt(y) = \hgt(y') + \lev(y) - \lev(y')`.
4. _Part (c)._
   Two model generators $`y, y'` of $`P` have the same height, hence the same level by step 3, so
   $`y \approx y'`.
   If $`s \approx t` and $`s \in L_B`, then $`L_B\, ds = L_B\, dt`
   ({name}`SepEquiv.span_modelD_eq`): by (S2) in the model $`L_{(t)}`, $`ds = c\, dt` with
   $`c \in L_{(t)} \subset L_B`, and symmetrically.

The factor $`c` in step 4 is separable algebraic over $`l(t)`, so it lies in the point $`Q_t`
({name}`exists_modelD_eq_smul_of_isSeparable`); this is how Chapter 6 shows
$`\mu(x) \in Q_x`.

# The lax property
%%%
tag := "ss:lax"
%%%

:::lem "4.5" (title := "Lax property") (tag := "lem:lax")
If $`P_1, \dots, P_m` are distinct points with $`\rk\{P_1, \dots, P_m\} < m`, then the lines
$`\omega_A(P_1), \dots, \omega_A(P_m)` are linearly dependent.
:::

The proof is the general form of {cref "ss:lax-general"}[], applied to $`E = L_B`; in a model it
reads:

{docstring MilnorAlgDep.algebraicIndependent_of_linearIndependent_modelD}

For points:

{docstring MilnorAlgDep.not_linearIndependent_modelD_of_not_algebraicIndependent}

_Proof._
Let $`y_k^0 = \Frob^{-\hgt(y_k)}(y_k)` be the canonical model generators.
If their differentials were linearly independent in $`\Omega_B`, the $`y_k^0` would be
algebraically independent, and so would the $`y_k`, because each $`y_k` is algebraic over
$`l(y_k^0)` and conversely ({name}`algebraicIndependent_of_isAlgebraic_adjoin`).

The formal statement covers any algebraically dependent family of transcendental elements: the
points need not be distinct.
The lax property is used in the following form, which the blueprint calls _propagation_: if a
point $`X` is collinear with $`P, Q` and also with $`R, S`, where
$`\omega_A(P) \neq \omega_A(Q)`, $`\omega_A(R) \neq \omega_A(S)` and the planes
$`\omega_A(P) + \omega_A(Q)` and $`\omega_A(R) + \omega_A(S)` are distinct, then $`\omega_A(X)` is
the intersection of these two planes.

{docstring MilnorAlgDep.omega_le_sup_of_isAlgebraic}

{docstring MilnorAlgDep.omega_eq_inf_of_isAlgebraic}

_Proof._
If $`x` is algebraic over $`l(q, r)`, the family $`(x, q, r)` is algebraically dependent, so by the
lax property the differentials of the model generators of $`Q_x, Q_q, Q_r` are linearly
dependent.
Those of $`Q_q` and $`Q_r` are linearly independent, since they span distinct lines; so the first
one lies in the plane they span.
A line contained in two distinct planes is their intersection
({name}`span_singleton_eq_inf_of_le`, a dimension count).
No distinctness of $`X` from the other points is needed.
Only the first half, the inclusion, is used in {ref "sec:quadrangle"}[Chapter 5].

When $`\Gamma \neq 0` the converse of {cref "lem:lax"}[] fails: if $`a, b \in A`, then
$`Q_a` and $`Q_{a + \Frob(b)}` are distinct points with the same line $`L_A\, da`.
The next lemma describes exactly what happens on a collinear triple.

# The trichotomy
%%%
tag := "ss:trichotomy"
%%%

:::lem "4.6" (title := "Trichotomy") (tag := "lem:trichotomy")
Let $`P, Q, R` be distinct collinear points and let $`(i, j, k) \in \Gamma^3` be the heights of a
level triple $`(\alpha, \beta, \gamma)` of $`(P, Q, R)`.

* *(a)* If $`i < j`, then $`k = i` and $`\omega_A(R) = \omega_A(P)`.
* *(b)* If $`i = j` and $`\omega_A(P) \neq \omega_A(Q)`, then $`k = i`, and $`\omega_A(R)` is
  contained in $`\omega_A(P) + \omega_A(Q)` and different from $`\omega_A(P)` and $`\omega_A(Q)`.
* *(c)* If $`i = j` and $`\omega_A(P) = \omega_A(Q)`, then $`k \geq i`.
* *(d)* Conversely, if $`\omega_A(P), \omega_A(Q), \omega_A(R)` are pairwise distinct, then
  $`(\lambda_A(P), \lambda_A(Q), \lambda_A(R))` is a level triple of $`(P, Q, R)`, i.e.
  $`i = j = k`.
:::

In Lean a level triple of $`(P, Q, R)` is given by a normalized triple $`(x, y, z)`, its heights
are the heights $`(\hgt x, \hgt y, \hgt z)` of its elements, and $`\omega_A(P)` is
{name}`omega` `l p B x`.
The case $`i > j` is (a)–(c) with $`P` and $`Q` exchanged ({name}`IsNormalized.swap₁₂`).

{docstring MilnorAlgDep.IsNormalized.trichotomy_lt}

{docstring MilnorAlgDep.IsNormalized.trichotomy_eq_of_omega_ne}

{docstring MilnorAlgDep.IsNormalized.hgt_le_of_hgt_le}

The blueprint's statement of (c) is {name}`IsNormalized.trichotomy_eq_of_omega_eq`, which
is deduced from it.
Part (d) has two forms: model generators with distinct lines form a normalized triple, and the
elements of a normalized triple with distinct lines have equal heights.

{docstring MilnorAlgDep.isNormalized_of_hgt_eq_zero}

{docstring MilnorAlgDep.IsNormalized.hgt_eq_of_omega_ne}

_Proof (as formalized)._
A diagonal twist $`(x, y, z) \mapsto (\Frob^{-i} x, \Frob^{-i} y, \Frob^{-i} z)` preserves
normalized triples ({name}`IsNormalized.frobZ_iff`) and lines ({name}`omega_frobZ`), and shifts all
heights by $`-i` ({name}`hgt_frobZ`); so in (a)–(c) we may assume $`i = 0 \leq j`.
Then $`x` is a model generator, $`y \in L_B` by {cref "lem:pointsmodel"}[] (a), and $`z \in L_B` by
{cref "lem:model"}[] (b), being separable over $`l(x, y) \subset L_B`.
Since each of $`x, y, z` is separable over the field generated by the other two, (S2) in $`L_B`
shows that each of $`dx, dy, dz` lies in the span of the other two
({name}`IsNormalized.modelD_mem_sup`).
This replaces the blueprint's relation $`f_X\, dx + f_Y\, dy + f_Z\, dz = 0` with non-zero
coefficients, which came from the irreducible relation and Lemma 3.1.
By {cref "lem:pointsmodel"}[] (b), $`dx \neq 0`, and $`dy = 0` if and only if $`j > 0`.

(a) If $`j > 0`, then $`dy = 0`, so $`dx \in L_B\, dz`.
As $`dx \neq 0`, also $`dz \neq 0` and $`L_B\, dz = L_B\, dx`.
So $`z` is a model generator, $`k = 0`, and $`\omega_A(R) = L_B\, dz = L_B\, dx = \omega_A(P)`.

(b) If $`j = 0` and $`\omega_A(P) \neq \omega_A(Q)`, then $`dx, dy` are non-zero and span distinct
lines.
If $`dz = 0`, then $`dx \in L_B\, dy`, which is impossible; so $`z` is a model generator, $`k = 0`,
and $`\omega_A(R) = L_B\, dz \subset L_B\, dx + L_B\, dy`.
If $`\omega_A(R) = \omega_A(P)`, then $`dy \in L_B\, dx + L_B\, dz = L_B\, dx`, which is impossible;
similarly $`\omega_A(R) \neq \omega_A(Q)`.

(c) $`z \in L_B` means $`k \geq 0 = i`.
This only used $`j \geq 0`: so $`i \leq j` implies $`i \leq k`, and the hypotheses $`i = j` and
$`\omega_A(P) = \omega_A(Q)` of the blueprint are not needed.

(d) Let $`x, y, z` be model generators of $`P, Q, R` with pairwise distinct lines.
Then $`dx, dy, dz` are non-zero and pairwise linearly independent
({name}`linearIndependent_pair_of_span_singleton_ne`), so $`(x, y, z)` is normalized by
{name}`isNormalized_of_linearIndependent_modelD`: for instance $`z` is separable over $`l(x, y)`
by the separability criterion, because $`dx, dy` are linearly independent.
So $`(\lambda_B(P), \lambda_B(Q), \lambda_B(R))` is a level triple.
If $`(x, y, z)` is any normalized triple of the three points, compare it with the normalized triple
of canonical model generators $`(x_0, y_0, z_0)`: by {cref "lem:normalized"}[] (b),
$`\lev x - \lev x_0 = \lev y - \lev y_0 = \lev z - \lev z_0`, and these differences are
$`\hgt x, \hgt y, \hgt z`.
(The blueprint argues with Lemma 3.1 (b), (c) for the irreducible relation of $`(x, y, z)`.)
