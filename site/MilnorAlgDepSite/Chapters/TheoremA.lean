import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite
open MilnorAlgDep

set_option pp.rawOnError true

#doc (Manual) "Proof of Theorem A" =>
%%%
tag := "sec:main"
%%%

The proof of {cref "thm:A"}[] proceeds in three steps.
Step A shows that $`\psi(x)` and $`\psi(1-x)` have the same level; Step B extracts from
$`\psi` a function $`t` on $`K` and shows that it is a field embedding $`\tau`; Step C identifies
$`\psi` with a rational multiple of $`[\tau]`.

In the formalization the two characteristics are treated separately.
In characteristic $`0` there are no levels: Step A is empty, the adapted model is $`L` itself,
and the logarithmic derivative $`\dlog \colon V_{L|l} \to \Omega_{L|l}` is injective.
Step B is proved once, for an abstract homomorphism $`\Delta` satisfying four hypotheses, and
used in both characteristics.
The characteristic $`0` proof is complete and consists of {ref "ss:reductions"}[Section 6.1],
{ref "ss:model0"}[Section 6.3.1], {ref "ss:stepB"}[Sections 6.4], {ref "ss:embedding"}[6.5],
{ref "ss:stepC0"}[6.6.1] and {ref "ss:end"}[6.7].
The parts marked "characteristic p" are being formalized; their Lean counterparts do not exist
yet.

# Reductions and notation
%%%
tag := "ss:reductions"
%%%

The homomorphism $`\psi` extends uniquely to $`(K^i)^\times` by
$`\psi(x) = p_K^{-j} \psi(x^{p_K^j})`, where $`p_K` is the characteristic exponent of $`K`; the
extension satisfies (A1)–(A4) with $`k` replaced by its perfect closure $`k^i \subset K^i`, and
$`k^i \cap K = k` by (A1).
Also $`V_{L|l} = V_{L^i|l^i}` ({ref "ss:perfectClosure"}[Section 2.3.1]).
So we may and do assume that $`K` and $`L` are perfect; then $`k` is perfect.
Note that at this stage $`K` and $`L` may have different characteristics; until this is excluded
({cref "prop:tau"}[]), $`\Frob` always denotes the Frobenius of $`L` and we make no use of the
Frobenius of $`K`.
We write $`p` for the characteristic exponent of $`L`, $`\Gamma = \Gamma(L)`, and $`V = V_{L|l}`.
By (A1), $`\psi(-1) = 0` and $`\psi(cx) = \psi(x)` for $`c \in k^\times`.
For every $`x \in K \sm k` we have $`1 - x \notin k`, and $`Q_{1-x} = Q_x` by (A2) and (V3).

In Lean, $`K^i` is any perfect field `Ki` over $`K` such that `algebraMap K Ki` is
$`q`-radical (every element has a $`q^n`-th power in $`K`), where $`q` is the characteristic
exponent of $`K`, not of $`L`.

{docstring MilnorAlgDep.extendPsi}

The extension is well defined because the target is a $`\QQ`-vector space.
It satisfies (A1) with $`k^i` = {name}`perfectClosureIn` `k Ki q`
({name}`extendPsi_eq_zero_iff`), and $`k^i \cap K = k`
({name}`algebraMap_mem_perfectClosureIn_iff`); (A3) is inherited
({name}`extendPsi_A3`); and (A2) holds because $`(x + y)^{q^n} = x^{q^n} + y^{q^n}`:

{docstring MilnorAlgDep.extendPsi_A2}

The reduction to perfect $`K` is only needed in positive characteristic: the characteristic
$`0` proof below works for an arbitrary field $`K` (which turns out to have characteristic $`0`).
The reduction to perfect $`L` is {name}`theoremA_aux`, which applies the perfect case
to $`L^i`, $`l^i` and $`\psi` followed by the comparison map
{name}`V.toPerfectClosure`.
The reduction to perfect $`K` is:

{docstring MilnorAlgDep.theoremA_perfect_of_isPRadical}

_Characteristic p (placeholder)._
For $`v \in V \sm 0` with representative $`(N, a)` the blueprint puts
$`\lev(v) = \lev(a) \in \Lambda(Q_v)`, and uses the consequence
$$`\psi(x + y) = \psi(y) + \psi\bigl(1 - (-x/y)\bigr), \qquad
  \psi\bigl(1 - (-x/y)\bigr) \in G_{Q_{x/y}} \sm 0,`
of (A1) and (A2), for $`x, y \in K^\times` with $`x + y \neq 0` and $`x/y \notin k`.
In particular, if $`x, y` are $`\psi`-independent then $`Q_x, Q_y, Q_{x+y}` are three distinct
collinear points.
These are used only in Step A.

# Step A: the levels of ψ(x) and ψ(1 − x)
%%%
tag := "sec:stepA"
%%%

_This section is needed only in positive characteristic; it will be written when its
formalization exists._

:::prop "6.1" (tag := "prop:levels")
For every $`x \in K \sm k` we have $`\lev \psi(1-x) = \lev \psi(x)`.
:::

If $`\Gamma = 0` there is nothing to prove.

_Formal counterpart (placeholder):_ `MilnorAlgDep/CharP/StepA.lean` (work package WP-P4).

# The adapted model
%%%
tag := "ss:model"
%%%

Let $`x_1, \dots, x_d` be as in (A3), choose representatives $`(N_i, a_i)` of $`\psi(x_i)`, and
extend $`a_1, \dots, a_d` to a transcendence basis $`A` of $`L|l`.
Put
$$`F = L_A, \qquad \Omega = \Omega_A = \Omega_{L_A|l},`
and for $`v \in V \sm 0` let $`\hgt(v) = \hgt_A(\lev v) \in \Gamma` be its height
({ref "sec:models"}[Chapter 4]).
If $`\Gamma = 0` then $`F = L`, $`\Omega = \Omega_{L|l}` and all heights are $`0`.
Let
$$`W = \{0\} \cup \{ v \in V \sm 0 : \hgt(v) \geq 0 \}.`

:::lem "6.4" (tag := "lem:W")
* *(a)* $`W` is a subgroup of $`V`, and there is a homomorphism $`\dlog_A \colon W \to \Omega`
  such that $`\dlog_A(v) = N^{-1}\, da/a` for every representative $`(N, a)` of
  $`v \in W \sm 0`.
* *(b)* For $`v \in W \sm 0`: $`\dlog_A(v) \neq 0` if and only if $`\hgt(v) = 0`, and then
  $`F \cdot \dlog_A(v) = \omega_A(Q_v)`.
* *(c)* If $`\Gamma = 0`, then $`W = V` and $`\dlog_A` is injective.
  If $`\Gamma = \ZZ`, then $`\ker(\dlog_A) = pW`, $`V = \bigcup_j p^{-j} W` and
  $`\bigcap_j p^j W = 0`.
:::

Here $`\omega_A(Q)` is the line of the point $`Q` in $`\Omega`; for $`\Gamma = 0` it is
$`L\, da` for any $`a \in Q \sm l`.
Put
$$`K_0 = \{0\} \cup \psi^{-1}(W), \qquad \Delta = \dlog_A \circ \psi \colon K_0^\times \to \Omega.`
An element $`x \in K_0^\times` is _primitive_ if $`\Delta(x) \neq 0`, i.e. $`x \notin k` and
$`\hgt \psi(x) = 0`.
Two primitive elements $`x, y` are _transverse_ if $`\Delta(x), \Delta(y)` are linearly
independent; by {cref "lem:W"}[] this implies $`Q_x \neq Q_y`, so transverse elements are
$`\psi`-independent.

:::lem "6.5" (tag := "lem:K0")
* *(a)* $`K_0` is a subfield of $`K` containing $`k`.
  If $`\Gamma = 0`, then $`K_0 = K` and every $`x \in K \sm k` is primitive.
* *(b)* If $`x \in K_0 \sm k` then $`1 - x \in K_0 \sm k`, and $`1 - x` is primitive if and only
  if $`x` is.
  If $`x` is primitive, then
  $$`\Delta(1-x) = \mu(x)\, \Delta(x) \qquad \text{for a unique } \mu(x) \in F^\times,
    \text{ and } \mu(x) \in Q_x.`
* *(c)* $`x_1, \dots, x_d` are primitive and $`\Delta(x_1), \dots, \Delta(x_d)` are linearly
  independent.
  For any three lines in $`\Omega` there is a primitive $`z` such that $`F \Delta(z)` is none of
  them.
:::

By (c), any two primitive elements are transverse to a common third one.

## Characteristic 0
%%%
tag := "ss:model0"
%%%

The formal proof of the characteristic $`0` case bundles the data and hypotheses (A1)–(A3), with
the two elements of (A3) made explicit:

{docstring MilnorAlgDep.Char0Hyp}

_The logarithmic derivative ({cref "lem:W"}[] for $`\Gamma = 0`)._
The map $`a \mapsto a^{-1} da` is a homomorphism $`L^\times \to \Omega_{L|l}` vanishing on
$`l^\times`, and $`\Omega_{L|l}` is a $`\QQ`-vector space, so it factors through
$`V_{L|l} = (L^\times / l^\times) \otimes \QQ`.

{docstring MilnorAlgDep.dlog}

The formula $`\dlog(v) = N^{-1}\, da/a` for any representative is
{name}`dlog_of_nsmul_eq_cls`.
If $`\dlog(v) = 0` and $`Nv = [a]`, then $`da = 0`, so $`a` is algebraic over $`l`
({name}`kaehler_D_eq_zero_iff_isAlgebraic`), hence $`a \in l` and $`v = 0` by (V1):

{docstring MilnorAlgDep.dlog_injective}

Combining (V3) with the characteristic $`0` criterion
{name}`algebraicIndependent_iff_linearIndependent_kaehler_D` gives the fact on which
the whole characteristic $`0` proof rests:

{docstring MilnorAlgDep.vAlgIndep_iff_linearIndependent_dlog}

For $`\Gamma = 0`, part (b) of {cref "lem:W"}[] is used in the following form: elements of $`V`
with the same point have proportional logarithmic derivatives, with a factor in the point.
(This is the argument for $`\mu(x) \in Q_x` in the blueprint's proof of {cref "lem:K0"}[] (b).)

{docstring MilnorAlgDep.exists_mem_pointV_dlog_eq_smul}

_Proof._
Let $`(N, a)` and $`(M, b)` be representatives of $`v` and $`w`, so $`b \in Q_a`.
In characteristic $`0` the point $`Q_a` is separable algebraic over $`l(a)`, so by (S2)
$`\Omega_{Q_a|l}` is free of rank one with basis $`da`; hence $`db = c\, da` in
$`\Omega_{Q_a|l}` with $`c \in Q_a`, and pushing forward along
$`\Omega_{Q_a|l} \to \Omega_{L|l}` gives the same identity in $`\Omega_{L|l}`
({name}`exists_mem_point_D_eq_smul`).
No injectivity of $`\Omega_{Q_a|l} \to \Omega_{L|l}` is needed.
Then $`\dlog w = \frac{1}{M} \frac{db}{b} = \frac{c\,N a}{M b} \dlog v`.

_The homomorphism $`\Delta` ({cref "lem:K0"}[] for $`\Gamma = 0`)._
Here $`K_0 = K` and $`\Delta = \dlog \circ \psi` is
{name}`Char0Hyp.Δhom`.
Since $`\dlog` is injective, $`\Delta(x) = 0` if and only if $`x \in k`, which is part (a):

{docstring MilnorAlgDep.Char0Hyp.data_Δ_eq_zero_iff}

For part (b), let $`x \notin k`.
Then $`1 - x \notin k`, and $`\psi(x), \psi(1-x)` are non-zero and dependent by (A2); by
{name}`vAlgIndep_iff_linearIndependent_dlog` their images under $`\dlog` are
proportional ({name}`Char0Hyp.Δhom_one_sub_mem_span`), and by
{name}`exists_mem_pointV_dlog_eq_smul`, applied with $`Q_{1-x} = Q_x`, the factor
lies in $`Q_x`:

{docstring MilnorAlgDep.Char0Hyp.μ_mem_pointV}

For part (c), $`\Delta(x_1), \Delta(x_2)` are linearly independent by
{name}`vAlgIndep_iff_linearIndependent_dlog`.
The elements $`x_1 x_2^n`, $`n \geq 0`, have $`\Delta(x_1 x_2^n) = \Delta(x_1) + n\Delta(x_2)`,
and a line contains at most one of these vectors (characteristic $`0`), so all but three of them
avoid three given lines ({name}`exists_add_smul_notMem_span`):

{docstring MilnorAlgDep.Char0Hyp.exists_Δhom_notMem_span}

These are the hypotheses of the abstract Step B ({ref "ss:stepB"}[Section 6.4]), with $`F = L`
and $`\Omega = \Omega_{L|l}`: (H0) is $`\psi(-1) = 0`, (H1) is "$`x \in k` if and only if
$`1 - x \in k`", (H2) is part (b) and (H3) is part (c).

{docstring MilnorAlgDep.Char0Hyp.data}

## Characteristic p
%%%
tag := "ss:modelP"
%%%

_Placeholder._
The model $`L_A`, the height, and the proofs of {cref "lem:W"}[] and {cref "lem:K0"}[] for
$`\Gamma = \ZZ` (which use {cref "prop:levels"}[]) will be described here.

_Formal counterpart (placeholder):_ `MilnorAlgDep/CharP/AdaptedModel.lean` (work package WP-P5).

# Step B: the functions μ and t
%%%
tag := "ss:stepB"
%%%

Step B only uses a few properties of $`\Delta`, and the formalization proves it in that
generality.
Let $`K_0` and $`F` be fields, $`\Omega` an $`F`-vector space and
$`\Delta \colon K_0^\times \to \Omega` a homomorphism; call $`x` primitive if $`\Delta(x) \neq 0`
and $`x, y` transverse if $`\Delta(x), \Delta(y)` are linearly independent.
Assume:

* *(H0)* $`\Delta(-1) = 0`;
* *(H1)* for $`x \neq 0, 1`: $`x` is primitive if and only if $`1 - x` is;
* *(H2)* for primitive $`x \neq 1`: $`\Delta(1-x) \in F\, \Delta(x)`;
* *(H3)* for any $`v_1, v_2, v_3 \in \Omega` there is $`z` with
  $`\Delta(z) \notin F v_1 \cup F v_2 \cup F v_3`.

In the blueprint's setting (H1) and (H2) are {cref "lem:K0"}[] (b) together with $`\Delta = 0`
on $`k^\times`, (H3) is {cref "lem:K0"}[] (c), and (H0) holds because $`\psi(-1) = 0`.
(H0) is assumed separately: it follows from $`2\Delta(-1) = \Delta(1) = 0` if $`2` is invertible
in $`F`, but a priori $`K_0` and $`F` may have different characteristics.
Nothing beyond (H0)–(H3) is needed.

{docstring MilnorAlgDep.StepBData}

The homomorphism is a total function on $`K_0` with $`\Delta(0) = 0`, so "primitive" is just
`Δ x ≠ 0`, which implies $`x \neq 0, 1`; the constructor
{name}`StepBData.ofAddMonoidHom` builds this data from a homomorphism
`Additive K₀ˣ →+ Ω`.
For primitive $`x` define $`\mu(x)` by $`\Delta(1-x) = \mu(x) \Delta(x)` (by (H1) and (H2)) and
put
$$`t(x) = \frac{\mu(x)}{\mu(x) - 1}.`

{docstring MilnorAlgDep.StepBData.μ}

{docstring MilnorAlgDep.StepBData.t}

:::lem "6.6" (title := "One variable") (tag := "lem:onevar")
Let $`x` be primitive.
Then $`1-x` and $`1/x` are primitive,
$$`\mu(1-x) = \mu(x)^{-1}, \qquad \mu(1/x) = 1 - \mu(x), \qquad \mu(x) \neq 1,`
and the element $`t(x) \in F \sm \{0, 1\}` satisfies $`t(1-x) = 1 - t(x)` and
$`t(1/x) = 1/t(x)`.
In the setting of {ref "ss:model"}[Section 6.3], moreover $`t(x) \in Q_x`.
:::

_Proof._
$`1-x` is primitive by (H1), and $`1/x` is primitive because $`\Delta(1/x) = -\Delta(x)`.
From $`\Delta(x) = \Delta(1-(1-x)) = \mu(1-x)\mu(x)\Delta(x)` we get the first formula.
Since $`1 - 1/x = -(1-x)/x` and $`\Delta(-1) = 0`,
$$`\mu(1/x)\Delta(1/x) = \Delta(1-1/x) = \Delta(1-x) - \Delta(x) = (\mu(x) - 1)\Delta(x),`
which is the second formula; and $`\mu(1/x) \neq 0` gives $`\mu(x) \neq 1`.
The identities for $`t` are a direct computation: with $`\mu = \mu(x)`,
$`t(1-x) = \mu^{-1}/(\mu^{-1} - 1) = 1/(1 - \mu) = 1 - t(x)` and
$`t(1/x) = (1-\mu)/(-\mu) = 1/t(x)`.
That $`t(x) \in Q_x` follows from $`\mu(x) \in Q_x` ({cref "lem:K0"}[]).

The formal statements are {name}`StepBData.μ_one_sub`,
{name}`StepBData.μ_inv`, {name}`StepBData.μ_ne_one`,
{name}`StepBData.t_one_sub` and {name}`StepBData.t_inv`.
The last assertion belongs to the concrete setting; in characteristic $`0` it is
{name}`Char0Hyp.τ_mem_pointV`.

{docstring MilnorAlgDep.StepBData.Transverse}

:::lem "6.7" (title := "Two variables") (tag := "lem:twovar")
If $`x, y` are transverse, then $`xy` is primitive and $`t(xy) = t(x)\, t(y)`.
:::

_Proof._
$`\Delta(xy) = \Delta(x) + \Delta(y) \neq 0`.
Let $`u = x(1-y)/(x-1)`.
Then
$$`\Delta(u) = \Delta(x) + \Delta(1-y) - \Delta(1-x) = (1 - \mu(x))\Delta(x) + \mu(y)\Delta(y) \neq 0,`
so $`u` is primitive.
Since $`1 - xy = (1-x)(1-u)`,
$$`\mu(xy)\bigl(\Delta(x) + \Delta(y)\bigr) = \Delta(1-xy)
  = \mu(x)\Delta(x) + \mu(u)\bigl((1-\mu(x))\Delta(x) + \mu(y)\Delta(y)\bigr).`
Comparing coefficients, $`\mu(xy) = \mu(x) + \mu(u)(1 - \mu(x))` and $`\mu(xy) = \mu(u)\mu(y)`.
Eliminating $`\mu(u)` gives $`\mu(xy)\bigl(\mu(x) + \mu(y) - 1\bigr) = \mu(x)\mu(y)`, that is
$$`1 - \frac{1}{\mu(xy)} = \Bigl(1 - \frac{1}{\mu(x)}\Bigr)\Bigl(1 - \frac{1}{\mu(y)}\Bigr).`
As $`1 - 1/\mu = 1/t`, this is $`t(xy) = t(x)t(y)`.

{docstring MilnorAlgDep.StepBData.Transverse.t_mul}

Hypothesis (H3) is used through the following consequence, with two of the three vectors equal
to $`\Delta(y)`, $`\Delta(z)` and the third $`0`.

{docstring MilnorAlgDep.StepBData.exists_transverse_transverse}

# The field embedding
%%%
tag := "ss:embedding"
%%%

Let
$$`\mathcal N = \{ x \in K_0^\times : \Delta(x) = 0 \},`
a subgroup of $`K_0^\times` (containing $`k^\times` in the blueprint's setting); so
$`K_0^\times` is the disjoint union of $`\mathcal N` and the set of primitive elements.
If $`x \in \mathcal N` and $`z` is primitive, then $`xz` is primitive and
$`\Delta(xz) = \Delta(z)`.

:::lem "6.8" (tag := "lem:tconst")
* *(a)* There is a homomorphism $`\tau \colon \mathcal N \to F^\times` such that
  $`t(xz) = \tau(x)\, t(z)` for all $`x \in \mathcal N` and all primitive $`z`.
* *(b)* $`\tau(-1) = -1`, and for transverse $`x, y` the element $`x + y` is primitive,
  transverse to $`x` and to $`y`, and $`t(x+y) = t(x) + t(y)`.
:::

_Proof._
(a) Let $`x \in \mathcal N`.
For transverse $`z, z'` the pairs $`(xz, z')` and $`(xz', z)` are transverse, so
{cref "lem:twovar"}[] gives $`t(xz)t(z') = t(xzz') = t(xz')t(z)`, i.e.
$`t(xz)/t(z) = t(xz')/t(z')`.
Since any two primitive elements are transverse to a common third one, the quotient
$`t(xz)/t(z)` is the same for all primitive $`z`.

The formalization fixes one primitive element $`z_0` and defines $`\tau(x) = t(xz_0)/t(z_0)`;
that this is a homomorphism on $`\mathcal N` is never needed separately, since it follows from
{cref "prop:tau"}[] (1).

{docstring MilnorAlgDep.StepBData.τ₀}

{docstring MilnorAlgDep.StepBData.t_mul_of_Δ_eq_zero}

(b) Let $`x, y` be transverse.
Then $`-x/y` is primitive and so is $`1 + x/y`, with
$`\Delta(1 + x/y) = \mu(-x/y)(\Delta(x) - \Delta(y))`.
Hence $`x + y = y(1 + x/y)` has
$`\Delta(x+y) = \mu(-x/y)\Delta(x) + (1 - \mu(-x/y))\Delta(y)`; both coefficients are non-zero by
{cref "lem:onevar"}[], so $`x + y` is primitive and transverse to $`x` and to $`y`.
The pairs $`(y, 1 + x/y)` and $`(-x, 1/y)` are transverse, so by Lemmas 6.6, 6.7 and (a),
$$`t(x+y) = t(y)\bigl(1 - t(-x/y)\bigr) = t(y)\Bigl(1 - \tau(-1)\frac{t(x)}{t(y)}\Bigr)
  = t(y) - \tau(-1)\, t(x).`
By symmetry this equals $`t(x) - \tau(-1) t(y)`, so $`(1 + \tau(-1))(t(x) - t(y)) = 0`.
Suppose $`\tau(-1) \neq -1`.
Then $`t(x) = t(y)` for every transverse pair.
The formal proof applies this to two pairs only, $`(x, y)` and $`(x, xy)`: it gives
$`t(y) = t(x) = t(xy) = t(x)t(y)`, so $`t(y) = 1`, which is not a value of $`t`.
(The blueprint concludes that $`t` is constant on primitive elements.)
Hence $`\tau(-1) = -1` ({name}`StepBData.τ₀_neg_one`) and $`t(x+y) = t(x) + t(y)`:

{docstring MilnorAlgDep.StepBData.Transverse.t_add}

We extend $`\tau` to a map $`\tau \colon K_0 \to F` by $`\tau(0) = 0` and $`\tau(x) = t(x)` for
primitive $`x`.
For $`x \in K_0^\times` let $`\ell(x) = F\Delta(x)`; this is a line in $`\Omega` if $`x` is
primitive, and $`0` if $`x \in \mathcal N`.
By {cref "lem:twovar"}[] and {cref "lem:tconst"}[] (a),
$$`t(xz) = \tau(x)\, t(z) \qquad \text{for all } x \in K_0^\times \text{ and all primitive } z
  \text{ with } F\Delta(z) \neq \ell(x), \qquad \text{(P3)}`
and in this situation $`xz` is primitive.

{docstring MilnorAlgDep.StepBData.t_mul_of_notMem_span}

:::prop "6.9" (tag := "prop:tau")
$`\tau \colon K_0 \to F` is a field embedding.
In particular $`K` and $`L` have the same characteristic.
:::

_Proof._
(1) _Multiplicativity._
Let $`x, y \in K_0^\times`.
If $`\Delta(y) \notin \ell(x)`, then $`y` is primitive, and (P3) gives
$`\tau(xy) = t(xy) = \tau(x)t(y) = \tau(x)\tau(y)`.
Otherwise choose, by (H3), a primitive $`z` such that $`F\Delta(z)` is different from $`\ell(x)`,
$`\ell(y)` and $`\ell(xy)`.
By (P3), $`t(xyz) = \tau(xy)t(z)`, and $`yz` is primitive with $`t(yz) = \tau(y)t(z)`.
Moreover $`\Delta(yz) = \Delta(y) + \Delta(z) \notin \ell(x)`, because $`\Delta(y) \in \ell(x)`
and $`\Delta(z) \notin \ell(x)`.
So (P3) applies to $`x` and $`yz` and gives $`t(xyz) = \tau(x)t(yz) = \tau(x)\tau(y)t(z)`.
Hence $`\tau(xy) = \tau(x)\tau(y)`.
(The blueprint distinguishes "transverse or not" and then uses symmetry; the split above avoids
the symmetry step.)

(2) $`\tau(1-s) = 1 - \tau(s)` for all $`s \in K_0 \sm \{0, 1\}`.
For primitive $`s` this is {cref "lem:onevar"}[].
Let $`s \in \mathcal N`; then $`1 - s \in \mathcal N` by (H1).
Choose transverse $`x, y`.
Then $`(1-s)x` is primitive with $`\Delta((1-s)x) = \Delta(x)`, so it is transverse to $`y`, and
by {cref "lem:tconst"}[]
$$`t\bigl((1-s)x + y\bigr) = \tau(1-s)\, t(x) + t(y).`
On the other hand $`x + y` is primitive and transverse to $`x`, hence to $`-sx`, and
$`t(-sx) = \tau(-1)\tau(s)t(x) = -\tau(s)t(x)` (two applications of {cref "lem:tconst"}[] (a),
so that multiplicativity of $`\tau` on $`\mathcal N` is not needed).
So
$$`t\bigl((x+y) + (-sx)\bigr) = t(x) + t(y) - \tau(s)\, t(x).`
Comparing, $`\tau(1-s) = 1 - \tau(s)`.

(3) _Additivity._
Let $`x, y \in K_0^\times` with $`x + y \neq 0`.
By (1), (2) and $`\tau(-1) = -1`,
$$`\tau(x+y) = \tau(y)\, \tau\bigl(1 - (-x/y)\bigr) = \tau(y)\bigl(1 + \tau(x)/\tau(y)\bigr)
  = \tau(x) + \tau(y).`
Also $`\tau(-x) = -\tau(x)` and $`\tau(1) = 1`.
So $`\tau` is a ring homomorphism from the field $`K_0` to $`F`, hence injective, and
$`\chr K = \chr K_0 = \chr F = \chr L`.

The three steps are {name}`StepBData.τFun_mul`,
{name}`StepBData.τFun_one_sub` and {name}`StepBData.τFun_add`, and the
ring homomorphism is:

{docstring MilnorAlgDep.StepBData.τ}

{docstring MilnorAlgDep.StepBData.exists_ringHom}

The ring homomorphism is unique ({name}`StepBData.existsUnique_ringHom`), and
{name}`exists_ringHom_of_addMonoidHom` restates the result for a bundled
homomorphism $`K_0^\times \to \Omega`.
In characteristic $`0`, applied to {name}`Char0Hyp.data`:

{docstring MilnorAlgDep.Char0Hyp.τ}

In particular $`K` has characteristic $`0` ({name}`Char0Hyp.charZero`).

_Characteristic p (placeholder)._
From now on $`K` and $`L` have the same characteristic exponent $`p`.
The blueprint shows that $`\Frob(K_0) \subset K_0`, $`K = \bigcup_{j \geq 0} \Frob^{-j}(K_0)`,
and that every $`x \in K_0 \sm k` is uniquely $`\Frob^j(x_0)` with $`x_0` primitive and
$`j = \hgt \psi(x) \geq 0`, the _primitive root_ of $`x`; then $`\tau(x) = \Frob^j(t(x_0))`.
In characteristic $`0` this is empty: $`K_0 = K` and every $`x \in K \sm k` is primitive.

# Step C: identification
%%%
tag := "ss:stepC"
%%%

:::lem "6.10" (tag := "lem:tauinQ")
$`\tau(x) \in Q_x \sm l` for every $`x \in K_0 \sm k`, and $`\tau(k) \subset l`.
:::

:::lem "6.11" (tag := "lem:theta")
There is $`\theta \in \FF^\times` such that for every primitive $`x`
$$`d\tau(x) \neq 0 \qquad \text{and} \qquad \Delta(x) = \theta\, \dlog \tau(x).`
:::

:::prop "6.12" (tag := "prop:rational")
There is $`r \in \QQ^\times` with $`\psi(x) = r\, [\tau(x)]` for all $`x \in K_0^\times`.
:::

## Characteristic 0
%%%
tag := "ss:stepC0"
%%%

Here $`F = L`, $`K_0 = K`, $`\FF = \QQ`, and $`\Delta = \dlog \circ \psi`.

_Proof of {cref "lem:tauinQ"}[]._
For $`x \notin k` we have $`\tau(x) = \mu(x)/(\mu(x) - 1) \in Q_x` because $`\mu(x) \in Q_x`
({cref "lem:K0"}[]).
For $`c \in k^\times` and $`x \notin k`, $`\tau(c) = \tau(cx)/\tau(x) \in Q_x`; taking
$`x = x_1, x_2` gives $`\tau(c) \in Q_{x_1} \cap Q_{x_2} = l`.

{docstring MilnorAlgDep.Char0Hyp.τ_mem_pointV}

{docstring MilnorAlgDep.Char0Hyp.τ_mem_range_of_mem}

Suppose $`\tau(x) = c \in l` for some $`x \notin k`.
Then $`\mu(x) = c/(c-1) = \kappa \in l`.
Let $`(N, a)` and $`(M, b)` be representatives of $`\psi(x)` and $`\psi(1-x)`; then
$`b \in Q_a` and $`\dlog b = (M\kappa/N)\, \dlog a`.
The eigenvalue lemma, in the form below, shows that $`M\kappa/N` is rational, so $`\mu(x)` is
rational and $`\tau(x) = \tau(r)` for the rational number $`r = \mu(x)/(\mu(x) - 1) \in K`.
Since $`\tau` is injective, $`x = r`, which lies in the prime field of $`K`, hence in $`k`: a
contradiction.
(The formal proof allows the two representatives to have different denominators $`N`, $`M`.)

{docstring MilnorAlgDep.Char0Hyp.τ_notMem_range}

The eigenvalue lemma is applied to the derivation $`\delta` of the point $`Q_a` defined by
$`df = \delta(f)\, da/a`.
In Lean it is defined through the coordinate of the basis $`da` of $`\Omega_{Q_a|l}`:

{docstring MilnorAlgDep.pointDeriv}

{docstring MilnorAlgDep.exists_ratCast_of_dlogL_eq}

_Proof of {cref "lem:theta"}[]._
In characteristic $`0`, the blueprint's $`\sigma_x = \Frob^{-e_0}\tau(x)` is $`\tau(x)` and the
height argument is vacuous.
For $`x \notin k`, the points $`Q_{\tau(x)}` and $`Q_x` agree by {cref "lem:tauinQ"}[]
({name}`Char0Hyp.point_τ`), so
$`\Delta(x) = \theta(x)\, \dlog \tau(x)` with $`\theta(x) \in Q_x`
({name}`Char0Hyp.exists_Δ_eq_smul_dlogL_τ`).
For transverse $`x, y` we have $`\tau(xy) = \tau(x)\tau(y)`, so
$$`\theta(xy)\bigl(\dlog \tau(x) + \dlog \tau(y)\bigr) = \theta(x)\dlog \tau(x) + \theta(y)\dlog \tau(y),`
and $`\theta(x) = \theta(y)` since $`\dlog \tau(x), \dlog \tau(y)` are linearly independent
({name}`Char0Hyp.coeff_eq_of_transverse`).
Since any two primitive elements are transverse to a common third one, $`\theta` is a constant.
It lies in $`Q_{x_1} \cap Q_{x_2} = l` ({name}`pointV_inf_pointV_eq_bot`).
Finally let $`(N, a)` be a representative of $`\psi(x_1)`; then $`a \in Q_{\tau(x_1)}` and
$`\dlog a = N\theta\, \dlog \tau(x_1)`, so $`N\theta` is rational by the eigenvalue lemma.
That $`d\tau(x) \neq 0` follows from $`\Delta(x) \neq 0`; the formal statement does not record
it.

{docstring MilnorAlgDep.Char0Hyp.exists_rat_Δ_eq_smul_dlogL_τ}

_Proof of {cref "prop:rational"}[] for $`\Gamma = 0`._
For $`x \notin k`, {cref "lem:theta"}[] gives
$`\dlog\bigl(\psi(x) - \theta[\tau(x)]\bigr) = \Delta(x) - \theta\, \dlog \tau(x) = 0`, so
$`\psi(x) = \theta[\tau(x)]` because $`\dlog` is injective.
For $`x \in k^\times` both sides vanish, by (A1) and $`\tau(k) \subset l`.
Finally $`\theta \neq 0` because $`\psi \neq 0`.

{docstring MilnorAlgDep.Char0Hyp.exists_rat_ψ_eq}

## Characteristic p
%%%
tag := "ss:stepCP"
%%%

_Placeholder._
In positive characteristic {cref "lem:tauinQ"}[] uses the primitive roots, the proof of
{cref "lem:theta"}[] compares heights with {cref "lem:normalized"}[], and {cref "prop:rational"}[]
needs a $`p`-adic approximation argument with norms and unique factorization in $`l[s]`.
These proofs will be described here.

_Formal counterpart (placeholder):_ `MilnorAlgDep/CharP/StepC.lean` (work package WP-P6).

# End of the proof
%%%
tag := "ss:end"
%%%

By the description of $`K` through primitive roots and since $`L` is perfect, $`\tau` extends
uniquely to a field embedding $`\tau \colon K \to L` commuting with Frobenius, and
$`\psi = r[\tau]` holds on $`K^\times` because $`V` is uniquely divisible; in characteristic
$`0` there is nothing to extend, as $`K_0 = K`.
By {cref "lem:tauinQ"}[], $`\tau^{-1}(l) = k`.
If $`x \in K` is algebraic over $`k`, then $`\tau(x)` is algebraic over $`l`, so $`\tau(x) \in l`
and $`x \in k`; thus $`k` is relatively algebraically closed.
In characteristic $`0` this gives the existence part of Theorem A, with no reduction to perfect
fields and without (A4):

{docstring MilnorAlgDep.theoremA_perfect_of_charZero}

It remains to prove uniqueness.

:::lem "6.13" (tag := "lem:unique")
Let $`\tau, \tau' \colon K \to L` be field embeddings with
$`\tau^{-1}(l) = \tau'^{-1}(l) = k \neq K`, and $`r, r' \in \QQ^\times` with
$`r[\tau(x)] = r'[\tau'(x)]` in $`V` for all $`x \in K^\times`.
Then $`\tau' = \Frob^j \circ \tau` and $`r' = p^{-j} r` for some $`j \in \Gamma`.
:::

The formal statement is {name}`theoremA_perfect_unique` (shown in
{ref "ss:statementA"}[Section 1.1]).
It assumes only that $`\psi = r[\tau] = r'[\tau']` is non-zero, which implies the hypotheses of
the lemma: if $`\psi(x_0) \neq 0` then $`r, r' \neq 0`, and by (V1)
$`\tau(x) \in l \iff \psi(x) = 0 \iff \tau'(x) \in l`, while $`\tau(x_0) \notin l`.
The proof uses only $`r, r' \neq 0` and the existence of $`x_0` with $`\tau(x_0) \notin l`.
It is uniform in the characteristic: "prime to $`p`" is "non-zero in $`L`".

_Proof (as formalized)._
Write $`r/r' = p^j A/B` with $`j \in \ZZ` ($`j = 0` in characteristic $`0`) and integers $`A, B`
non-zero in $`L`:

{docstring MilnorAlgDep.exists_eq_zpow_mul_div}

Since $`[\Frob^j y] = p^j [y]` ({name}`cls_frobeniusEquiv_zpow`), the hypothesis
becomes $`A[\Frob^j \tau(y)] = B[\tau'(y)]` for all $`y \in K^\times`.
Let $`x \in K` with $`\tau(x) \notin l`, and put $`T = \Frob^j \tau(x)`, $`S' = \tau'(x)`.
The hypothesis for $`x` and for $`1 - x` gives, by (V1),
$$`T^A = c\, S'^{B}, \qquad (1-T)^A = c'\, (1-S')^{B} \qquad (c, c' \in l^\times)`
({name}`V.exists_zpow_eq_mul_pow_of_smul_cls_eq`), and $`T` is transcendental
over $`l`.

{docstring MilnorAlgDep.eq_of_zpow_eq_of_transcendental}

Here the blueprint takes logarithmic differentials in $`E = l(S, S')` and divides; the formal
proof applies a derivation $`\delta` with $`\delta T = 1`, which exists because $`dT` is a basis of
$`\Omega_{E|l}` for the field $`E` of elements of $`L` separable over $`l(T)`.
Then $`A\, S' = B\, \delta S'\, T` and $`A(1 - S') = B\, \delta S'\, (1 - T)`, and eliminating
$`\delta S'` gives $`A(S' - T) = 0`:

{docstring MilnorAlgDep.eq_of_derivation_of_zpow_eq}

So $`\tau' = \Frob^j \circ \tau` on $`\{ x : \tau(x) \notin l \}`.
If $`\tau(x) \in l`, write $`x = (x + x_0) - x_0`, where $`\tau(x + x_0), \tau(x_0) \notin l`;
so $`\tau' = \Frob^j \circ \tau` on $`K`.
Finally $`r[\tau(x_0)] = r' p^j [\tau(x_0)]` with $`[\tau(x_0)] \neq 0` gives $`r' = p^{-j} r`.
This completes the proof of Theorem A. ∎

## How the formal proof is assembled
%%%
tag := "ss:assembly"
%%%

The file `MilnorAlgDep/TheoremA.lean` contains the three frozen statements of
{ref "ss:statementA"}[Section 1.1], each proved by one line that forwards to a theorem with the
same statement:

```
theoremA                                 TheoremA.lean
└─ theoremA_aux                          Reduction.lean
   │   L ↦ L^i, ψ ↦ V.toPerfectClosure ∘ ψ
   └─ theoremA_perfect_aux               Reduction.lean
      │   case split on ringChar L
      ├─ = 0: theoremA_perfect_of_charZero     Char0/Main.lean
      └─ ≠ 0: theoremA_perfect_of_isPRadical   Reduction.lean
         │   K ↦ PerfectClosure K q, ψ ↦ extendPsi
         └─ theoremA_core_charP          CharP/Main.lean (sorry)

theoremA_perfect         = theoremA_perfect_aux
theoremA_perfect_unique  = theoremA_perfect_unique_aux
                                         Uniqueness.lean
```

In the second branch $`q` is the characteristic of $`K`, which is prime by (A4); Mathlib's
`PerfectClosure K q` is the perfect closure.
The characteristic $`0` proof is the content of `MilnorAlgDep/Char0/`: `DLog.lean`
({cref "lem:W"}[]), `PointDeriv.lean` (differentials of a point and the eigenvalue lemma in
$`\Omega_{L|l}`), `Delta.lean` ({cref "lem:K0"}[] and {cref "prop:tau"}[]), `StepC.lean`
({cref "lem:tauinQ"}[], {cref "lem:theta"}[], {cref "prop:rational"}[]) and `Main.lean`
({ref "ss:end"}[Section 6.7]).
The remaining `sorry` is the positive characteristic core:

{docstring MilnorAlgDep.theoremA_core_charP}
