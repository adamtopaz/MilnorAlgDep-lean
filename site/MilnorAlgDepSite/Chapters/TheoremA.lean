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
The characteristic $`0` proof consists of {ref "ss:reductions"}[Section 6.1],
{ref "ss:model0"}[Section 6.3.1], {ref "ss:stepB"}[Sections 6.4], {ref "ss:embedding"}[6.5],
{ref "ss:stepC0"}[6.6.1] and {ref "ss:end"}[6.7].
The characteristic $`p` proof uses {ref "sec:levels"}[Chapters 3–5] and, in this chapter,
{ref "ss:reductions"}[Section 6.1] with {ref "ss:notationP"}[6.1.1], Step A
({ref "sec:stepA"}[Section 6.2]), {ref "ss:modelP"}[Section 6.3.2], Step B with
{ref "ss:roots"}[Section 6.5.1], {ref "ss:stepCP"}[Section 6.6.2] and
{ref "ss:end"}[Section 6.7].
Both are complete; {ref "ss:assembly"}[Section 6.7.1] shows how they are put together.

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

## Characteristic p
%%%
tag := "ss:notationP"
%%%

In the characteristic $`p` parts of this chapter, $`L` is perfect of characteristic $`p > 0`, and
$`K` is perfect of positive characteristic by (A4); that the two characteristics agree is only
proved in {cref "prop:tau"}[].
The formal proof bundles the data and the hypotheses, with the three elements of (A3) made
explicit, as it does in characteristic $`0` ({ref "ss:model0"}[Section 6.3.1]):

{docstring MilnorAlgDep.CharPHyp}

The assumptions on the fields are separate arguments:
`(p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]`, and
`[PerfectField K]` from Step A on.
The prime `p` is an explicit argument of every definition (`H.K₀ p`, `H.τ p`, ...), as in
{name}`levDiff` `l p`.
The homomorphism is extended to $`K` by $`\psi(0) = 0`, so that $`\psi(1 - x)` and
$`\psi(x + y)` can be written without proofs that the arguments are non-zero:

{docstring MilnorAlgDep.CharPHyp.ψK}

The point $`Q_x` is `pointV l (H.ψK x)`, and "$`u, w` are $`\psi`-independent" is
`VAlgIndep l ![H.ψK u, H.ψK w]`.

_Representatives and levels._
By (V2) every element of $`V` has a representative $`(N, a)` with $`N` prime to $`p`.
The formal proof fixes one for every $`v` (for $`v = 0` it is $`(1, 1)`); for $`v = \psi(x)` it
is denoted $`(N, \rho(x))`:

{docstring MilnorAlgDep.IsVRep +hideFields +hideStructureConstructor}

Its fields are `pos : 0 < N`, `coprime : N.Coprime p` and `nsmul_eq : N • v = 〚a〛`.

{docstring MilnorAlgDep.CharPHyp.ρ}

For $`v \in V \sm 0` with representative $`(N, a)` the blueprint puts
$`\lev(v) = \lev(a) \in \Lambda(Q_v)`.
This is well defined: if $`(N', a')` is another representative then $`a^{N'} = c\, a'^{N}` with
$`c \in l^\times`, and $`a \approx a^{N'}`, $`a' \approx a'^N` because $`N, N'` are prime to $`p`
({name}`IsVRep.sepEquiv`).
As in {ref "sec:levels"}[Chapter 3] ({cref "ss:elementwise"}[]), only differences of levels are
formalized:

{docstring MilnorAlgDep.levDiffV}

{docstring MilnorAlgDep.levDiffV_eq}

The blueprint notes $`\lev(pv) = \lev(v) + 1` and $`\lev(-v) = \lev(v)`.
The formal proof has one rule for all rational multiples, which gives these two and
$`\lev(Nv) = \lev(v)` for $`N` prime to $`p` ({name}`levDiffV_p_nsmul_left`,
{name}`levDiffV_neg_left`, {name}`levDiffV_nsmul_left`):

{docstring MilnorAlgDep.levDiffV_smul_left}

_Proof._
Write $`q = p^j A/B` with integers $`A, B` prime to $`p` ({name}`exists_eq_zpow_mul_div`, also
used for {cref "lem:unique"}[]).
If $`(M, b)` represents $`v`, then $`(BM, \Frob^j(b^A))` represents $`qv`, and
$`\lev \Frob^j(b^A) = \lev(b^A) + j = \lev(b) + j`.

Heights are treated in the same way.
For a transcendence basis $`B`, the height of $`v \neq 0` is the height of a representative
({name}`hgtV_eq`); for $`v, w` in one point, $`\hgt(v) - \hgt(w) = \lev(v) - \lev(w)`
({name}`hgtV_sub_hgtV`), and in particular $`\hgt(qv) = \hgt(v) + v_p(q)` ({name}`hgtV_smul`).

{docstring MilnorAlgDep.hgtV}

_The sum formula._
The following consequence of (A1) and (A2) is used several times: for $`x, y \in K^\times` with
$`x + y \neq 0` and $`x/y \notin k`,
$$`\psi(x + y) = \psi(y) + \psi\bigl(1 - (-x/y)\bigr), \qquad
  \psi\bigl(1 - (-x/y)\bigr) \in G_{Q_{x/y}} \sm 0. \qquad \text{(eq:sum)}`
The first part is $`\psi` applied to $`x + y = y\,(1 - (-x/y))`.
For the second, $`s = -x/y \notin k`, so $`1 - s \notin k` and $`Q_{1-s} = Q_s = Q_{x/y}` by (A2)
and $`\psi(-1) = 0`.

{docstring MilnorAlgDep.CharPHyp.ψK_add}

{docstring MilnorAlgDep.CharPHyp.pointV_ψK_one_sub_neg_div}

In particular, if $`x, y` are $`\psi`-independent, then $`\psi(x + y) \neq 0` and
$`Q_x, Q_y, Q_{x+y}` are three distinct collinear points.
Indeed $`Q_{x/y}` lies on $`\la Q_x, Q_y \ra` and is different from $`Q_y` (otherwise
$`\psi(x) = \psi(x/y) + \psi(y) \in G_{Q_y}`), so by (eq:sum) $`\psi(x + y)` is the sum of a
non-zero element of $`G_{Q_y}` and a non-zero element of $`G_{Q_{x/y}}`: it is non-zero, its point
lies on $`\la Q_x, Q_y \ra` and is not $`Q_y`; by symmetry it is not $`Q_x`.
In the language of {ref "sec:levels"}[Chapter 3], the representatives form a collinear triple:

{docstring MilnorAlgDep.CharPHyp.isCollinearTriple_add}

That a sum of non-zero elements of two distinct points is non-zero and lies in neither point is
{name}`pointV_add_ne`.
"Lies on $`\la Q_x, Q_y \ra`" is a statement about closures in the algebraic matroid: a
representative of $`mv + nw` ($`m, n \in \ZZ`) lies in the closure of representatives of $`v` and
$`w` ({name}`mem_closure_of_eq_zsmul_add_zsmul`).
The incidence part needs no hypothesis on $`x/y`, because $`\psi(x + y) = \psi(y)` if
$`x/y \in k`.
{cref "lem:cocycle"}[] uses it in this form, which saves the blueprint's argument for $`G \neq B`
there:

{docstring MilnorAlgDep.CharPHyp.isAlgebraic_ρ_add}

# Step A: the levels of ψ(x) and ψ(1 − x)
%%%
tag := "sec:stepA"
%%%

:::prop "6.1" (tag := "prop:levels")
For every $`x \in K \sm k` we have $`\lev \psi(1-x) = \lev \psi(x)`.
:::

{docstring MilnorAlgDep.CharPHyp.levDiffV_one_sub}

The adapted model uses the proposition in the form of heights:

{docstring MilnorAlgDep.CharPHyp.hgtV_one_sub}

If $`\Gamma = 0` there is nothing to prove, and the characteristic $`0` proof has no Step A.
In this section $`\Gamma = \ZZ`, so $`d = 3`, and by (A4) the field $`K` has positive
characteristic $`q` (not yet known to be $`p`); as $`K` is perfect, $`K^\times` is divisible by
$`q`, and therefore
$$`\text{every homomorphism } K^\times \to \ZZ \text{ is trivial.} \qquad \text{(eq:nohom)}`
Indeed $`\chi(x) = q^n \chi(x^{1/q^n})` is divisible by $`q^n` for every $`n`.
This is the only place where the characteristic $`p` proof uses (A4), apart from the reduction to
a perfect field $`K` in {ref "ss:reductions"}[Section 6.1].

{docstring MilnorAlgDep.nohom}

For $`s \in K \sm k` put
$$`n(s) = \lev \psi(1 - s) - \lev \psi(s) \in \ZZ.`
Since $`\psi(1 - 1/s) = \psi(1 - s) - \psi(s)` and $`\lev \psi(1/s) = \lev \psi(s)`, we have
$`n(1/s) = \lev\bigl(\psi(1-s) - \psi(s)\bigr) - \lev \psi(s)` ({name}`CharPHyp.n_inv`).
Obviously $`n(1 - s) = -n(s)` ({name}`CharPHyp.n_one_sub`).

{docstring MilnorAlgDep.CharPHyp.n}

For $`\psi`-independent $`u, w` the points $`Q_u, Q_w, Q_{u+w}` are distinct and collinear
({ref "ss:notationP"}[Section 6.1.1]), and we define $`c(u, w) \in \ZZ` by the condition that
$$`\bigl(\lev \psi(u),\ \lev \psi(w) + c(u, w),\ \ast\bigr) \text{ is the level triple of }
  (Q_u, Q_w, Q_{u+w}). \qquad \text{(eq:defc)}`
Clearly $`c(w, u) = -c(u, w)` ({name}`CharPHyp.c_swap`, from {name}`levelTriple_swap_fst`).
In Lean, $`c(u, w)` is the first entry of the level triple relative to the chosen representatives
({cref "ss:normalized"}[]):

{docstring MilnorAlgDep.CharPHyp.c}

:::lem "6.2" (title := "The gauge of a sum") (tag := "lem:gauge")
Let $`u, w` be $`\psi`-independent and $`s = -u/w`.
Then
$$`c(u, w) = \begin{cases} -n(s) & \text{if } n(s) > 0, \\
  n(1/s) & \text{if } n(s) = 0 \text{ and } n(1/s) > 0, \\
  0 & \text{if } n(s) < 0, \text{ or } n(s) = n(1/s) = 0, \end{cases}`
and these cases are exhaustive.
In particular $`c(u, w)` depends only on $`s`; we denote it by $`\nu(s)`.
:::

In Lean the right-hand side is the definition of $`\nu`, and the lemma says
$`c(u, w) = \nu(-u/w)`:

{docstring MilnorAlgDep.CharPHyp.ν}

{docstring MilnorAlgDep.CharPHyp.c_eq_ν}

_Proof (as formalized)._
_Setup._
Since $`u, w` are $`\psi`-independent, $`s = -u/w \notin k` (otherwise $`\psi(u) = \psi(w)`;
{name}`CharPHyp.notMem_neg_div`), and $`s, w` are $`\psi`-independent.
Choose representatives with a common denominator $`N` (the product of the chosen ones,
{name}`exists_isVRep₃`): $`N\psi(s) = [a]`, $`N\psi(w) = [y]`, $`N\psi(1-s) = [e]`.
Then $`a, e \in Q_s`, the elements $`a, y` are algebraically independent, and, since $`u = -sw`
and $`u + w = w(1 - s)`,
$$`N\psi(u) = [ay], \qquad N\psi(u + w) = [ye], \qquad \lev(e) = \lev(a) + n(s).`
So $`c(u, w)` can be computed from any normalized triple $`(X, Y, Z)` of the three points
$`(Q_u, Q_w, Q_{u+w}) = (Q_{ay}, Q_y, Q_{ye})`: by {cref "lem:normalized"}[] (b),
$$`c(u, w) = \bigl(\lev Y - \lev y\bigr) - \bigl(\lev X - \lev(ay)\bigr).`

{docstring MilnorAlgDep.CharPHyp.gauge_setup}

In each case we exhibit a normalized triple.
The blueprint checks the separability conditions with the irreducible polynomial relation of
$`(X, Y, Z)` and {cref "lem:sepcrit"}[].
The formal proof checks all three at once, with the separability criterion of
{cref "ss:sepcrit"}[]: in the model of an algebraically independent pair $`(b_1, b_2)`, where
$`db_1, db_2` is a basis of the differentials, three elements whose differentials are pairwise
linearly independent form a normalized triple.
In coordinates, the three $`2 \times 2` determinants must be non-zero:

{docstring MilnorAlgDep.isNormalized_of_coords}

Two facts are used to compute the differentials: $`d(y^{p^m}) = 0` for $`m > 0`
({name}`modelD_pow_pow_of_pos`), and if $`t \approx t'` with $`dt' \neq 0`, then $`dt = c\, dt'`
with $`c \neq 0` ({name}`SepEquiv.exists_modelD_eq_smul`, from {cref "lem:pointsmodel"}[] (c)).

_Case $`i = n(s) > 0`._
Then $`e \approx a'` for $`a' = \Frob^i(a)` (called $`A` in the blueprint and in the docstring
below).
Work in the model of $`(a', y)`; it contains $`e`, and $`de = c\, da'` with $`c \neq 0`.
Take
$$`(X, Y, Z) = \bigl(a'\, y^{p^i},\ y,\ ye\bigr) = \bigl(\Frob^i(ay),\ y,\ ye\bigr).`
Then $`dX = y^{p^i}\, da'`, $`dY = dy` and $`dZ = yc\, da' + e\, dy`.
The determinants are $`y^{p^i}` for $`(X, Y)`, $`y^{p^i} e` for $`(X, Z)` and $`-yc` for
$`(Y, Z)`, all non-zero.
So $`(X, Y, Z)` is normalized, with $`\lev X = \lev(ay) + i` and $`\lev Y = \lev y`; hence
$`c(u, w) = -i`.

{docstring MilnorAlgDep.CharPHyp.c_eq_neg_n_of_pos}

_Case $`n(s) = -j < 0`._
Put $`\alpha = \Frob^{-j}(a)` and $`\eta = \Frob^{-j}(y)`; then $`e \approx \alpha`.
Work in the model of $`(\alpha, \eta)`; it contains $`e`, and $`de = c\, d\alpha` with
$`c \neq 0`.
Take
$$`(X, Y, Z) = \bigl(\alpha\eta,\ \eta,\ \eta^{p^j} e\bigr) = \bigl(\Frob^{-j}(ay),\ \Frob^{-j}(y),\ ye\bigr).`
Then $`dX = \eta\, d\alpha + \alpha\, d\eta`, $`dY = d\eta` and $`dZ = \eta^{p^j} c\, d\alpha`.
The determinants are $`\eta`, $`-\alpha\eta^{p^j} c` and $`-\eta^{p^j} c`, all non-zero.
The levels are $`\lev X = \lev(ay) - j` and $`\lev Y = \lev y - j`, so $`c(u, w) = 0`.

{docstring MilnorAlgDep.CharPHyp.c_eq_zero_of_n_neg}

_Case $`n(s) = 0`._
Then $`e \approx a`, so $`g = e/a` is separable algebraic over $`l(a)`, and hence
$`\lev(g) \geq \lev(a)` ({name}`levDiff_nonneg_iff`).
Since $`(N, g)` represents $`\psi(1 - s) - \psi(s)`, this says $`n(1/s) \geq 0`; so the cases of
the lemma are exhaustive.

{docstring MilnorAlgDep.CharPHyp.n_inv_nonneg_of_n_eq_zero}

Suppose first $`n(1/s) = 0`, so $`g \approx a` as well.
Work in the model of $`(a, y)`: it contains $`e` and $`g`, with $`de = c\, da` and
$`dg = c'\, da`, where $`c, c' \neq 0`; differentiating $`e = ga` gives $`c = g + ac'`.
Take $`(X, Y, Z) = (ay, y, ye)`: $`dX = y\, da + a\, dy`, $`dY = dy`, $`dZ = yc\, da + e\, dy`.
The determinants are $`y` for $`(X, Y)`, $`-yc` for $`(Y, Z)`, and
$$`ye - ayc = y\,(e - ag - a^2 c') = -a^2 y\, c' \neq 0 \qquad \text{for } (X, Z).`
So the triple is normalized and $`c(u, w) = 0`.
(This is the blueprint's computation $`e - a e_a = -a^2 (e/a)_a`, with $`c' = (e/a)_a`.)

{docstring MilnorAlgDep.CharPHyp.c_eq_zero_of_n_eq_zero}

Suppose finally $`n(s) = 0` and $`n(1/s) > 0`.
The first case, applied to the pair $`(w, u)`, for which $`-w/u = 1/s`, gives
$`c(w, u) = -n(1/s)`, so $`c(u, w) = n(1/s)`.

:::lem "6.3" (title := "Cocycle") (tag := "lem:cocycle")
If $`u, w, z \in K` are $`\psi`-independent, then $`c(u, z) = c(u, w) + c(w, z)`.
:::

{docstring MilnorAlgDep.CharPHyp.c_add_c}

_Proof._
Apply {cref "lem:quadrangle"}[] to the points
$$`A = Q_u,\quad B = Q_w,\quad C = Q_z,\quad D = Q_{u+w},\quad E = Q_{w+z},\quad
  G = Q_{u+w+z},\quad H = Q_{u+z}.`
The points $`A, B, C` are not collinear.
$`D` lies on $`\la A, B \ra` and $`E` on $`\la B, C \ra`, and they differ from $`A, B` and from
$`B, C` respectively, by {ref "ss:notationP"}[Section 6.1.1]; for the same reason $`u + z \notin k`,
so $`H` is a point.
$`G` is a point because $`u + w` and $`z` are again $`\psi`-independent
({name}`CharPHyp.vAlgIndep_add_of_vAlgIndep₃`), so that $`u + w + z \notin k`.
By (eq:sum), applied to $`(u + w) + z` and to $`u + (w + z)`, the point $`G` lies on
$`\la D, C \ra` and on $`\la A, E \ra`; applied to $`u + z` and to $`(u + w + z) + (-w)`, it shows
that $`H` lies on $`\la A, C \ra` and on $`\la B, G \ra`.
The formal proof uses the incidence form {name}`CharPHyp.isAlgebraic_ρ_add` of (eq:sum) for these
four incidences.
The blueprint also shows $`G \neq B`, which the line $`\la B, G \ra` requires; the formal
quadrangle lemma does not need it ({ref "sec:quadrangle"}[Chapter 5]).
So there are levels $`\alpha_A, \alpha_B, \alpha_C` which are the first two entries of level
triples of $`(A, B, D)`, of $`(B, C, E)` and of $`(A, C, H)`.
By (eq:defc) this means
$$`\alpha_B - \lev \psi(w) = \alpha_A - \lev \psi(u) + c(u, w), \qquad
  \alpha_C - \lev \psi(z) = \alpha_B - \lev \psi(w) + c(w, z),`
and $`\alpha_C - \lev \psi(z) = \alpha_A - \lev \psi(u) + c(u, z)`.
The claim follows.
In Lean this computation is {name}`levelTriple_fst_add_levelTriple_fst`
({ref "sec:quadrangle"}[Chapter 5]).

_Proof of {cref "prop:levels"}[] (as formalized)._
Let $`s, s'` be $`\psi`-independent.
By (A3) one of $`x_1, x_2, x_3`, say $`z`, is such that $`s, s', z` are $`\psi`-independent
({name}`CharPHyp.exists_vAlgIndep₃`: otherwise the representatives of all three would lie in the
closure of two elements in the algebraic matroid).
Put $`w = -s'z` and $`u = ss'z`.
Then $`u, w, z` are $`\psi`-independent, because
$`(\psi(u), \psi(w), \psi(z)) = (\psi(s) + \psi(s') + \psi(z),\ \psi(s') + \psi(z),\ \psi(z))` is a
unimodular change of variables ({name}`VAlgIndep.add_add₃`).
Moreover $`-u/w = s`, $`-w/z = s'` and $`-u/z = -ss'`, so Lemmas 6.3 and 6.2 give
$$`\nu(-ss') = \nu(s) + \nu(s') \qquad \text{for all } \psi\text{-independent } s, s'.
  \qquad \text{(eq:nu)}`

{docstring MilnorAlgDep.CharPHyp.ν_neg_mul}

Put $`\delta(s) = \nu(-s) - \nu(s)`.
Applying (eq:nu) to $`(-s, s')` and to $`(s, -s')` gives $`\delta(s) = \delta(s')` for all
$`\psi`-independent $`s, s'` ({name}`CharPHyp.ν_neg_sub_ν_eq`).
The blueprint concludes that $`\delta` is a constant $`\delta_0` and then shows $`\delta_0 = 0`.
The formal proof shows directly that $`\delta` vanishes at the given pair: $`\delta(s) = \delta(s')`,
and also $`\delta(-s) = \delta(s')`, since $`-s, s'` are $`\psi`-independent too; as
$`\delta(-s) = -\delta(s)`, this gives $`\delta(s) = 0`.
Then (eq:nu) for $`(-s, s')` reads
$$`\nu(ss') = \nu(-s) + \nu(s') = \nu(s) + \nu(s') \qquad \text{for all } \psi\text{-independent }
  s, s'.`

{docstring MilnorAlgDep.CharPHyp.ν_mul}

For $`c \in k^\times` and $`w \notin k` the integer $`\varrho(c) = \nu(cw) - \nu(w)` does not depend
on $`w` ({name}`CharPHyp.ν_mul_sub_ν_eq`): if $`w, w'` are $`\psi`-independent, then
$`\nu(cw) + \nu(w') = \nu(cww') = \nu(w) + \nu(cw')`, and two elements with the same point are
compared with a third one, which can be taken among $`x_1, x_2, x_3`
({name}`CharPHyp.exists_vAlgIndep_pair`).
Similarly $`\nu(xy) = \nu(x) + \nu(y)` whenever $`x, y, xy \notin k`
({name}`CharPHyp.ν_mul_of_notMem`): if $`Q_x = Q_y`, choose $`w` with $`Q_w \neq Q_x`; then
$`\nu(xy) + \nu(w) = \nu(xyw) = \nu(x) + \nu(yw) = \nu(x) + \nu(y) + \nu(w)`.
Define $`\chi \colon K^\times \to \ZZ` by $`\chi = \nu` on $`K \sm k` and $`\chi = \varrho` on
$`k^\times`, where the formal proof computes $`\varrho` with the fixed element $`w = x_1`.
Then $`\chi` is a homomorphism.
This is clear for pairs of constants, for a constant and a non-constant, and for $`x, y` with
$`x, y, xy \notin k`.
If $`x, y \notin k` and $`xy = c \in k`, choose $`w` which is $`\psi`-independent of $`x` and of
$`y`; then $`\varrho(c) + \nu(w) = \nu(cw) = \nu(x) + \nu(yw) = \nu(x) + \nu(y) + \nu(w)`.

{docstring MilnorAlgDep.CharPHyp.exists_addMonoidHom_eq_ν}

By (eq:nohom), $`\chi = 0`, so $`\nu = 0` on $`K \sm k` ({name}`CharPHyp.ν_eq_zero`).
By {cref "lem:gauge"}[], $`\nu(s) = 0` excludes $`n(s) > 0`.
Hence $`n(s) \leq 0` for all $`s \in K \sm k`, and since $`n(1 - s) = -n(s)` we conclude $`n = 0`:

{docstring MilnorAlgDep.CharPHyp.n_eq_zero}

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

_The adapted model._
Let $`a_1, a_2, a_3` be the chosen representatives $`\rho(x_i)` of $`\psi(x_i)`.
They are algebraically independent by (A3), so they extend to a transcendence basis $`A` of
$`L|l` (Mathlib's `exists_isTranscendenceBasis_superset`), and $`F = L_A` is the model of
{ref "sec:models"}[Chapter 4]:

{docstring MilnorAlgDep.CharPHyp.trBasis}

{docstring MilnorAlgDep.CharPHyp.F}

Heights are taken in this model, $`\hgt(v)` = `hgtV p (H.B p) v`
({ref "ss:notationP"}[Section 6.1.1]).
The elements $`x_i` have height $`0`, since their representatives belong to $`A`
({name}`CharPHyp.hgtV_x`).

_The group W._
The formal definition of $`W` does not mention heights: $`W` is the set of elements of $`V` having
a representative $`(N, a)` with $`a \in L_A`.
With this definition $`W` is visibly a subgroup (if $`Nv = [a]` and $`Mw = [b]`, then
$`NM(v + w) = [a^M b^N]`), and by {cref "lem:pointsmodel"}[] (a) it is the blueprint's $`W`:

{docstring MilnorAlgDep.W}

{docstring MilnorAlgDep.mem_W_iff}

_Proof._
A transcendental element of $`L` lies in $`L_A` if and only if its height is non-negative
({name}`mem_model_iff_hgt_nonneg`).
It remains to see that if some representative $`(N, a)` of $`v` has $`a \in L_A`, then so does the
chosen one $`(N', a')` ({name}`vRep_mem_model`): by (V2), $`a'^N = c\, a^{N'}` with
$`c \in l^\times`, so $`a'` is a root of $`X^N - c\,a^{N'} \in L_A[X]`, which is separable because
$`N` is prime to $`p`; hence $`a' \in L_A` by {cref "lem:model"}[] (b).

_The logarithmic derivative._
On $`F = L_A` we have $`\dlog y = y^{-1}\, dy \in \Omega_A` ({name}`modelDLog`, which is $`0`
outside $`L_A` by convention), and $`\dlog_A` is defined with any representative in $`L_A`; it is
$`0` outside $`W`.

{docstring MilnorAlgDep.dlogA}

{docstring MilnorAlgDep.dlogA_eq}

_Proof of {cref "lem:W"}[] for $`\Gamma = \ZZ` (as formalized)._
(a) If $`(N, a)` and $`(N', a')` are representatives of $`v` with $`a, a' \in L_A`, then
$`a^{N'} = c\, a'^{N}` with $`c \in l^\times`, so $`N' \dlog a = N \dlog a'`, as $`\dlog c = 0`.
So $`\dlog_A` is well defined ({name}`dlogA_eq`).
If $`(N, a)` and $`(M, b)` represent $`v, w \in W` with $`a, b \in L_A`, then $`(NM, a^M b^N)`
represents $`v + w`, and $`\dlog(a^M b^N) = M \dlog a + N \dlog b`; so $`\dlog_A` is additive
({name}`dlogA_add`), and it is a homomorphism $`W \to \Omega_A` ({name}`dlogAHom`).

(b) Let $`v \in W \sm 0` with chosen representative $`(N, a)`, so $`a \in L_A`.
Then $`\dlog_A(v) = N^{-1} a^{-1}\, da` is non-zero if and only if $`da \neq 0`, that is, if and
only if $`a` is a model generator, $`\hgt(v) = 0` ({cref "lem:pointsmodel"}[] (b),
{name}`hgt_eq_zero_iff`); and then $`F \dlog_A(v) = F\, da = \omega_A(Q_v)`
({name}`omega_eq_span_of_hgt_eq_zero`).

{docstring MilnorAlgDep.dlogA_ne_zero_iff}

{docstring MilnorAlgDep.span_dlogA_eq_omega}

(c) All three statements follow from $`\hgt(qv) = \hgt(v) + v_p(q)` ({name}`hgtV_smul`).
If $`v \in W \sm 0` and $`\dlog_A(v) = 0`, then $`\hgt(v) > 0` by (b), so $`p^{-1} v` has
non-negative height and lies in $`W`; conversely $`\dlog_A(pw) = p \dlog_A(w) = 0`, as $`F` has
characteristic $`p`.
If $`v \neq 0`, then $`p^j v \in W` as soon as $`j \geq -\hgt(v)`.
If $`v = p^j w_j` with $`w_j \in W` for every $`j`, then $`\hgt(v) = \hgt(w_j) + j \geq j` for every
$`j`, which is impossible unless $`v = 0`.

{docstring MilnorAlgDep.dlogA_eq_zero_iff}

{docstring MilnorAlgDep.exists_pow_nsmul_mem_W}

{docstring MilnorAlgDep.eq_zero_of_forall_mem_pow_nsmul_W}

_The field_ $`K_0`.
The first assertion of {cref "lem:K0"}[] (b) comes first, since (a) depends on it.
By {cref "prop:levels"}[], in the form {name}`CharPHyp.hgtV_one_sub`, $`\psi(1-x)` and $`\psi(x)`
have the same height for $`x \notin k`; so $`\psi(x) \in W` implies $`\psi(1 - x) \in W`
({name}`CharPHyp.ψK_one_sub_mem_W`).
For closure under addition, let $`x, y \in K_0` with $`x, y, x + y \neq 0`, and put
$`s = -x/y`.
By (eq:sum), $`\psi(x + y) = \psi(y) + \psi(1 - s)`.
If $`s \in k`, then $`\psi(1 - s) = 0`; otherwise $`\psi(s) = \psi(x) - \psi(y) \in W`, hence
$`\psi(1 - s) \in W`; in both cases $`\psi(x + y) \in W` ({name}`CharPHyp.K₀_add_mem`).
Closure under products, inverses and negatives holds because $`W` is a group and
$`\psi(-1) = 0`.

{docstring MilnorAlgDep.CharPHyp.K₀}

{docstring MilnorAlgDep.CharPHyp.Δhom}

By {cref "lem:W"}[] (b), an element $`x \in K_0` is primitive if and only if $`x \notin k` and
$`\hgt \psi(x) = 0` ({name}`CharPHyp.data_Δ_ne_zero_iff`).

_Proof of {cref "lem:K0"}[] (b) for $`\Gamma = \ZZ`._
Let $`x \in K_0 \sm k`.
Then $`1 - x \in K_0 \sm k`, and by {cref "lem:W"}[] (b) and {cref "prop:levels"}[], $`x` is
primitive if and only if $`\hgt \psi(x) = 0`, if and only if $`\hgt \psi(1 - x) = 0`, if and only
if $`1 - x` is primitive.
If $`x` is primitive, $`\Delta(x)` and $`\Delta(1 - x)` both span the line $`\omega_A(Q_x)` of
the common point $`Q_x = Q_{1-x}` ({cref "lem:W"}[] (b), {name}`omega_eq_of_samePoint`).
These are the hypotheses (H1) and (H2) of Step B ({ref "ss:stepB"}[Section 6.4]):

{docstring MilnorAlgDep.CharPHyp.Δhom_eq_zero_iff_one_sub}

{docstring MilnorAlgDep.CharPHyp.Δhom_one_sub_mem_span}

For $`\mu(x) \in Q_x`, let $`(N, a)` and $`(M, b)` be the chosen representatives of $`\psi(x)`
and $`\psi(1 - x)`; no common denominator is needed.
They are model generators of $`Q_x`, and $`b \approx a` by {cref "prop:levels"}[], so
$`db = c\, da` with $`c` separable algebraic over $`l(a)`, hence $`c \in Q_a = Q_x`
({name}`exists_modelD_eq_smul_of_isSeparable`, the argument of {cref "lem:pointsmodel"}[] (c)).
Then $`\Delta(1 - x) = \frac{Nac}{Mb} \Delta(x)`, and $`\mu(x) = \frac{Nac}{Mb} \in Q_x`.

{docstring MilnorAlgDep.CharPHyp.μ_mem_pointV}

_Proof of {cref "lem:K0"}[] (c) for $`\Gamma = \ZZ`._
We have $`\Delta(x_i) = N_i^{-1} a_i^{-1}\, da_i` with $`a_i \in A`, and $`(da)_{a \in A}` is a basis
of $`\Omega_A` ({cref "lem:model"}[] (a)); so $`\Delta(x_1), \Delta(x_2), \Delta(x_3)` are
linearly independent.

{docstring MilnorAlgDep.CharPHyp.linearIndependent_Δhom_x}

The blueprint then uses the $`p^2 + p + 1 \geq 7` lines $`F\bigl(\sum_j i_j \Delta(x_j)\bigr)`,
$`(i_1 : i_2 : i_3) \in \mathbf P^2(\FF_p)`.
Four lines suffice: if $`e_1, e_2, e_3` are linearly independent, any two of the four vectors
$`e_1, e_2, e_3, e_1 + e_2 + e_3` are linearly independent, and a line contains at most one of two
linearly independent vectors; so each of three given lines contains at most one of the four
vectors, and one of the four lies on none of them.
Applied to $`e_i = \Delta(x_i)`, this gives one of the monomials $`x_1, x_2, x_3, x_1 x_2 x_3`.

{docstring MilnorAlgDep.exists_notMem_span_four}

{docstring MilnorAlgDep.CharPHyp.exists_Δhom_notMem_span}

So the hypotheses (H0)–(H3) of Step B hold, (H0) because $`\psi(-1) = 0`:

{docstring MilnorAlgDep.CharPHyp.data}

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
{name}`Char0Hyp.τ_mem_pointV`, and in characteristic $`p` it is
{name}`CharPHyp.τ_mem_pointV`, both proved in Step C.

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

In characteristic $`p`, applied to {name}`CharPHyp.data`, and composed with the inclusion
$`F \subset L`:

{docstring MilnorAlgDep.CharPHyp.τ}

{docstring MilnorAlgDep.CharPHyp.ringChar_eq}

## Primitive roots
%%%
tag := "ss:roots"
%%%

From now on $`K` and $`L` have the same characteristic exponent $`p` (in characteristic $`p`,
{name}`CharPHyp.charP_K`), and $`\Frob` denotes the Frobenius of either field; $`\tau` commutes
with $`\Frob`.
In characteristic $`0` the rest of this section is empty: $`K_0 = K` and every $`x \in K \sm k` is
primitive.
For $`x \in K \sm k` we have $`\psi(\Frob x) = p\, \psi(x)`, which has height
$`\hgt \psi(x) + 1` if $`p > 1`.
Since $`K` is perfect, this shows:

* *(eq:roots)* $`\Frob(K_0) \subset K_0` and $`K = \bigcup_{j \in \Gamma_{\geq 0}} \Frob^{-j}(K_0)`;
  every $`x \in K_0 \sm k` can be written uniquely as $`x = \Frob^j(x_0)` with $`x_0` primitive and
  $`j \in \Gamma_{\geq 0}`, namely $`j = \hgt \psi(x)`.

We call $`x_0` the _primitive root_ of $`x`; then $`\tau(x) = \Frob^j(t(x_0))`.
That $`\Frob(K_0) \subset K_0` holds because $`K_0` is a subfield
({name}`CharPHyp.pow_mem_K₀`).

{docstring MilnorAlgDep.CharPHyp.exists_pow_pow_mem_K₀}

{docstring MilnorAlgDep.CharPHyp.exists_primitive_root}

{docstring MilnorAlgDep.CharPHyp.hgtV_pow_pow_of_primitive}

_Proof._
If $`p^j \psi(x) = \psi(x^{p^j})` lies in $`W`, then $`x^{p^j} \in K_0`; such a $`j` exists by
{cref "lem:W"}[] (c), $`V = \bigcup_j p^{-j} W`.
For $`x \in K_0 \sm k` let $`j = \hgt \psi(x) \geq 0` and let $`x_0` be the $`p^j`-th root of $`x`
in the perfect field $`K`; then $`x_0 \notin k` and $`\hgt \psi(x_0) = \hgt \psi(x) - j = 0`, so
$`x_0 \in K_0` is primitive.
Uniqueness: $`\hgt \psi(x_0^{p^j}) = j` for primitive $`x_0`.

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

Here $`\Gamma = \ZZ`, $`F = L_A` is the adapted model of {ref "ss:modelP"}[Section 6.3.2],
$`\FF = \FF_p`, and $`K` has characteristic $`p`.
The statements quantify over elements of $`K_0` (`x : H.K₀ p`); "$`x` is primitive" is
`(H.data p).Δ x ≠ 0`.

_The eigenvalue lemma in a model._
Lemmas 6.10, 6.11 and Proposition 6.12 apply {cref "lem:R"}[] in the following form.
Let $`a \in F` with $`da \neq 0` in $`\Omega_A`, and let $`E` be the field of elements of $`L`
separable algebraic over $`l(a)` (the model of the one-element family $`(a)`, contained in $`F`).
By (S2), $`\Omega_{E|l}` has the basis $`da`, and the derivation $`\delta` of $`E` with
$`df = \delta(f)\, da/a` satisfies $`\delta(a) = a`.
If $`b \in E^\times` and $`\dlog b = \kappa \dlog a` in $`\Omega_A` with $`\kappa \in l`, then
$`\delta(b) = \kappa b`, so $`\kappa \in \FF_p` by the eigenvalue lemma.
The blueprint notes that $`\Omega_{E|l} \to \Omega_A` is injective because $`da \neq 0`; the formal
proof of this lemma does not need this (although the docstring below mentions it): it pushes
$`db = f\, da` forward to $`\Omega_A` and compares there, using only $`da \neq 0` in
$`\Omega_A`.

{docstring MilnorAlgDep.exists_intCast_of_modelDLog_eq}

_Proof of {cref "lem:tauinQ"}[]._
For primitive $`x`, $`\tau(x) = t(x) = \mu(x)/(\mu(x) - 1) \in Q_x` because $`\mu(x) \in Q_x`
({cref "lem:K0"}[] (b)).
For $`x \in K_0 \sm k` with primitive root $`x_0`, $`\tau(x) = \tau(x_0)^{p^j}` lies in
$`Q_{x_0} = Q_x`.

{docstring MilnorAlgDep.CharPHyp.τ_mem_pointV}

For $`c \in k^\times` and $`x \in K_0 \sm k` we have $`cx \in K_0 \sm k` and $`Q_{cx} = Q_x`, so
$`\tau(c) = \tau(cx)/\tau(x) \in Q_x`.
The blueprint takes two transverse $`x`; the formal proof takes $`x = x_1` and $`x = x_2`, whose
points meet in $`l`.

{docstring MilnorAlgDep.CharPHyp.τ_mem_range_of_mem}

Suppose $`\tau(x) \in l` for some $`x \in K_0 \sm k`.
If $`x_0` is the primitive root of $`x`, then $`\tau(x_0)^{p^j} \in l`, so $`\tau(x_0)` is
algebraic over $`l` and lies in $`l`; so we may assume that $`x` is primitive, and put
$`c = \tau(x) = t(x) \in l`.
Then $`\kappa = \mu(x) = c/(c - 1)` lies in $`l`.
Let $`(N, a)` and $`(M, b)` be the chosen representatives of $`\psi(x)` and $`\psi(1 - x)`.
Both have height $`0` in the same point $`Q_x`, so $`b \approx a` ({name}`sepEquiv_of_hgt_eq`), and
$`\Delta(1 - x) = \kappa \Delta(x)` reads
$$`\dlog b = \frac{M\kappa}{N} \dlog a \qquad \text{in } \Omega_A.`
By the eigenvalue lemma, $`M\kappa/N` is the image of an integer; as $`M, N` are prime to $`p`, so
is $`\kappa`: $`\kappa = n` with $`n \in \ZZ`.
Then $`\tau(x) = n/(n - 1) = \tau\bigl(n/(n-1)\bigr)`, and since $`\tau` is injective,
$`x = n/(n-1)` lies in the prime field of $`K`, which is contained in $`k`: a contradiction.
(The blueprint uses representatives with a common denominator, and argues that $`\tau` maps the
prime field of $`K` onto $`\FF`.)

{docstring MilnorAlgDep.CharPHyp.τ_notMem_range}

_Proof of {cref "lem:theta"}[] (as formalized)._
The steps are those of the blueprint, but $`e_0 = 0` is shown before $`\theta \in l`.

1. _The height of_ $`\tau(x)` _is constant on primitive elements._
   Let $`x, y` be transverse, and $`(N, a)`, $`(M, b)` the chosen representatives of $`\psi(x)`,
   $`\psi(y)`.
   Then $`(NM, a^M b^N)` represents $`\psi(xy)`, and $`a^M, b^N` have height $`0`
   ($`a^M \approx a`, $`b^N \approx b`).
   Since $`Q_x \neq Q_y` ({name}`CharPHyp.pointV_ne_of_transverse`), $`(a^M, b^N, a^M b^N)` is a
   normalized triple of $`(Q_x, Q_y, Q_{xy})` ({name}`isNormalized_mul`).
   So is $`(\tau x, \tau y, \tau(xy))`, because $`\tau(xy) = \tau(x)\tau(y)` and
   $`\tau(x) \in Q_x \sm l`, $`\tau(y) \in Q_y \sm l` by {cref "lem:tauinQ"}[].
   By {cref "lem:normalized"}[] (b), $`\hgt \tau(x) = \hgt \tau(y)`.
   Since any two primitive elements are transverse to a common third one, the height of
   $`\tau(x)` is a constant $`e_0` on primitive elements.
   (The blueprint uses representatives with a common denominator $`N`.)

   {docstring MilnorAlgDep.CharPHyp.hgt_τ_eq_of_transverse}

2. _The coefficient is constant._
   So $`\sigma_x = \Frob^{-e_0} \tau(x)` is a model generator of $`Q_x`, and
   $`\Delta(x) = \theta(x) \dlog \sigma_x` with $`\theta(x) \in F^\times`, since both vectors span
   $`\omega_A(Q_x)`.
   For transverse $`x, y` we have $`\sigma_{xy} = \sigma_x \sigma_y`, so
   $$`\theta(xy)\bigl(\dlog \sigma_x + \dlog \sigma_y\bigr) = \theta(x) \dlog \sigma_x + \theta(y) \dlog \sigma_y,`
   and $`\theta(x) = \theta(y)` because $`\dlog \sigma_x, \dlog \sigma_y` are linearly independent.
   Comparing with a common transverse element as in step 1, $`\theta` is a constant.

   {docstring MilnorAlgDep.CharPHyp.exists_hgt_τ_coeff}

3. $`e_0 = 0`.
   For primitive $`x`, $`\sigma_{1-x} = 1 - \sigma_x`, and
   $`\dlog(1 - \sigma) = -\frac{\sigma}{1 - \sigma} \dlog \sigma`, so
   $$`\Delta(1 - x) = \theta \dlog(1 - \sigma_x) = \frac{\sigma_x}{\sigma_x - 1}\, \Delta(x),
     \qquad\text{that is,}\qquad \mu(x) = \frac{\sigma_x}{\sigma_x - 1},`
   and hence $`\tau(x) = t(x) = \sigma_x = \Frob^{-e_0}\tau(x)`.
   Since $`\hgt \Frob^{-e_0}\tau(x) = \hgt \tau(x) - e_0`, this forces $`e_0 = 0`.
   So $`\tau(x)` is a model generator of $`Q_x` for every primitive $`x`; in particular
   $`d\tau(x) \neq 0`.

   {docstring MilnorAlgDep.CharPHyp.hgt_τ_eq_zero}

4. $`\theta \in \FF_p^\times`.
   For primitive $`x` and $`v \in W \cap G_{Q_x}`, we have $`\dlog_A(v) = c \dlog \tau(x)` with
   $`c \in F \cap Q_x`: a representative $`(N, a)` of $`v \neq 0` has $`a \in Q_x \cap F`, so $`a`
   is separable algebraic over $`l(\tau(x))`, because $`\tau(x)` is a model generator of $`Q_x` and
   $`\hgt a \geq 0` ({name}`isSeparable_of_hgt_le`); hence $`da = c'\, d\tau(x)` with $`c'` in the
   field of elements separable algebraic over $`l(\tau(x))`, which is contained in $`Q_x`.
   With $`v = \psi(x)` this shows $`\theta \in Q_x` for every primitive $`x`, so
   $`\theta \in Q_{x_1} \cap Q_{x_2} = l`.
   Finally the eigenvalue lemma, for $`\tau(x_1)` and the representative of $`\psi(x_1)`, shows that
   $`N\theta` is the image of an integer, hence so is $`\theta`; and $`\theta \neq 0` because
   $`\Delta(x_1) \neq 0` ({name}`CharPHyp.exists_intCast_of_dlogA_eq`).

   {docstring MilnorAlgDep.CharPHyp.exists_dlogA_eq_smul}

In the formal statement, $`\theta` is an integer which is non-zero in $`L`, that is, prime to
$`p`:

{docstring MilnorAlgDep.CharPHyp.exists_θ}

_Proof of {cref "prop:rational"}[] for $`\Gamma = \ZZ` (as formalized)._
On $`K_0^\times` let $`\psi_0` be the restriction of $`\psi` ({name}`CharPHyp.ψ₀`), and $`[\tau]`
the homomorphism $`x \mapsto [\tau(x)]` ({name}`CharPHyp.τV`).
It takes values in $`W`, because $`\tau(x) \in F`; it vanishes on $`k^\times` by
{cref "lem:tauinQ"}[]; and $`\dlog_A [\tau(x)] = \dlog \tau(x)` ({name}`CharPHyp.dlogA_τV`).

_Step 1: lifting modulo p._
* *(eq:lift)* If $`\psi' \colon K_0^\times \to W` is a homomorphism with $`\psi'(k^\times) = 0`
  and $`\psi'(x) \in G_{Q_x}` for all $`x \in K_0 \sm k`, then there is an integer $`m` with
  $`(\psi' - m[\tau])(K_0^\times) \subset pW`.

{docstring MilnorAlgDep.CharPHyp.exists_lift}

For primitive $`x`, step 4 of the proof of {cref "lem:theta"}[], with $`v = \psi'(x)`, gives
$`\dlog_A \psi'(x) = c(x) \dlog \tau(x)` with $`c(x) \in F \cap Q_x`.
As in step 2 there, $`c` is constant on primitive elements: for transverse $`x, y` compare
$`\dlog_A \psi'(xy) = c(xy)(\dlog \tau(x) + \dlog \tau(y))` with
$`c(x) \dlog \tau(x) + c(y) \dlog \tau(y)`, where $`\dlog \tau(x), \dlog \tau(y)` are linearly
independent, being non-zero multiples of $`\Delta(x), \Delta(y)` by {cref "lem:theta"}[].
So the constant lies in $`Q_{x_1} \cap Q_{x_2} = l`, and in $`\FF_p` by the eigenvalue lemma
({name}`CharPHyp.exists_intCast_of_dlogA_eq` with $`v = \psi'(x_1)`); let $`m \in \ZZ` be a lift.
Then $`\dlog_A\bigl(\psi'(x) - m[\tau(x)]\bigr) = 0` for primitive $`x`, so
$`\psi'(x) - m[\tau(x)] \in pW` by {cref "lem:W"}[] (c).
For $`x = \Frob^j(x_0)` as in (eq:roots) the same element is $`p^j` times the one for $`x_0`, and
for $`x \in k^\times` it is zero.

_Step 2: p-adic approximation._
* *(eq:padic)* For every $`j \geq 0` there is an integer $`r_j` with
  $`\psi - r_j[\tau] \in p^j W` on $`K_0^\times`.

{docstring MilnorAlgDep.CharPHyp.exists_padic}

The proof is by induction on $`j`, with $`r_0 = 0`, since $`\psi(K_0^\times) \subset W`.
Given $`r_j`, the homomorphism $`\psi_j = p^{-j}(\psi - r_j[\tau])` ($`V` is uniquely divisible)
takes values in $`W`, vanishes on $`k^\times`, and $`\psi_j(x) \in G_{Q_x}` for $`x \notin k`,
because $`\psi(x)` and $`[\tau(x)]` lie in $`G_{Q_x}` ({cref "lem:tauinQ"}[]).
By (eq:lift) there is $`m` with $`\psi_j - m[\tau] \in pW`, and $`r_{j+1} = r_j + p^j m` works.
The blueprint keeps the integers $`m_j` and puts $`r_j = \sum_{i < j} m_i p^i`, so that the $`r_j`
are compatible and converge $`p`-adically.
Compatibility is never used: the rest of the proof works with each $`j` separately, and the formal
statement is "for every $`j` there is $`r_j`".

_Step 3: a norm computation._
Fix the primitive element $`u = x_1`, put $`s = \tau(u)`, and let $`(N, a)` be the chosen
representative of $`\psi(u)`.
Both $`s` and $`a` are model generators of $`Q_u` (step 3 of the proof of {cref "lem:theta"}[]),
so $`a` is separable algebraic over $`l(s)` ({name}`CharPHyp.isSeparable_ρ_of_primitive`).
Let $`E = l(s, a) \subset F`.
Since $`ds \neq 0` in $`\Omega_A`,
$$`E \cap L_A^{\,p^j} = E^{p^j} \qquad (j \geq 0). \qquad \text{(eq:Epower)}`
Indeed, if $`y \in E` is $`z^p` with $`z \in L_A`, then $`dy = 0` in $`\Omega_A`.
The map $`\Omega_{E|l} \to \Omega_A` is injective: $`\Omega_{E|l} = E\, ds` by (S2), as $`E` is
separable algebraic over $`l(s)`, and $`ds \neq 0` in $`\Omega_A`
({name}`kaehler_map_injective_of_ne_zero`).
So $`dy = 0` in $`\Omega_{E|l}`, and $`y = w^p` with $`w \in E` by (S3); then $`z = w`.
Induction on $`j` gives the claim.

{docstring MilnorAlgDep.mem_of_pow_pow_mem}

By (eq:padic), $`\psi(u) - r_j[s] = p^j w_j` with $`w_j \in W`, so
$`p^j (N w_j) = [a\, s^{-N r_j}]`.
Let $`(M_j, g)` be a representative of $`N w_j` with $`g \in L_A`; it exists by the definition of
$`W`, also when $`N w_j = 0`.
Then $`(a\, s^{-N r_j})^{M_j} = c\, g^{p^j}` with $`c \in l^\times` by (V1), and $`g \in E` by
(eq:Epower), since $`g^{p^j} = c^{-1} (a\, s^{-N r_j})^{M_j} \in E`.
So for every $`j`,
$$`\bigl(a\, s^{-N r_j}\bigr)^{M_j} \in l^\times \cdot E^{p^j}, \qquad M_j \text{ prime to } p.`

{docstring MilnorAlgDep.exists_pow_eq_mul_pow_pow}

{docstring MilnorAlgDep.CharPHyp.exists_pow_eq_of_padic}

Now take norms from $`E` to $`l(s)`, a rational function field since $`s` is transcendental.
Let $`M = [E : l(s)]` and $`f = N_{E|l(s)}(a)`.
The blueprint writes $`f = c_0\, s^{\varepsilon} \prod_P P^{\varepsilon_P}` and compares the
exponents of $`s` in $`l[s]`, by unique factorization.
All that is needed is a homomorphism $`l(s)^\times \to \ZZ` which is trivial on $`l^\times` and
takes the value $`1` at $`s`; the formal proof uses the degree on $`l(s) \cong l(X)` (Mathlib's
`RatFunc.intDegree`, the order at $`\infty` up to sign) instead of the order at $`s`.
So $`x \mapsto \deg N_{E|l(s)}(x)` is a homomorphism $`E^\times \to \ZZ` which vanishes on
$`l^\times`, takes the value $`M` at $`s`, and is divisible by $`p^j` on $`(E^\times)^{p^j}`
({name}`normDegHom`).
With $`\varepsilon = \deg f`, applying it to the relation above gives
$`M_j (\varepsilon - M N r_j) \in p^j \ZZ`, and since $`M_j` is prime to $`p`,
$$`\varepsilon \equiv M N r_j \pmod{p^j} \qquad \text{for all } j \geq 0.`

{docstring MilnorAlgDep.exists_dvd_sub_of_forall_pow_eq}

_Step 4: conclusion._
The blueprint writes $`MN = p^\beta n'` with $`p \nmid n'`; taking $`j \geq \beta` shows
$`p^\beta \mid \varepsilon`, say $`\varepsilon = p^\beta m'`, and then
$`n' r_j \equiv m' \pmod{p^{j - \beta}}` for all $`j \geq \beta`.
The formal proof follows this:

{docstring MilnorAlgDep.exists_dvd_sub_of_dvd}

(The factorization is not needed: the same conclusion holds with $`\beta = 0`, $`n' = MN` and
$`m' = \varepsilon`, by the congruence of step 3.)
By (eq:padic), $`n'\psi - m'[\tau] = (n' r_j - m')[\tau] + n' p^j w_j` maps $`K_0^\times` into
$`p^{j - \beta} W` for all $`j \geq \beta`, as $`[\tau]` takes values in $`W`; hence into
$`\bigcap_j p^j W = 0` ({cref "lem:W"}[] (c)).

{docstring MilnorAlgDep.CharPHyp.zsmul_ψ₀_eq_of_dvd}

So $`\psi = \frac{m'}{n'}[\tau]` on $`K_0^\times`, and $`m' \neq 0` because $`\psi(u) \neq 0`:

{docstring MilnorAlgDep.CharPHyp.exists_rat_ψ₀_eq}

# End of the proof
%%%
tag := "ss:end"
%%%

By (eq:roots) and since $`L` is perfect, $`\tau` extends uniquely to a field embedding
$`\tau \colon K \to L` commuting with Frobenius, and $`\psi = r[\tau]` holds on $`K^\times` because
$`V` is uniquely divisible; in characteristic $`0` there is nothing to extend, as $`K_0 = K`.
By {cref "lem:tauinQ"}[], $`\tau^{-1}(l) = k`.
If $`x \in K` is algebraic over $`k`, then $`\tau(x)` is algebraic over $`l`, so $`\tau(x) \in l`
and $`x \in k`; thus $`k` is relatively algebraically closed.
In characteristic $`0` this gives the existence part of Theorem A, with no reduction to perfect
fields and without (A4):

{docstring MilnorAlgDep.theoremA_perfect_of_charZero}

In characteristic $`p`, $`K` is $`p`-radical over $`K_0` by (eq:roots): every $`x \in K` has a
power $`x^{p^j}` in $`K_0`.
So Mathlib's `PerfectRing.lift` extends $`\tau \colon K_0 \to L` to $`K`, as $`L` is perfect:

{docstring MilnorAlgDep.CharPHyp.τK}

For $`x \in K^\times` choose $`j` with $`y = x^{p^j} \in K_0`; then
$`p^j \psi(x) = \psi(y) = r[\tau(y)] = r[\tau(x)^{p^j}] = p^j r[\tau(x)]`, and $`p^j` cancels:

{docstring MilnorAlgDep.CharPHyp.exists_rat_ψ_eq}

If $`x \notin k` and $`x^{p^j} \in K_0`, then $`x^{p^j} \notin k`, so
$`\tau(x)^{p^j} = \tau(x^{p^j}) \notin l` by {cref "lem:tauinQ"}[], and $`\tau(x) \notin l`:

{docstring MilnorAlgDep.CharPHyp.τK_mem_range_iff}

{docstring MilnorAlgDep.CharPHyp.isRelAlgClosed_k}

Together with {cref "prop:tau"}[] ({name}`CharPHyp.ringChar_eq`) this is the existence part of
Theorem A in characteristic $`p`, for perfect fields.
The hypotheses are those of {name}`theoremA_perfect`, plus `[PerfectField K]` and
$`\chr L \neq 0`; in particular $`K` and $`L` are not assumed to have the same characteristic.
The proof turns (A3) with $`d = 3` into a {name}`CharPHyp` and applies the results above:

{docstring MilnorAlgDep.theoremA_core_charP}

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

Here the blueprint takes logarithmic differentials in $`E = l(S, S')` (its $`S` is our $`T`) and
divides; the formal
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
         └─ theoremA_core_charP          CharP/Main.lean
            │   H : CharPHyp K l L
            ├─ CharPHyp.ringChar_eq      CharP/AdaptedModel.lean
            ├─ CharPHyp.isRelAlgClosed_k CharP/Main.lean
            ├─ CharPHyp.τK_mem_range_iff CharP/Main.lean
            └─ CharPHyp.exists_rat_ψ_eq  CharP/Main.lean
               └─ CharPHyp.exists_rat_ψ₀_eq   CharP/StepC.lean

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
The characteristic $`p` proof is the content of `MilnorAlgDep/CharP/`.
On top of the files for {ref "sec:levels"}[Chapters 3–5] it consists of, in order of
dependence: `LevelV.lean` (levels and heights in $`V`, {name}`CharPHyp`, (eq:sum);
{ref "ss:notationP"}[Section 6.1.1]), `StepA.lean` ({cref "prop:levels"}[],
Lemmas 6.2 and 6.3), `AdaptedModel.lean` ($`W`, $`\dlog_A`, $`K_0`, Lemmas 6.4 and 6.5, and
$`\tau \colon K_0 \to L` from the abstract Step B), `StepCFields.lean` (the statements of
Step C about $`L|l` alone: the eigenvalue lemma in a model, (eq:Epower), the norm argument),
`StepC.lean` ((eq:roots), {cref "lem:tauinQ"}[], {cref "lem:theta"}[], {cref "prop:rational"}[])
and `Main.lean` ({ref "ss:end"}[Section 6.7]).
