import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite
open MilnorAlgDep

set_option pp.rawOnError true

#doc (Manual) "Conventions and standard facts" =>
%%%
tag := "sec:conv"
%%%

This chapter fixes the language of points and flats, the bookkeeping of Frobenius twists, and
the group $`V_{L|l}`, and collects the standard facts from field theory that the proof uses.

In Lean, a field extension $`L|l` is usually given as two fields with `[Algebra l L]`, so that
Mathlib's notions (`AlgebraicIndependent l`, `IsSeparable`, `IntermediateField l L`,
`Ω[L⁄l]`) apply directly; the main theorems take a subfield `l : Subfield L` instead, which Lean
coerces to a field with an algebra structure.

# Points and flats
%%%
tag := "ss:points"
%%%

Let $`L` be a field and $`l \subset L` a relatively algebraically closed subfield.
A _flat_ of $`L|l` is a relatively algebraically closed subfield of $`L` containing $`l`; its
_rank_ is its transcendence degree over $`l`.
A _point_ is a flat of rank $`1` and a _line_ is a flat of rank $`2`.
For $`a \in L \sm l` we write $`Q_a` for the point containing $`a`, the relative algebraic
closure of $`l(a)` in $`L`.
For points $`P_1, \dots, P_m` we write $`\la P_1, \dots, P_m \ra` for the flat they generate;
they are _collinear_ if this flat has rank at most $`2`.
Two distinct points intersect in $`l`, and two distinct lines through a point $`P` intersect
in $`P`.

{docstring MilnorAlgDep.point}

So `point l a` is an intermediate field of $`L|l`, defined for every $`a`.
It is relatively algebraically closed in $`L` ({name}`point_isRelAlgClosed`), and,
as a set, it is the closure of $`\{a\}` in the algebraic matroid of $`L|l`
({name}`coe_point`).
The matroid gives the basic facts about points quickly:

{docstring MilnorAlgDep.point_eq_point_iff_not_algebraicIndependent}

{docstring MilnorAlgDep.point_inf_point_eq_bot}

Flats of higher rank, lines and collinearity are used only in positive characteristic
({ref "sec:levels"}[Chapters 3–5] and {cref "sec:stepA"}[]) and are formalized there.

# Frobenius and the group Γ
%%%
tag := "ss:frobenius"
%%%

For a perfect field $`L` let $`p` be its characteristic exponent ($`p = 1` in characteristic
$`0`) and $`\Frob \colon x \mapsto x^p` its Frobenius automorphism.
We put $`\Gamma = \ZZ` if $`p > 1` and $`\Gamma = \{0\}` if $`p = 1`, and
$`\Gamma_{\geq 0} = \{ j \in \Gamma : j \geq 0 \}`; all integers measuring Frobenius twists are
elements of $`\Gamma`.
We write $`\FF` for the prime field of the field under consideration.

In Lean the characteristic exponent is Mathlib's `ringExpChar L` and the Frobenius automorphism
of a perfect field is `frobeniusEquiv L (ringExpChar L)`, a ring automorphism whose integer powers
are the $`\Frob^j`, $`j \in \ZZ`.
In characteristic $`0` it is the identity.
So the group $`\Gamma` does not appear: statements quantify over $`j \in \ZZ`, and in
characteristic $`0` all $`j` give the same map.
The files for positive characteristic write {name}`frobZ` `L p j` for $`\Frob^j`.
Two characteristic functions occur in the formal statements: `ringChar L` (which is $`0` in
characteristic $`0`) in hypotheses (A3) and (A4), which distinguish characteristic $`0` from
positive characteristic, and `ringExpChar L` (which is $`1` in characteristic $`0`) wherever the
blueprint's $`p` appears.
On classes, $`[\Frob^j(y)] = p^j [y]`:

{docstring MilnorAlgDep.cls_frobeniusEquiv_zpow}

# The group V
%%%
tag := "ss:V"
%%%

For a subgroup $`H` of $`L^\times`, the formalization works with the $`\QQ`-vector space
$`(L^\times / H) \otimes_\ZZ \QQ`, written additively.

{docstring MilnorAlgDep.VOf}

{docstring MilnorAlgDep.VOf.cls}

The two cases used are $`H = l^\times`, which gives $`V_{L|l}`, and $`H = 1`, which gives
$`L^\times_\QQ = L^\times \otimes \QQ = \Kr_1(L)` of {ref "sec:K"}[Chapter 7].

{docstring MilnorAlgDep.V}

Here {name}`constUnits` `l L` is the image of $`l^\times` in $`L^\times`.
Since $`\QQ \otimes_\ZZ M` is the localization of an abelian group $`M` at the non-zero integers,
every element of `VOf H` has the form $`\frac1n [a]` ({name}`VOf.exists_nsmul_eq_cls`),
and $`[a] = 0` if and only if $`a^n \in H` for some $`n \geq 1`
({name}`VOf.cls_eq_zero_iff`).
"Relatively algebraically closed" is the class {name}`IsRelAlgClosed` in internal
results; the main theorems spell it out as `∀ x : L, IsAlgebraic l x → x ∈ l`.

Now let $`L` be perfect, $`l \subset L` relatively algebraically closed, and $`V = V_{L|l}`.

1. *(V1)* $`[a] = 0` in $`V` if and only if $`a \in l^\times`, because $`L^\times/l^\times` is
   torsion-free.
2. *(V2)* Every $`v \in V \sm 0` has a _representative_: a pair $`(N, a)` with $`N \geq 1` an
   integer prime to $`p` and $`a \in L \sm l` such that $`Nv = [a]`.
   Indeed $`v = \frac1n [b]` with $`n = p^j n'`, and one takes $`N = n'`,
   $`a = \Frob^{-j}(b)`.
   If $`(N', a')` is another representative then $`a^{N'} = c\,a'^{N}` with $`c \in l^\times`.
3. *(V3)* Consequently the point $`Q_v = Q_a` depends only on $`v`.
   For a point $`Q`, the set $`G_Q = \{ v : v = 0 \text{ or } Q_v = Q \}` is a subgroup of $`V`,
   the image of $`(Q^\times / l^\times) \otimes \QQ`.
   Elements $`v_1, \dots, v_m \in V \sm 0` are _algebraically independent_ if their
   representatives are; $`v, v'` are dependent if and only if $`Q_v = Q_{v'}`.

For a homomorphism $`\psi \colon K^\times \to V` and $`x \notin \ker \psi` we write
$`Q_x = Q_{\psi(x)}`, and we call $`x_1, \dots, x_m` _$`\psi`-independent_ if
$`\psi(x_1), \dots, \psi(x_m)` are algebraically independent.

{docstring MilnorAlgDep.V.cls_eq_zero_iff}

{docstring MilnorAlgDep.V.exists_rep_coprime}

Representatives are not required to be prime to $`p` elsewhere in Lean
({name}`V.exists_rep` drops this condition, and does not need $`L` perfect); the
uniqueness statement is {name}`V.rep_unique`.

{docstring MilnorAlgDep.VAlgIndep}

{docstring MilnorAlgDep.VAlgIndep.iff_of_nsmul_eq_cls}

_Proof of independence of the choices._
If $`M[a] = N[b]` with $`M \geq 1`, then $`a^{Mk} = c\, b^{Nk}` for some $`k \geq 1` and
$`c \in l`, so $`a` is algebraic over $`l(b)`
({name}`V.isAlgebraic_adjoin_of_zsmul_cls_eq`).
Two families $`(a_i)`, $`(b_i)` such that each $`a_i` is algebraic over $`l(b_i)` and each $`b_i`
over $`l(a_i)` are algebraically independent together or not at all
({name}`algebraicIndependent_of_isAlgebraic_adjoin`): in the algebraic matroid,
$`a_i` and $`b_i` have the same closure.

The point $`Q_v` is defined through one chosen representative, and shown to be independent of
the choice:

{docstring MilnorAlgDep.pointV}

{docstring MilnorAlgDep.vAlgIndep_pair_iff}

The subgroup $`G_Q` is {name}`pointGroup` `Q`, and
{name}`mem_pointGroup_point_iff` says that $`G_Q = \{0\} \cup \{v : Q_v = Q\}`.

## Perfect closures
%%%
tag := "ss:perfectClosure"
%%%

The blueprint replaces $`L` and $`l` by their perfect closures, using $`V_{L|l} = V_{L^i|l^i}`.
In Lean, $`L^i` is any field $`M` with `[Algebra L M]` that is a perfect closure of $`L` in the
sense of Mathlib (`IsPerfectClosure (algebraMap L M) p`, where $`p` is the characteristic
exponent), and $`l^i` is defined inside $`M`:

{docstring MilnorAlgDep.perfectClosureIn}

{docstring MilnorAlgDep.V.toPerfectClosure_bijective}

_Proof._
Injectivity: if $`[a]` becomes $`0` in $`V_{L^i|l^i}`, then $`a^{k p^m} \in l` for some
$`k \geq 1` and $`m`, so $`[a] = 0` in $`V_{L|l}`.
Surjectivity: every $`b \in M^\times` has a power $`b^{p^m}` in $`L`, so
$`[b] = p^{-m}[b^{p^m}]` is in the image.

The comparison map also preserves and reflects algebraic independence
({name}`V.vAlgIndep_toPerfectClosure_iff`), and $`l^i` is relatively algebraically
closed in $`L^i` if $`l` is relatively algebraically closed in $`L`
({name}`perfectClosureIn_isRelAlgClosed`).

# Standard facts
%%%
tag := "ss:standard"
%%%

:::lem "2.1" (title := "Standard facts") (tag := "lem:standard")
Let $`l` be a perfect field of characteristic exponent $`p`.

* *(S1)* Let $`f \in l[Y_1, \dots, Y_m]`.
  If $`\partial f / \partial Y_1 = 0`, then $`Y_1` does not occur in $`f`, or $`p > 1` and
  $`f \in l[Y_1^p, Y_2, \dots, Y_m]`.
  If all partial derivatives of $`f` vanish, then $`f` is constant, or $`p > 1` and $`f` is a
  $`p`-th power.
* *(S2)* Let $`E \supset l` be a field which is separable algebraic over $`l(A)` for an
  algebraically independent set $`A`.
  Then $`\{ da : a \in A \}` is a basis of $`\Omega_{E|l}`, and $`d(\Frob y) = 0` for $`y \in E`
  if $`p > 1`.
  If $`y \in E` is separable algebraic over $`l(x_1, \dots, x_r) \subset E`, then
  $`dy \in \sum_i E\, dx_i`; more precisely $`g_Y\, dy + \sum_i g_{X_i}\, dx_i = 0` for every
  polynomial relation $`g(x_1, \dots, x_r, y) = 0` over $`l`.
* *(S3)* In the situation of (S2) assume moreover that $`l` is relatively algebraically closed
  in $`E`, and let $`y \in E \sm l`.
  Then there is a largest $`j \in \Gamma_{\geq 0}` with $`\Frob^{-j}(y) \in E`, and
  $`d(\Frob^{-j} y) \neq 0`.
  In particular, if $`dy = 0` then $`p > 1` and $`y \in \Frob(E)`.
:::

The Lean docstrings in `MilnorAlgDep/Standard/Differentials/` cite this lemma as "Lemma 2.3";
it is Lemma 2.1 of the blueprint.
In Lean, $`\Omega_{E|l}` is Mathlib's `Ω[E⁄l]`, the differential is `KaehlerDifferential.D l E`,
the set $`A` is a family `a : ι → E` with `AlgebraicIndependent l a`, and "$`E` is separable
algebraic over $`l(A)`" is the hypothesis
`hsep : Algebra.IsSeparable (IntermediateField.adjoin l (Set.range a)) E`.
In applications $`E` is an intermediate field of a larger field, typically the field of elements
of $`L` separable algebraic over $`l(A)`
({name}`isSeparable_adjoin_restrictFamily_separableClosure`).

## (S1): polynomials with vanishing derivatives

{docstring MilnorAlgDep.exists_eq_pow_of_pderiv_eq_zero}

_Proof._
The coefficient of $`Y^{m - e_i}` in $`\partial f / \partial Y_i` is $`m_i c_m`, where $`c_m` is
the coefficient of $`Y^m` in $`f`.
So if all partial derivatives vanish, every exponent occurring in $`f` is divisible by $`p`:
$`f = g(Y_1^p, \dots, Y_m^p)` ({name}`exists_expand_eq_of_pderiv_eq_zero`).
Taking $`p`-th roots of the coefficients of $`g`, which is possible since $`l` is perfect, gives
$`f = h^p`.
In characteristic $`0` the same computation shows that $`f` is constant
({name}`eq_C_of_pderiv_eq_zero`); the statements for a single variable are
{name}`notMem_vars_of_pderiv_eq_zero` and
{name}`dvd_of_mem_support_of_pderiv_eq_zero`.

## (S2): a basis of the differentials

{docstring MilnorAlgDep.kaehlerBasis}

_Proof._
The evaluation map $`l[X_a : a \in A] \to l(A)` is a localization, hence formally étale, and
$`E` is separable algebraic over $`l(A)`, hence formally étale over $`l(A)`; no finiteness is
needed for either.
So $`\Omega_{E|l} = E \otimes \Omega_{l[X]|l}` (Mathlib's
`KaehlerDifferential.isBaseChange_of_formallyEtale`), and the latter has the basis
$`1 \otimes dX_a`.

The chain rule gives $`\sum_i g_{X_i}(x)\, dx_i = 0` for every relation $`g(x) = 0`
({name}`sum_pderiv_smul_derivation_eq_zero`), and $`d(y^p) = p y^{p-1} dy = 0`
({name}`kaehler_D_pow_char`).

{docstring MilnorAlgDep.kaehler_D_mem_span_range_of_isSeparable}

_Proof._
Let $`F = l(x_1, \dots, x_r)`.
Applying the differential of $`\Omega_{E|F}` to the minimal polynomial $`f` of $`y` over $`F`
gives $`f'(y)\, dy = 0` in $`\Omega_{E|F}`, and $`f'(y) \neq 0` since $`y` is separable; so
$`dy` lies in the kernel of $`\Omega_{E|l} \to \Omega_{E|F}`, which is the $`E`-span of
$`dF` by the exact sequence $`E \otimes \Omega_{F|l} \to \Omega_{E|l} \to \Omega_{E|F} \to 0`
({name}`kaehler_D_mem_span_of_isSeparable`).

## (S3): roots of elements with vanishing differential

The formal proof has two steps: first the kernel of $`d` is $`E^p`, then an element outside $`l`
is not a $`p^j`-th power for every $`j`.
The blueprint calls the first step standard; for the second it uses a discrete valuation, which
the formal proof replaces by an argument with differentials.

{docstring MilnorAlgDep.kaehler_D_eq_zero_iff_exists_pow_eq}

_Proof._
Let $`F = E^p` (a subfield containing $`l`, as $`l` is perfect) and let $`\partial_a` be the
coordinate derivations of the basis $`(da)_{a \in A}` ({name}`coordDerivation`), so
$`dy = 0` if and only if $`\partial_a y = 0` for all $`a`.
Every $`y \in E` is separable over $`l(A) \subset F(A)` and purely inseparable over $`F`, hence
$`y \in F(A)`, and in fact $`y \in F(A_0)` for a finite $`A_0 \subset A`.
Induction on $`A_0` reduces the claim to one step
({name}`mem_of_mem_adjoin_simple_of_derivation_eq_zero`): if a derivation
$`\partial` vanishes on a field $`M`, $`x^p \in M` and $`\partial x \neq 0`, then every
$`y \in M(x)` with $`\partial y = 0` lies in $`M`.
Indeed $`y = g(x)` with $`\deg g` less than the degree of the minimal polynomial of $`x` over
$`M`, and $`0 = \partial y = g'(x)\, \partial x` forces $`g' = 0`, so $`g` is a polynomial in
$`X^p` and $`y \in M(x^p) = M`.

{docstring MilnorAlgDep.isAlgebraic_of_forall_exists_pow_pow_eq}

So the blueprint's discrete valuation is replaced by the perfect core
$`P = \bigcap_j E^{p^j}` ({name}`perfectCore`) and the general form of the lax
property ({ref "ss:lax-general"}[Section 2.4.4]), applied over the perfect field $`P`.

{docstring MilnorAlgDep.exists_pow_pow_eq_kaehler_D_ne_zero}

The exponent $`j` is the largest one with $`y \in E^{p^j}`
({name}`pow_pow_eq_iff_le_of_kaehler_D_ne_zero`), and $`(j, z)` is unique
({name}`existsUnique_pow_pow_eq_kaehler_D_ne_zero`).
For $`p = 1` the statement of (S3) is that $`dy \neq 0` for $`y` transcendental over $`l`; in
Lean this is part of the characteristic $`0` criterion below.

## Differentials and algebraic independence
%%%
tag := "ss:lax-general"
%%%

The lax property (Lemma 4.5) holds in the following general form, for any family in any extension
$`E` of a perfect field $`l`: if $`y_1, \dots, y_m \in E` have linearly independent differentials
in $`\Omega_{E|l}`, then they are algebraically independent over $`l`.
It is used for (S3) above and, in characteristic $`0`, gives a criterion for algebraic
independence.

{docstring MilnorAlgDep.algebraicIndependent_of_linearIndependent_kaehler_D}

_Proof (the blueprint's proof of Lemma 4.5)._
Let $`f` be a non-zero relation of minimal total degree.
If all partial derivatives of $`f` vanish, then $`f` is constant or $`f = g^p` by (S1), and $`g`
would be a relation of smaller degree.
Otherwise a non-zero partial derivative has smaller degree
({name}`totalDegree_pderiv_lt`), hence does not vanish at $`y`, and
$`\sum_i f_{Y_i}(y)\, dy_i = 0` is a non-trivial linear relation.

The Lean docstring cites this as "Lemma 4.6 (Lax property)"; the lax property is Lemma 4.5 of
the blueprint.
In characteristic $`0` the converse holds, because an algebraically independent family extends to
a transcendence basis over which $`E` is separable algebraic, and (S2) applies:

{docstring MilnorAlgDep.algebraicIndependent_iff_linearIndependent_kaehler_D}

{docstring MilnorAlgDep.kaehler_D_eq_zero_iff_isAlgebraic}

These two statements are all that the characteristic $`0` proof of Theorem A needs to know about
differentials, as the blueprint's remark on formalization (Remark 8.3) predicts.

## The eigenvalue lemma
%%%
tag := "ss:eigenvalue"
%%%

:::lem "2.2" (title := "Eigenvalue lemma") (tag := "lem:R")
Let $`E \supset l` be fields, $`a \in E` transcendental over $`l`, and $`\delta` a derivation of
$`E` with $`\delta(l) = 0` and $`\delta(a) = a`.
Let $`b \in E^\times` be separable algebraic over $`l(a)` with $`\delta(b) = \kappa b` for some
$`\kappa \in l`.
Then $`\kappa` lies in the prime field $`\FF` of $`l`.
:::

{docstring MilnorAlgDep.eigenvalue_mem_primeField}

In Lean the prime field of $`l` is the bottom element of the lattice of subfields, so the
conclusion reads `κ ∈ (⊥ : Subfield l)`.
The derivation is an $`l`-linear derivation `δ : Derivation l E E`, which encodes
$`\delta(l) = 0`.
The variants {name}`exists_ratCast_eq_eigenvalue` (characteristic $`0`: $`\kappa`
is rational) and {name}`exists_intCast_eq_eigenvalue` (characteristic $`p`:
$`\kappa` is the image of an integer) are the forms used later.

_Proof (as formalized)._
The blueprint works with a primitive polynomial over $`l[a]` and Gauss' lemma; the formal proof
works with the minimal polynomial over $`l(a)` instead.

1. On $`l(a)` the derivation is $`a \cdot d/da`: for polynomials $`P, Q`,
   $`\delta(P(a)/Q(a)) = a(P'Q - PQ')(a)/Q(a)^2`.
   In particular $`\delta` maps $`l(a)` into itself.
2. Let $`f = \sum_{j=0}^n f_j Y^j` be the minimal polynomial of $`b` over $`l(a)`, so $`f_n = 1`.
   Applying $`\delta` to $`f(b) = 0` gives $`\sum_j (\delta f_j + j\kappa f_j) b^j = 0`.
   Subtracting $`n\kappa f(b) = 0` gives a polynomial of degree less than $`n` over $`l(a)`
   vanishing at $`b`, so all its coefficients vanish:
   $`\delta f_j = (n - j)\kappa f_j` for all $`j` ({name}`derivation_coeff_minpoly`).
3. If a non-zero $`g \in l(a)` satisfies $`\delta g = \varepsilon g` with $`\varepsilon \in l`,
   then $`\varepsilon` is the image of an integer.
   Write $`g = P(a)/Q(a)`; since $`a` is transcendental this is the polynomial identity
   $`X(P'Q - PQ') = \varepsilon PQ`, and comparing the coefficients of index
   $`\operatorname{ord}_X P + \operatorname{ord}_X Q` gives
   $`\varepsilon = \operatorname{ord}_X P - \operatorname{ord}_X Q`
   ({name}`exists_intCast_eq_of_euler`).
4. Since $`b \neq 0`, $`f_0 \neq 0`; and since $`f` is separable, $`f' \neq 0`, so there is $`j`
   with $`f_j \neq 0` and $`j \neq 0` in $`l` ({name}`exists_coeff_minpoly_ne_zero`).
   Applying 3 to $`f_0` and $`f_j` shows that $`n\kappa` and $`(n - j)\kappa` are images of
   integers, hence so is $`j\kappa`, and $`\kappa \in \FF` because $`j` is invertible in $`l`.
