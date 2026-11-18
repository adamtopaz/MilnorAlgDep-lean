import VersoManual
import MilnorAlgDepSite.Support
import MilnorAlgDep

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open MilnorAlgDepSite
open MilnorAlgDep

set_option pp.rawOnError true

#doc (Manual) "The formalization" =>
%%%
tag := "sec:formalization"
%%%

The Lean development lives in the library `MilnorAlgDep` of the
[repository](https://github.com/adamtopaz/MilnorAlgDep-lean), on top of Mathlib.
Its goal is Theorems A–D with no `sorry` and no axioms beyond the standard ones; the current
state is described in {ref "ss:status"}[Section 1.5].
This chapter describes how the library is organized, how to read its statements, which Lean
declaration formalizes which statement of the blueprint, and where the formal proofs deviate
from the blueprint.

# Organization
%%%
tag := "ss:organization"
%%%

The modules follow the structure of the proof.
The right-hand column gives the sections of this text where they are discussed.

```
MilnorAlgDep/
  Foundations/
    VOf.lean              VOf H = ℚ ⊗ (Lˣ ⧸ H), classes [a]              2.3
    V.lean                V l L, IsRelAlgClosed, (V1), (V2)              2.3
    AlgIndep.lean         VAlgIndep: algebraic independence in V         2.3
    Points.lean           points Q_a and Q_v, subgroups G_Q, (V3)        2.1, 2.3
    PerfectClosure.lean   l^i and V_{L|l} = V_{L^i|l^i}                  2.3.1
  Standard/
    Differentials/        (S1)-(S3), Lemma 4.5 in general form           2.4
    Eigenvalue.lean       Lemma 2.2                                      2.4.5
  StepB/
    Basic.lean            abstract Step B: μ, t, Lemmas 6.6, 6.7         6.4
    Abstract.lean         Lemma 6.8, (P3), Proposition 6.9               6.5
  Char0/
    DLog.lean             dlog : V → Ω_{L|l} (Lemma 6.4, Γ = 0)          6.3.1
    PointDeriv.lean       differentials of a point; eigenvalue lemma     6.3.1, 6.6.1
    Delta.lean            Δ = dlog ∘ ψ, Lemma 6.5, τ                     6.3.1, 6.5
    StepC.lean            Lemmas 6.10, 6.11, Proposition 6.12 (Γ = 0)    6.6.1
    Main.lean             Theorem A when char L = 0                      6.7
  CharP/
    Main.lean             Theorem A when char L > 0 (sorry)              Chapters 3-6
  Reduction.lean          reduction to perfect K and L                   6.1
  Reduction/ExtendPsi.lean  extension of ψ to K^i                        6.1
  Uniqueness.lean         Lemma 6.13                                     6.7
  TheoremA.lean           the statements of Theorem A                    1.1, 6.7.1
  Milnor/
    Defs.lean             MilnorKQ: definition, grading, φ₁, τ_*, r^deg   7
    Basic.lean            properties; direct sum decomposition           7
    PerfectClosure.lean   𝒦_* under purely inseparable extensions        7
    ValuationExt.lean     existence of valuations                        7.1
    Tame.lean             Lemma 7.1, relative tame symbol                7.1
    Symbols.lean          Lemma 7.2                                      7.1
    DegOne.lean           degree one parts of graded homomorphisms       7.2
    TheoremB.lean         Theorem B                                      7.2
    PrimeField.lean       prime fields and their algebraic closures      7.3, 7.4
    KPrime.lean           (eq:dep), Lemma 7.3                            7.3
    LiftC.lean            the last step of the proof of Theorem C        7.3
    TheoremC.lean         Theorem C                                      7.3
    TheoremD.lean         Theorem D                                      7.4
```

The positive characteristic part (levels, models, the quadrangle lemma, Steps A and C) will add
further files under `CharP/`.
Every file is a Lean module and starts with a docstring saying which part of the blueprint it
formalizes; every declaration corresponding to a numbered statement has a docstring naming it.
The root module `MilnorAlgDep` imports all files.
Hovering over a name in this text shows its type and documentation; clicking it jumps to its
documentation.

# Reading the formal statements
%%%
tag := "ss:reading"
%%%

The main theorems are stated in {ref "sec:intro"}[Chapter 1].
The following encoding choices are made throughout.

* _Fields._ Internal results are stated for two fields with `[Algebra l L]`, so that Mathlib's
  notions (`AlgebraicIndependent l`, `IsSeparable`, `IntermediateField l L`, `Ω[L⁄l]`) apply
  directly; the main theorems take subfields `k : Subfield K` and `l : Subfield L`.
  "Relatively algebraically closed" is the class {name}`IsRelAlgClosed` internally,
  and is spelled out as `∀ x : L, IsAlgebraic l x → x ∈ l` in the main theorems.
* _The group_ $`V_{L|l}`. For a subgroup `H` of `Lˣ`, `VOf H = ℚ ⊗[ℤ] Additive (Lˣ ⧸ H)` is a
  $`\QQ`-vector space ({name}`VOf`); $`V_{L|l}` is
  {name}`V` `l L = VOf (constUnits l L)` and $`L^\times_\QQ` is `VOf ⊥`.
  The class of a unit `a` is `〚a〛`, notation for {name}`VOf.cls` `_ (.ofMul a)`,
  with the subgroup read off from the expected type.
* _The homomorphism_ $`\psi`. Multiplicative groups are turned into additive ones with
  Mathlib's `Additive`: $`\psi` is an additive homomorphism `ψ : Additive Kˣ →+ V l L`, and
  $`\psi(x)` is `ψ (.ofMul x)` for a unit `x`.
  Field embeddings act on units by `Units.map`, so $`[\tau(x)]` is `〚Units.map (τ : K →* L) x〛`.
* _Pairs of units._ Statements about $`x` and $`1 - x` (hypothesis (A2), the Steinberg relations,
  Lemma 7.3) quantify over pairs of units `x y : Kˣ` with `x + y = 1`.
  This avoids the junk values of $`1 - x` at $`x = 1`, and makes $`x \neq 0, 1` automatic.
* _Algebraic independence in_ $`V`. {name}`VAlgIndep` `l v` means that some (equivalently
  every) choice of representatives $`N_i v_i = [a_i]` gives an algebraically independent family
  $`(a_i)` in $`L`.
  An algebraically independent family consists of non-zero elements, so the negation,
  "dependent", also covers the case that one of the elements is $`0`; this is how the blueprint's
  "dependent, or one of them is $`0`" appears.
* _Characteristic._ `ringChar L` is $`0` in characteristic $`0` and $`p` in characteristic $`p`;
  it is used in (A3) (where $`d` is `if ringChar L = 0 then 2 else 3`) and in (A4)
  (`ringChar L ≠ 0 → ringChar K ≠ 0`).
  `ringExpChar L`, the characteristic exponent, is $`1` in characteristic $`0`; it is the $`p` of
  the uniqueness statements, and the Frobenius is `frobeniusEquiv L (ringExpChar L)`, raised to
  integer powers.
* _Perfect closures._ The perfect closure $`L^i` is not constructed: the statements take any
  field `M` with `[Algebra L M]`, `[PerfectRing M p]` and `[IsPerfectClosure (algebraMap L M) p]`,
  with $`p` pinned down by `[ExpChar L p]`.
  The subfield $`l^i` is {name}`perfectClosureIn` `l M p`, and $`V_{L|l}` is compared
  with $`V_{L^i|l^i}` by {name}`V.toPerfectClosure`.
  In Theorem D, $`K^i` and $`L^i` come with their own exponents `pK` and `pL`.
* _The Milnor ring._ $`\Kr_*(L|l)` and $`\Kr_*(L)` are {name}`MilnorKQ` applied to
  `constUnits l L` and to `⊥`, both defined directly as the tensor algebra of `VOf H` modulo the
  Steinberg relations ({ref "ss:milnorRing"}[Chapter 7]).
  A homomorphism of graded algebras is an algebra homomorphism `φ` with
  {name}`MilnorKQ.IsGraded` `φ`, and $`\varphi_1` is
  {name}`MilnorKQ.degOne` `φ`.
  The map $`\tau_*` is {name}`MilnorKQ.map` `τ h`, where `h` proves that $`\tau` maps
  the subgroup into the subgroup, and $`r^{\deg}` is {name}`MilnorKQ.degScale`.
* _Prime fields._ The prime field of $`K` is `⊥ : Subfield K`.
  In Theorem C the subfields $`k_0, l_0` are arguments characterized by hypotheses
  (`∀ x, x ∈ k₀ ↔ IsAlgebraic (⊥ : Subfield K) x`); internally $`l_0` is
  {name}`primeAlgClosure`.
* _Valuations_ are Mathlib's valuation subrings `A : ValuationSubring L`.
  "$`v` is trivial on $`M`" is `∀ x : M, algebraMap M L x ∈ A`, and $`v(b) > 0` is
  `A.valuation b < 1`, since Mathlib's valuations are multiplicative.
  The value group is $`L^\times / O^\times`, with $`O^\times` = `A.unitGroup`.
* _Differentials._ $`\Omega_{E|l}` is `Ω[E⁄l]` and $`d` is `KaehlerDifferential.D l E`.
  "$`E` is separable algebraic over $`l(A)`" is
  `Algebra.IsSeparable (IntermediateField.adjoin l (Set.range a)) E` for a family `a : ι → E`.

# Blueprint items and Lean declarations
%%%
tag := "ss:table"
%%%

Placeholders refer to the positive characteristic part, which is in progress.

:::table +header
*
  * Blueprint
  * Lean
*
  * Theorem A
  * {name}`theoremA_perfect`, {name}`theoremA`,
    {name}`theoremA_perfect_unique`
*
  * Theorems B, C, D
  * {name}`theoremB`, {name}`theoremB_unique`,
    {name}`theoremC`, {name}`theoremC_unique`,
    {name}`theoremD`
*
  * $`V_{L|l}`, $`[a]` (1.1, 2.3)
  * {name}`V`, {name}`VOf`, {name}`VOf.cls`
*
  * algebraic independence in $`V_{L|l}`
  * {name}`VAlgIndep`, {name}`VAlgIndep.iff_of_nsmul_eq_cls`
*
  * points (2.1)
  * {name}`point`, {name}`point_eq_point_iff_not_algebraicIndependent`,
    {name}`point_inf_point_eq_bot`
*
  * (V1), (V2)
  * {name}`V.cls_eq_zero_iff`, {name}`V.exists_rep_coprime`,
    {name}`V.rep_unique`
*
  * (V3)
  * {name}`pointV`, {name}`pointGroup`,
    {name}`mem_pointGroup_point_iff`, {name}`vAlgIndep_pair_iff`
*
  * $`V_{L|l} = V_{L^i|l^i}`
  * {name}`perfectClosureIn`, {name}`V.toPerfectClosure_bijective`
*
  * Lemma 2.1 (S1)
  * {name}`exists_eq_pow_of_pderiv_eq_zero`, {name}`eq_C_of_pderiv_eq_zero`
*
  * Lemma 2.1 (S2)
  * {name}`kaehlerBasis`, {name}`kaehler_D_mem_span_range_of_isSeparable`,
    {name}`kaehler_D_pow_char`
*
  * Lemma 2.1 (S3)
  * {name}`kaehler_D_eq_zero_iff_exists_pow_eq`,
    {name}`exists_pow_pow_eq_kaehler_D_ne_zero`,
    {name}`kaehler_D_eq_zero_iff_isAlgebraic`
*
  * Lemma 2.2
  * {name}`eigenvalue_mem_primeField`
*
  * Lemma 4.5, general form
  * {name}`algebraicIndependent_of_linearIndependent_kaehler_D`,
    {name}`algebraicIndependent_iff_linearIndependent_kaehler_D`
*
  * other statements of Chapters 3–5
  * placeholder
*
  * Section 6.1
  * {name}`extendPsi`, {name}`theoremA_perfect_of_isPRadical`,
    {name}`theoremA_perfect_aux`, {name}`theoremA_aux`
*
  * Proposition 6.1, Lemmas 6.2, 6.3
  * placeholder
*
  * Lemma 6.4, $`\Gamma = 0`
  * {name}`dlog`, {name}`dlog_injective`,
    {name}`exists_mem_pointV_dlog_eq_smul`
*
  * Lemma 6.5, $`\Gamma = 0`
  * {name}`Char0Hyp.data_Δ_eq_zero_iff`, {name}`Char0Hyp.μ_mem_pointV`,
    {name}`Char0Hyp.exists_Δhom_notMem_span`
*
  * Lemmas 6.4, 6.5, $`\Gamma = \ZZ`
  * placeholder
*
  * hypotheses of Step B
  * {name}`StepBData`
*
  * Lemma 6.6
  * {name}`StepBData.μ_one_sub`, {name}`StepBData.μ_inv`,
    {name}`StepBData.μ_ne_one`, {name}`StepBData.t_one_sub`,
    {name}`StepBData.t_inv`
*
  * Lemma 6.7
  * {name}`StepBData.Transverse.t_mul`
*
  * Lemma 6.8
  * {name}`StepBData.t_mul_of_Δ_eq_zero`, {name}`StepBData.τ₀_neg_one`,
    {name}`StepBData.Transverse.t_add`
*
  * (P3)
  * {name}`StepBData.t_mul_of_notMem_span`
*
  * Proposition 6.9
  * {name}`StepBData.τ`, {name}`StepBData.exists_ringHom`,
    {name}`Char0Hyp.τ`
*
  * Lemma 6.10, $`\Gamma = 0`
  * {name}`Char0Hyp.τ_mem_pointV`, {name}`Char0Hyp.τ_mem_range_of_mem`,
    {name}`Char0Hyp.τ_notMem_range`
*
  * Lemma 6.11, $`\Gamma = 0`
  * {name}`Char0Hyp.exists_rat_Δ_eq_smul_dlogL_τ`
*
  * Proposition 6.12, $`\Gamma = 0`
  * {name}`Char0Hyp.exists_rat_ψ_eq`
*
  * Lemmas 6.10–6.12, $`\Gamma = \ZZ`
  * placeholder
*
  * Section 6.7, $`\Gamma = 0`
  * {name}`theoremA_perfect_of_charZero`
*
  * Lemma 6.13
  * {name}`theoremA_perfect_unique_aux`,
    {name}`eq_of_zpow_eq_of_transcendental`
*
  * $`\Kr_*(L)`, $`\Kr_*(L|l)`
  * {name}`MilnorKQ`, {name}`MilnorKQ.grade`,
    {name}`MilnorKQ.gradedAlgebra`
*
  * $`\varphi_1`, $`\tau_*`, $`r^{\deg}`
  * {name}`MilnorKQ.degOne`, {name}`MilnorKQ.map`,
    {name}`MilnorKQ.degScale`
*
  * bilinear maps out of $`\Kr_2`
  * {name}`MilnorKQ.ofBilin`
*
  * $`\Kr_*` and purely inseparable extensions
  * {name}`MilnorKQ.perfectClosureEquiv`
*
  * Lemma 7.1
  * {name}`tameSymbol`, {name}`tameSymbol_symbol_of_mem`
*
  * existence of valuations (7.1)
  * {name}`exists_valuationSubring_of_transcendental`
*
  * Lemma 7.2
  * {name}`symbol_ne_zero_of_algebraicIndependent`,
    {name}`symbol_ne_zero_of_isAlgebraic_of_transcendental`
*
  * remark after Lemma 7.2
  * {name}`not_vAlgIndep_of_ι_mul_ι_eq_zero`
*
  * (eq:dep)
  * {name}`TheoremC.not_vAlgIndep_psi`
*
  * Lemma 7.3
  * {name}`subfieldOfKer`, {name}`TheoremC.psi_eq_zero_of_add_eq_one`
*
  * last step of the proof of Theorem C
  * {name}`TheoremC.degOne_cls_eq_of_proj`
*
  * proof of Theorem D
  * {name}`TheoremD.exists_eq_of_degOne_bijective`,
    {name}`TheoremD.bijective_of_smul_cls_map_eq`
:::

# Deviations from the blueprint
%%%
tag := "ss:deviations"
%%%

The formal proofs follow the blueprint, with the following differences.
None of them is a correction of a mathematical error; the formalization so far has found no gap
in the characteristic $`0` part of the blueprint or in its Section 7.

_Organization._

* _The two characteristics are treated separately._
  The blueprint is uniform in the characteristic, at the price of a characteristic exponent
  $`p = 1` and $`\Gamma = 0` in characteristic $`0`; in Lean that would force case distinctions
  through the whole theory of levels.
  {ref "sec:levels"}[Chapters 3–5] and Step A are formalized for $`p` prime only, and the
  characteristic $`0` proof uses $`\dlog \colon V_{L|l} \to \Omega_{L|l}` directly
  ({ref "ss:model0"}[Section 6.3.1]).
* _Step B is abstract_ ({ref "ss:stepB"}[Section 6.4]).
  Lemmas 6.6–6.8 and Proposition 6.9 are proved for any homomorphism $`\Delta` satisfying
  (H0)–(H3), and used in both characteristics.
  No hypothesis beyond (H0)–(H3) is needed; (H0), $`\Delta(-1) = 0`, is listed separately
  because it does not follow from the homomorphism property when $`2 = 0` in $`F` (a priori
  $`K_0` and $`F` may have different characteristics).
  The assertions $`\mu(x) \in Q_x` and $`t(x) \in Q_x` belong to the concrete setting and are
  proved there.
* _Reductions_ ({ref "ss:reductions"}[Section 6.1]).
  The formal statement of Theorem A allows an arbitrary field $`K`.
  The reduction to perfect $`K` is only made in positive characteristic, and is proved for any
  perfect $`q`-radical extension of $`K`; the characteristic $`0` proof works for arbitrary $`K`.

_Standard facts_ ({ref "sec:conv"}[Chapter 2]).

* _(S3) is proved via the perfect core, not a discrete valuation._
  The perfect core $`P = \bigcap_j E^{p^j}` is a perfect field on which $`d` vanishes, so the
  differentials of a transcendence basis stay independent over $`P`; the lax property over $`P`
  then shows that $`P` is algebraic over $`l`.
  This also avoids the blueprint's linear disjointness step.
  The kernel of $`d` (the blueprint's "standard" first step) is proved by a $`p`-basis argument.
* _The lax property (Lemma 4.5) is proved in a general form_, for any family in any extension of
  a perfect field, without models; in characteristic $`0` its converse holds, which gives the
  criterion "algebraically independent if and only if the differentials are linearly
  independent".
* _The eigenvalue lemma avoids Gauss's lemma_ ({ref "ss:eigenvalue"}[Section 2.4.5]).
  It works with the minimal polynomial over $`l(a)`, and identifies the eigenvalues of the Euler
  operator on $`l(a)` as differences of orders of vanishing at $`0`.

_Theorem A_ ({ref "sec:main"}[Chapter 6]).

* _Lemma 6.8 and Proposition 6.9._
  $`\tau` is defined on $`\mathcal N` with one fixed primitive element $`z_0`, and its
  multiplicativity on $`\mathcal N` is never needed separately; $`\tau(-1) = -1` is obtained from
  two transverse pairs $`(x, y)`, $`(x, xy)`; step (1) of Proposition 6.9 distinguishes
  $`\Delta(y) \notin \ell(x)` from $`\Delta(y) \in \ell(x)` instead of "transverse or not", which
  avoids a symmetry argument.
* _Characteristic $`0` details._
  $`\mu(x) \in Q_x` is proved by pushing forward the basis $`da` of $`\Omega_{Q_a|l}`, without
  injectivity of $`\Omega_{Q_a|l} \to \Omega_{L|l}`; the richness hypothesis (H3) comes from the
  elements $`x_1 x_2^n`; in Lemmas 6.10 and 6.11 representatives may have different
  denominators.
* _Uniqueness (Lemma 6.13) assumes only $`\psi \neq 0`_, which implies the blueprint's
  hypotheses.
  Instead of dividing logarithmic differentials, the proof applies a derivation $`\delta` with
  $`\delta T = 1`; this does not need $`dS' \neq 0`, and handles negative exponents and $`p = 1`
  uniformly.

_Milnor $`K`-theory_ ({ref "sec:K"}[Chapter 7]).

* _The Milnor ring is defined directly and relatively_, as the tensor algebra over $`\QQ` of
  `VOf H` modulo the Steinberg relations; $`\Kr_*(L|l)` is not defined as a quotient of
  $`\Kr_*(L)`.
  The two definitions agree, but the comparison is not formalized.
* _The tame symbol is defined on all of_ $`\Kr_*(L)` (it vanishes in degrees $`0` and $`1`), and
  part (a) of Lemma 7.2 uses a relative tame symbol on $`\Kr_*(L|l)`, since that ring is not a
  quotient of $`\Kr_*(L)` by definition.
* _Lemma 7.2(a) does not need $`l` relatively algebraically closed_, and uses $`M = l(a)`
  instead of its relative algebraic closure: the residue map is injective on every field on which
  the valuation is trivial.
* _Theorem C._ $`\tau^{-1}(l_0) = k_0` follows directly from the isomorphism of prime fields
  induced by $`\tau`, so $`k' = k_0` is never needed.
  In the last step, the characteristic $`p` case uses $`C_L = 0` (non-zero elements of $`l_0` are
  roots of unity), and the tame symbol argument is only used in characteristic $`0`.
  Case (ii) of Lemma 7.3 uses the finiteness of $`\FF_p(1 - \zeta)`.
* _Theorem D._ Only $`\tau\tau'` has to be a power of Frobenius: this makes $`\tau` surjective.
* The existence of valuations is proved with a valuation subring dominating $`M[b]` instead of an
  extension of the $`b`-adic valuation of $`M(b)`; this is the same argument.

_Statements._

* The uniqueness clauses are separate theorems with fewer hypotheses than in the blueprint (see
  {ref "ss:statementA"}[Section 1.1]).
* Some hypotheses of the frozen statements are not used by the proofs: `[ExpChar L p]` in
  {name}`theoremA` (it documents $`p`), $`r' \neq 0` in
  {name}`theoremB_unique` and {name}`theoremC_unique`,
  `[IsRelAlgClosed l L]` in {name}`symbol_ne_zero_of_algebraicIndependent`, and
  `hφsymm` in {name}`theoremD` is implied by the others (not formalized).

# Status
%%%
tag := "ss:formalStatus"
%%%

See {ref "ss:status"}[Section 1.5].
The only `sorry` in the library is the proof of {name}`theoremA_core_charP` in
`MilnorAlgDep/CharP/Main.lean`.
