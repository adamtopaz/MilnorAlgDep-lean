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
It proves Theorems A–D with no `sorry` and no axioms beyond the standard ones
({ref "ss:status"}[Section 1.5]).
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
    VOf.lean              VOf H = ℚ ⊗ (Lˣ ⧸ H), classes [a]   2.3
    V.lean                V l L, IsRelAlgClosed, (V1), (V2)   2.3
    AlgIndep.lean         algebraic independence in V         2.3
    Points.lean           points Q_a, Q_v, G_Q, (V3)          2.1, 2.3
    PerfectClosure.lean   l^i, V_{L|l} = V_{L^i|l^i}          2.3.1
  Standard/
    Differentials/        (S1)-(S3), Lemma 4.5 (general)      2.4
    Eigenvalue.lean       Lemma 2.2                           2.4.5
    SepCrit.lean          separability criterion (Lemma 3.1)  3.2
  StepB/
    Basic.lean            μ, t, Lemmas 6.6, 6.7               6.4
    Abstract.lean         Lemma 6.8, (P3), Prop. 6.9          6.5
  Char0/
    DLog.lean             dlog, Lemma 6.4 (Γ = 0)             6.3.1
    PointDeriv.lean       differentials of a point            6.3.1
    Delta.lean            Δ, Lemma 6.5, τ                     6.3.1, 6.5
    StepC.lean            Lemmas 6.10-6.12 (Γ = 0)            6.6.1
    Main.lean             Theorem A, char L = 0               6.7
  CharP/                  Theorem A, char L > 0
    Frobenius.lean        Frob^j as frobZ, l is perfect       2.2, 3
    Model.lean            Def. 4.1, Lemma 4.2, criterion      3.2, 4.1
    Levels.lean           ≈, levDiff, Lemma 3.2               3.3
    Normalized.lean       Def. 3.4, Lemma 3.5, levelTriple    3.4
    Models.lean           hgt, ω, Lemmas 4.3, 4.5             4.2, 4.3
    Trichotomy.lean       Lemma 4.6                           4.4
    Quadrangle.lean       Lemma 5.1                           5
    LevelV.lean           levDiffV, hgtV, CharPHyp, (eq:sum)  6.1.1
    StepA.lean            Lemmas 6.2, 6.3, Prop. 6.1          6.2
    AdaptedModel.lean     W, dlog_A, K₀, Lemmas 6.4, 6.5, τ   6.3.2, 6.5
    StepCFields.lean      eigenvalue lemma, norm argument     6.6.2
    StepC.lean            (eq:roots), Lemmas 6.10-6.12        6.5.1, 6.6.2
    Main.lean             τ on K, Theorem A, char L > 0       6.7
  Reduction.lean          reduction to perfect K and L        6.1
  Reduction/
    ExtendPsi.lean        extension of ψ to K^i               6.1
  Uniqueness.lean         Lemma 6.13                          6.7
  TheoremA.lean           statements of Theorem A             1.1
  Milnor/
    Defs.lean             MilnorKQ, grading, φ₁, τ_*, r^deg   7
    Basic.lean            properties, direct sum              7
    PerfectClosure.lean   purely inseparable extensions       7
    ValuationExt.lean     existence of valuations             7.1
    Tame.lean             Lemma 7.1, relative tame symbol     7.1
    Symbols.lean          Lemma 7.2                           7.1
    DegOne.lean           degree one parts                    7.2
    TheoremB.lean         Theorem B                           7.2
    PrimeField.lean       prime fields, k₀ and l₀             7.3
    KPrime.lean           (eq:dep), Lemma 7.3                 7.3
    LiftC.lean            last step of Theorem C              7.3
    TheoremC.lean         Theorem C                           7.3
    TheoremD.lean         Theorem D                           7.4
```

The files under `CharP/` are listed in dependency order.
No file contains a `sorry`.
Every file is a Lean module and starts with a docstring saying which part of the blueprint it
formalizes; every declaration corresponding to a numbered statement has a docstring naming it.
The root module `MilnorAlgDep` imports all files.
Hovering over a name in this text shows its type and documentation; clicking it jumps to its
documentation.

The statements of Theorems A–D and the definitions they mention ({name}`V`, the class map
{name}`VOf.cls`, {name}`VAlgIndep`, and {name}`MilnorKQ` with its grading) were written and
reviewed at the start of the formalization, before any proof, and were changed afterwards only by
explicit decision; this text calls them the _frozen_ statements.
`TheoremA.lean` contains the frozen statements of Theorem A, each proved by forwarding to a theorem
with the same statement ({ref "ss:assembly"}[Section 6.7.1]).

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
* _Levels._ {ref "sec:levels"}[Chapters 3–5] work with elements instead of sets of levels:
  points are given by transcendental elements, levels by level differences
  {name}`levDiff` `l p s t` $`= \lev(s) - \lev(t)`, level triples by
  {name}`levelTriple` `l p x y z`, and the model level by heights {name}`hgt` `l p B y`.
  The dictionary is in {cref "ss:elementwise"}[].

# Blueprint items and Lean declarations
%%%
tag := "ss:table"
%%%

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
  * $`\Frob^j`; $`l` is perfect (Chapter 3)
  * {name}`frobZ`, {name}`IsRelAlgClosed.perfectField`, {name}`point_frobZ`
*
  * Lemma 3.1
  * not formalized; replaced by {name}`isSeparable_adjoin_of_linearIndependent_kaehler_D`,
    {name}`isSeparable_of_linearIndependent_modelD`
*
  * same point, $`s \approx t`
  * {name}`SamePoint`, {name}`SepEquiv`
*
  * Lemma 3.2
  * {name}`existsUnique_sepEquiv_frobZ`, {name}`SepEquiv.trans`
*
  * Definition 3.3 (levels)
  * {name}`levDiff`, {name}`levDiff_eq_iff`, {name}`levDiff_nonneg_iff`
*
  * Definition 3.4 (normalized triples)
  * {name}`IsCollinearTriple`, {name}`IsNormalized`
*
  * Lemma 3.5, level triples
  * {name}`exists_isNormalized`, {name}`IsNormalized.isNormalized_iff`,
    {name}`levelTriple`, {name}`isNormalized_levelTriple`,
    {name}`levelTriple_eq_of_isNormalized`
*
  * Definition 4.1 (models)
  * {name}`model`, {name}`modelD`
*
  * Lemma 4.2
  * {name}`modelBasis`, {name}`mem_model_of_isSeparable`,
    {name}`exists_pow_pow_mem_model`
*
  * Lemma 4.3
  * {name}`frobZ_neg_mem_model_iff`, {name}`hgt_eq_zero_iff`,
    {name}`span_modelD_eq_of_hgt_eq_zero`
*
  * Definition 4.4 (height, line)
  * {name}`hgt`, {name}`hgt_sub_hgt`, {name}`omega`,
    {name}`omega_eq_of_samePoint`
*
  * Lemma 4.5 for points, propagation
  * {name}`not_linearIndependent_modelD_of_not_algebraicIndependent`,
    {name}`omega_le_sup_of_isAlgebraic`, {name}`omega_eq_inf_of_isAlgebraic`
*
  * Lemma 4.6
  * {name}`IsNormalized.trichotomy_lt`, {name}`IsNormalized.trichotomy_eq_of_omega_ne`,
    {name}`IsNormalized.trichotomy_eq_of_omega_eq`, {name}`IsNormalized.hgt_le_of_hgt_le`,
    {name}`isNormalized_of_hgt_eq_zero`, {name}`IsNormalized.hgt_eq_of_omega_ne`
*
  * Lemma 5.1
  * {name}`quadrangle`, {name}`levelTriple_fst_add_levelTriple_fst`
*
  * Section 6.1
  * {name}`extendPsi`, {name}`theoremA_perfect_of_isPRadical`,
    {name}`theoremA_perfect_aux`, {name}`theoremA_aux`
*
  * Section 6.1, $`\Gamma = \ZZ`: hypotheses, levels and heights in $`V`
  * {name}`CharPHyp`, {name}`IsVRep`, {name}`levDiffV`, {name}`levDiffV_eq`,
    {name}`levDiffV_smul_left`, {name}`hgtV`
*
  * (eq:sum) and its consequences
  * {name}`CharPHyp.ψK_add`, {name}`CharPHyp.pointV_ψK_one_sub_neg_div`,
    {name}`CharPHyp.isCollinearTriple_add`, {name}`CharPHyp.isAlgebraic_ρ_add`
*
  * (eq:nohom)
  * {name}`nohom`
*
  * $`n`, $`c` (eq:defc), Lemma 6.2
  * {name}`CharPHyp.n`, {name}`CharPHyp.c`, {name}`CharPHyp.ν`, {name}`CharPHyp.c_eq_ν`,
    {name}`isNormalized_of_coords`
*
  * Lemma 6.3
  * {name}`CharPHyp.c_add_c`
*
  * (eq:nu), Proposition 6.1
  * {name}`CharPHyp.ν_neg_mul`, {name}`CharPHyp.exists_addMonoidHom_eq_ν`,
    {name}`CharPHyp.n_eq_zero`, {name}`CharPHyp.levDiffV_one_sub`, {name}`CharPHyp.hgtV_one_sub`
*
  * Lemma 6.4, $`\Gamma = 0`
  * {name}`dlog`, {name}`dlog_injective`,
    {name}`exists_mem_pointV_dlog_eq_smul`
*
  * Lemma 6.5, $`\Gamma = 0`
  * {name}`Char0Hyp.data_Δ_eq_zero_iff`, {name}`Char0Hyp.μ_mem_pointV`,
    {name}`Char0Hyp.exists_Δhom_notMem_span`
*
  * adapted model, $`W`, $`\dlog_A` (6.3)
  * {name}`CharPHyp.trBasis`, {name}`CharPHyp.F`, {name}`W`, {name}`mem_W_iff`,
    {name}`dlogA`
*
  * Lemma 6.4, $`\Gamma = \ZZ`
  * {name}`dlogA_eq`, {name}`dlogA_add`, {name}`dlogA_ne_zero_iff`,
    {name}`span_dlogA_eq_omega`, {name}`dlogA_eq_zero_iff`, {name}`exists_pow_nsmul_mem_W`,
    {name}`eq_zero_of_forall_mem_pow_nsmul_W`
*
  * $`K_0`, $`\Delta` (6.3), Lemma 6.5, $`\Gamma = \ZZ`
  * {name}`CharPHyp.K₀`, {name}`CharPHyp.Δhom`, {name}`CharPHyp.Δhom_eq_zero_iff_one_sub`,
    {name}`CharPHyp.Δhom_one_sub_mem_span`, {name}`CharPHyp.μ_mem_pointV`,
    {name}`CharPHyp.linearIndependent_Δhom_x`, {name}`CharPHyp.exists_Δhom_notMem_span`,
    {name}`CharPHyp.data`
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
    {name}`Char0Hyp.τ`, {name}`CharPHyp.τ`, {name}`CharPHyp.ringChar_eq`
*
  * (eq:roots)
  * {name}`CharPHyp.pow_mem_K₀`, {name}`CharPHyp.exists_pow_pow_mem_K₀`,
    {name}`CharPHyp.exists_primitive_root`, {name}`CharPHyp.hgtV_pow_pow_of_primitive`
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
  * eigenvalue lemma in a model (6.6.2)
  * {name}`exists_intCast_of_modelDLog_eq`
*
  * Lemma 6.10, $`\Gamma = \ZZ`
  * {name}`CharPHyp.τ_mem_pointV`, {name}`CharPHyp.τ_mem_range_of_mem`,
    {name}`CharPHyp.τ_notMem_range`
*
  * Lemma 6.11, $`\Gamma = \ZZ`
  * {name}`CharPHyp.hgt_τ_eq_of_transverse`, {name}`CharPHyp.exists_hgt_τ_coeff`,
    {name}`CharPHyp.hgt_τ_eq_zero`, {name}`CharPHyp.exists_dlogA_eq_smul`,
    {name}`CharPHyp.exists_θ`
*
  * (eq:lift), (eq:padic)
  * {name}`CharPHyp.exists_lift`, {name}`CharPHyp.exists_padic`
*
  * (eq:Epower), the norm argument
  * {name}`mem_of_pow_pow_mem`, {name}`exists_pow_eq_mul_pow_pow`,
    {name}`exists_dvd_sub_of_forall_pow_eq`, {name}`exists_dvd_sub_of_dvd`
*
  * Proposition 6.12, $`\Gamma = \ZZ`
  * {name}`CharPHyp.exists_rat_ψ₀_eq`, {name}`CharPHyp.zsmul_ψ₀_eq_of_dvd`
*
  * Section 6.7, $`\Gamma = 0`
  * {name}`theoremA_perfect_of_charZero`
*
  * Section 6.7, $`\Gamma = \ZZ`
  * {name}`CharPHyp.τK`, {name}`CharPHyp.exists_rat_ψ_eq`, {name}`CharPHyp.τK_mem_range_iff`,
    {name}`CharPHyp.isRelAlgClosed_k`, {name}`theoremA_core_charP`
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
None of them is a correction of a mathematical error: the formalization found no error and no gap
in the statements and proofs of the blueprint (see also {cref "ss:formalAdds"}[]).
The differences are simplifications, reorganizations, and choices of encoding.

_Organization._

* _The two characteristics are treated separately._
  The blueprint is uniform in the characteristic, at the price of a characteristic exponent
  $`p = 1` and $`\Gamma = 0` in characteristic $`0`; in Lean that would force case distinctions
  through the whole theory of levels.
  {ref "sec:levels"}[Chapters 3–5] and the characteristic $`p` parts of
  {ref "sec:main"}[Chapter 6] are formalized for $`p` prime only (`MilnorAlgDep/CharP/`), and the
  characteristic $`0` proof uses $`\dlog \colon V_{L|l} \to \Omega_{L|l}` directly
  ({ref "ss:model0"}[Section 6.3.1]).
  The two proofs share the standard facts, the reduction to a perfect field $`L`, the abstract
  Step B and the proof of uniqueness.
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

_Levels, models, quadrangle_ ({ref "sec:levels"}[Chapters 3–5]).

* _Element-wise formulation_ ({cref "ss:elementwise"}[]).
  There is no torsor of levels $`\Lambda(P)`: the formalization uses the relation $`\approx`
  ({name}`SepEquiv`), "same point" ({name}`SamePoint`) and the level difference
  {name}`levDiff` `l p s t` $`= \lev(s) - \lev(t) \in \ZZ` with its calculus.
  Normalized triples are a predicate on elements that includes "three distinct collinear points"
  ({name}`IsNormalized`, {name}`IsCollinearTriple`), and the level triple is recorded relative to
  three elements ({name}`levelTriple`).
  The model level $`\lambda_A(P)` is not defined: heights are defined directly as a supremum
  ({name}`hgt`), and the line of a point through its canonical model generator ({name}`omega`).
* _Lemma 3.1 is not formalized._
  It is replaced by a separability criterion: over a perfect field, if the differentials of a
  family are linearly independent, every element algebraic over the field it generates is
  separable over it ({name}`isSeparable_adjoin_of_linearIndependent_kaehler_D`; proof through the
  minimal polynomial, coordinate derivations and (S3)).
  No irreducible multivariate relation occurs in the formal proofs: Lemma 3.2 is proved in the
  model of the one-element family $`(t)`, Lemma 3.5 (a) in the models of $`(x, y)` and
  $`(x, z_0)`, Lemma 3.5 (b) with the span statements of (S2), and the trichotomy from "each of
  $`dx, dy, dz` lies in the span of the other two".
* _Models are defined for any family_ $`B` ({name}`model`), not only for transcendence bases, and
  the differential {name}`modelD` is a total function, $`0` outside the model.
* _Lemma 4.3_ is proved from two facts, that the height is constant on $`\approx`-classes and
  that $`\hgt(\Frob^j y) = \hgt(y) + j`, instead of the blueprint's case analysis.
* _Lemma 4.5_ holds for any algebraically dependent family of transcendental elements, so
  propagation needs no distinctness hypothesis.
* _Lemma 4.6 (c)_ holds under the weaker hypothesis $`i \leq j`
  ({name}`IsNormalized.hgt_le_of_hgt_le`).
* _Lemma 5.1_ is stated for seven elements and six normalized triples ({name}`quadrangle`) and
  proved in coordinates with respect to {name}`modelBasis`; the incidences
  $`G \notin \{A, C, D, E\}`, $`H \notin \{A, B, C, G\}` come out of the distinctness of the lines
  instead of being proved first, and only the inclusion half of propagation is used.
  The consequence used for Lemma 6.3 is {name}`levelTriple_fst_add_levelTriple_fst`.

_Theorem A_ ({ref "sec:main"}[Chapter 6]).

* _Levels of elements of_ $`V` ({ref "ss:notationP"}[Section 6.1.1]).
  As in Chapters 3–5, only level differences {name}`levDiffV` `p v w` $`= \lev(v) - \lev(w)` and
  heights {name}`hgtV` are defined, through fixed representatives prime to $`p`; one rule,
  $`\lev(qv) = \lev(v) + v_p(q)` for $`q \in \QQ^\times`, covers the blueprint's remarks on
  $`pv`, $`-v` and $`Nv`.
  $`\psi` is extended to $`K` by $`\psi(0) = 0` ({name}`CharPHyp.ψK`).
* _(eq:sum) is used in an unconditional form_: $`Q_{x+y}` lies on $`\la Q_x, Q_y \ra` whenever
  $`x, y, x + y \neq 0` ({name}`CharPHyp.isAlgebraic_ρ_add`).
  This gives the incidences of {cref "lem:cocycle"}[] directly, and the blueprint's proof of
  $`G \neq B` there is not needed.
* _Lemma 6.2._
  The function $`\nu` is defined by the case formula of the lemma, which becomes the identity
  $`c(u, w) = \nu(-u/w)` ({name}`CharPHyp.c_eq_ν`).
  In all three cases normality is checked by one criterion, pairwise linearly independent
  differentials in the model of two elements ({name}`isNormalized_of_coords`), instead of the
  irreducible relation of the triple and Lemma 3.1.
* _Proposition 6.1._
  The constant $`\delta_0 = \nu(-s) - \nu(s)` is shown to vanish at each pair of
  $`\psi`-independent elements directly, without proving first that it is a constant; the
  homomorphism $`\chi` computes $`\varrho` with the fixed element $`x_1`.
* _Lemmas 6.4 and 6.5._
  $`W` is defined as the set of elements with a representative in $`L_A` ({name}`W`), which is
  visibly a subgroup, and identified with $`\{0\} \cup \{\hgt \geq 0\}` afterwards
  ({name}`mem_W_iff`).
  In Lemma 6.5 (c) four monomials $`x_1, x_2, x_3, x_1 x_2 x_3` replace the $`p^2 + p + 1` lines
  of $`\mathbf P^2(\FF_p)` ({name}`exists_notMem_span_four`).
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
* _Representatives in characteristic_ $`p`.
  A common denominator for several representatives is used only in {cref "lem:gauge"}[]
  ({name}`exists_isVRep₃`).
  Elsewhere (the proofs of $`\mu(x) \in Q_x` and of Lemmas 6.10, 6.11) the chosen representatives
  $`(N, a)`, $`(M, b)` are used, and $`(NM, a^M)`, $`(NM, b^N)` where a common denominator matters.
* _Lemmas 6.10 and 6.11 in characteristic_ $`p`.
  $`\tau(c) \in Q_x` is shown for every $`x \in K_0 \sm k`, and $`\tau(k) \subset l` follows with
  $`x = x_1, x_2` instead of two transverse elements.
  In {cref "lem:theta"}[], $`e_0 = 0` is proved before $`\theta \in l`, so that $`\tau(x)` is
  already known to be a model generator when the coefficient is shown to lie in $`Q_x`
  ({name}`CharPHyp.exists_dlogA_eq_smul`, shared with (eq:lift)); $`\theta` is an integer prime to
  $`p`.
  The eigenvalue lemma in a model is applied without the injectivity of
  $`\Omega_{E|l} \to \Omega_A` ({name}`exists_intCast_of_modelDLog_eq`).
* _Proposition 6.12._
  The integers $`r_j` of (eq:padic) need not be compatible: the formal statement is "for every
  $`j` there is $`r_j`" ({name}`CharPHyp.exists_padic`).
  The norm argument uses the degree on $`l(s) \cong l(X)` instead of the order at $`s`
  ({name}`exists_dvd_sub_of_forall_pow_eq`), so unique factorization in $`l[s]` and the exponents
  $`\varepsilon_P` do not occur.
  The factorization $`MN = p^\beta n'` is unnecessary (the conclusion holds with $`\beta = 0`), but
  is kept ({name}`exists_dvd_sub_of_dvd`).
* _End of the proof._
  $`\tau` is extended from $`K_0` to $`K` by Mathlib's `PerfectRing.lift`, since $`K` is
  $`p`-radical over $`K_0` and $`L` is perfect ({name}`CharPHyp.τK`).
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
The library has no `sorry`, and the main theorems depend only on the axioms `propext`,
`Classical.choice` and `Quot.sound`.
