module

public import MilnorAlgDep.CharP.AdaptedModel
public import MilnorAlgDep.Standard.Eigenvalue
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import Mathlib.FieldTheory.RatFunc.Degree
public import Mathlib.RingTheory.Norm.Basic

/-!
# Field-theoretic lemmas for Step C in characteristic `p`

Blueprint Section 6.6 with `Γ = ℤ`: the statements in the proofs of Lemmas 6.10, 6.11 and
Proposition 6.12 that concern only the extension `L / l` and a model, not the homomorphism `ψ`.

* `exists_intCast_of_modelDLog_eq`: the eigenvalue lemma (Lemma 2.2) in the form used in
  Lemmas 6.10, 6.11 and `eq:lift`.
* `mem_of_pow_pow_mem`: `eq:Epower`, `E ∩ L_A^{p^j} = E^{p^j}`.
* `exists_pow_eq_mul_pow_pow`: from `p^j • v = [b]` with `v ∈ W`, `b ∈ E` to
  `b^M = c y^{p^j}` with `y ∈ E`.
* `exists_dvd_sub_of_forall_pow_eq`: the norm argument (the degree of `N_{E|l(s)}(a)` in
  `l(s) ≅ l(X)`, through `normDegHom`).
* `exists_dvd_sub_of_dvd`: elementary arithmetic (`MN = p^β n'`, `ε = p^β m'`).

## Deviation from the blueprint

In the norm argument the blueprint compares orders at `s` (unique factorization in `l[s]`). We use
the degree `RatFunc.intDegree` on `l(s) ≅ RatFunc l` instead (the order at `∞`, up to sign): all
that is needed is a homomorphism `l(s)ˣ → ℤ` which vanishes on `lˣ` and is `1` at `s`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf IntermediateField KaehlerDifferential

variable {l L : Type*} [Field l] [Field L] [Algebra l L] {ι : Type*}

/-! ### The degree of a norm

Used in the norm argument (`exists_dvd_sub_of_forall_pow_eq`): for a finite extension `E / K` and
an isomorphism `σ : K ≃ k(X)`, the map `x ↦ deg σ(N_{E|K}(x))` is a homomorphism `Eˣ → ℤ` which
vanishes on `kˣ` and takes the value `[E : K]` on `σ⁻¹(X)`. (The blueprint uses the order at `s`
instead of the degree; any discrete valuation of `k(X)` trivial on `k` with `v(X) = ±1` works.) -/

section NormDeg

variable {k : Type*} [Field k]

/-- The degree `RatFunc.intDegree` on `k(X)ˣ`, as a homomorphism to `Multiplicative ℤ`. -/
noncomputable def intDegreeHom : (RatFunc k)ˣ →* Multiplicative ℤ where
  toFun x := .ofAdd (RatFunc.intDegree (x : RatFunc k))
  map_one' := by simp
  map_mul' x y := by
    rw [Units.val_mul, RatFunc.intDegree_mul x.ne_zero y.ne_zero, ofAdd_add]

theorem toAdd_intDegreeHom (x : (RatFunc k)ˣ) :
    (intDegreeHom x).toAdd = RatFunc.intDegree (x : RatFunc k) :=
  rfl

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [FiniteDimensional K E]

variable (E) in
/-- `x ↦ deg σ(N_{E|K}(x))` on `Eˣ`, for an isomorphism `σ : K ≃ k(X)`. -/
noncomputable def normDegHom (σ : K ≃+* RatFunc k) : Eˣ →* Multiplicative ℤ :=
  intDegreeHom.comp ((Units.map σ.toMonoidHom).comp (Units.map (Algebra.norm K : E →* K)))

theorem normDegHom_algebraMap (σ : K ≃+* RatFunc k) (u : Kˣ) :
    normDegHom E σ (Units.map (algebraMap K E : K →* E) u) =
      intDegreeHom (Units.map σ.toMonoidHom u) ^ Module.finrank K E := by
  have h : Units.map (Algebra.norm K : E →* K) (Units.map (algebraMap K E : K →* E) u) =
      u ^ Module.finrank K E := by
    ext
    simp [Algebra.norm_algebraMap]
  rw [normDegHom, MonoidHom.comp_apply, MonoidHom.comp_apply, h, map_pow, map_pow]

end NormDeg

/-! ### Field-theoretic lemmas -/

section Fields

variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]

omit [Fact p.Prime] [CharP L p] [PerfectField L] in
/-- An element `s` with `d s ≠ 0` in `Ω_B` is transcendental over `l`. -/
theorem transcendental_of_modelD_ne_zero {B : ι → L} {s : L} (hds : modelD l B s ≠ 0) :
    Transcendental l s := by
  refine IsRelAlgClosed.transcendental fun ⟨c, hc⟩ ↦ hds ?_
  rw [← hc, modelD_algebraMap]

/-- Blueprint `eq:Epower` for `j = 1`: in the situation of `mem_of_pow_pow_mem`, if `z ∈ L_B` and
`z ^ p ∈ E`, then `z ∈ E`. -/
theorem mem_of_pow_mem_of_modelD_ne_zero {B : ι → L} {s : L} (hs : s ∈ model l B)
    (hds : modelD l B s ≠ 0) {E : IntermediateField l L} (hsE : s ∈ E) (hE : E ≤ model l B)
    (hsep : ∀ y ∈ E, IsSeparable l⟮s⟯ y) {z : L} (hz : z ∈ model l B) (hzp : z ^ p ∈ E) :
    z ∈ E := by
  have : PerfectField l := IsRelAlgClosed.perfectField l L
  have : CharP E p := (Algebra.charP_iff E L p).mpr inferInstance
  set s' : E := ⟨s, hsE⟩
  have hs' : Transcendental l s' := fun h ↦ transcendental_of_modelD_ne_zero hds (h.algHom E.val)
  have hsep' : Algebra.IsSeparable (adjoin l (Set.range fun _ : Unit ↦ s')) E :=
    isSeparable_adjoin_restrictFamily E (a := fun _ : Unit ↦ s) (fun _ ↦ hsE)
      fun y hy ↦ by rw [Set.range_const]; exact hsep y hy
  -- `Ω_{E|l} → Ω_B` is injective
  let : Algebra E (model l B) := (inclusion hE).toRingHom.toAlgebra
  have : IsScalarTower l E (model l B) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hinj := kaehler_map_injective_of_ne_zero (E' := model l B) hs'
    (by rwa [Set.range_const] at hsep') (by rwa [modelD_of_mem hs] at hds)
  -- so `d (z ^ p) = 0` in `Ω_{E|l}`, and `z ^ p` is a `p`-th power in `E` by (S3)
  have hD : D l E ⟨z ^ p, hzp⟩ = 0 := by
    apply hinj
    have := modelD_pow_char p hz
    rw [modelD_of_mem (pow_mem hz p)] at this
    rw [map_D, map_zero]
    exact this
  obtain ⟨w, hw⟩ := (kaehler_D_eq_zero_iff_exists_pow_eq p
    (algebraicIndependent_unique_type_iff.2 hs') hsep').1 hD
  have hwz : (w : L) = z := frobenius_inj L p (by
    rw [frobenius_def, frobenius_def]
    simpa using congrArg Subtype.val hw)
  exact hwz ▸ w.2

include p in
omit [PerfectField L] in
/-- **Blueprint Lemma 2.2** (eigenvalue lemma) in a model, in the form used in Lemmas 6.10, 6.11
and in `eq:lift`: let `a ∈ L_B` with `d a ≠ 0` in `Ω_B`, and `b ≠ 0` separable algebraic
over `l(a)`. If `dlog b = κ • dlog a` in `Ω_B` with `κ ∈ l`, then `κ` lies in the prime field
`F_p`, i.e. is the image of an integer. (Let `E` be the field of elements separable over `l(a)`
and `δ = a · d/da` the derivation of `E` with `d f = δ(f) • dlog a` in `Ω_{E|l}`. Mapping
`d b = (δ(b)/a) • d a` to `Ω_B` and comparing with the hypothesis, which is possible as
`d a ≠ 0` in `Ω_B`, gives `δ(b) = κ b`; then apply Lemma 2.2 to `δ`.) -/
theorem exists_intCast_of_modelDLog_eq {B : ι → L} {a b : L} (ha : a ∈ model l B)
    (hda : modelD l B a ≠ 0) (hb : IsSeparable l⟮a⟯ b) (hb0 : b ≠ 0) {κ : l}
    (h : modelDLog l B b = algebraMap l (model l B) κ • modelDLog l B a) :
    ∃ m : ℤ, (m : l) = κ := by
  have : CharP l p := IsRelAlgClosed.charP l L p
  have hatr : Transcendental l a := transcendental_of_modelD_ne_zero hda
  -- `E` = the field of elements of `L` separable over `l(a)`
  set A : Unit → L := fun _ ↦ a
  set E := model l A
  have hA : AlgebraicIndependent l A := algebraicIndependent_unique_type_iff.2 hatr
  have hrange : Set.range A = {a} := Set.range_const
  set a' : E := ⟨a, self_mem_model A ()⟩
  have ha' : Transcendental l a' := fun h ↦ hatr (h.algHom E.val)
  have ha0 : a ≠ 0 := fun h0 ↦ hatr (h0 ▸ isAlgebraic_zero)
  have hbE : b ∈ E := mem_model_iff.2 (by rwa [hrange])
  set b' : E := ⟨b, hbE⟩
  have hb'0 : b' ≠ 0 := fun h0 ↦ hb0 (congrArg Subtype.val h0)
  have hsep : IsSeparable l⟮a'⟯ b' := by
    have hsepE : Algebra.IsSeparable (adjoin l (Set.range fun _ : Unit ↦ a')) E :=
      isSeparable_adjoin_restrictFamily_separableClosure A
    rw [Set.range_const] at hsepE
    exact Algebra.IsSeparable.isSeparable _ b'
  -- `E ≤ L_B`
  have hEB : E ≤ model l B := fun y hy ↦
    mem_model_of_isSeparable (K := l⟮a⟯) (adjoin_simple_le_iff.2 ha)
      (by rw [← hrange]; exact mem_model_iff.1 hy)
  let : Algebra E (model l B) := (inclusion hEB).toRingHom.toAlgebra
  have : IsScalarTower l E (model l B) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- the derivation `δ = a d/da` of `E`
  set β := modelBasis hA
  have hβ : β () = D l E a' := by rw [modelBasis_apply, modelD_of_mem]
  set δ : Derivation l E E := a' • (β.coord ()).compDer (D l E)
  have hδ : ∀ y, δ y = a' * β.coord () (D l E y) := fun _ ↦ rfl
  have hδa : δ a' = a' := by
    rw [hδ, ← hβ, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_eq_same,
      mul_one]
  -- `d b' = f • d a'` in `Ω_{E|l}`, hence `d b = f • d a` in `Ω_B`
  set f : E := β.coord () (D l E b')
  have hf : D l E b' = f • D l E a' := by
    have := β.sum_repr (D l E b')
    rw [Fintype.sum_unique, hβ] at this
    exact this.symm
  have hfB : modelD l B b = algebraMap E (model l B) f • modelD l B a := by
    have := congrArg (KaehlerDifferential.map l l E (model l B)) hf
    rw [map_D, LinearMap.map_smul, map_D] at this
    rw [modelD_of_mem ha, modelD_of_mem (hEB hbE)]
    exact this.trans (algebraMap_smul (model l B) f _).symm
  -- from the hypothesis, `d b = (κ b / a) • d a` in `Ω_B`
  set aB : model l B := ⟨a, ha⟩
  set bB : model l B := ⟨b, hEB hbE⟩
  have haB : aB ≠ 0 := fun h0 ↦ ha0 (congrArg Subtype.val h0)
  have hκB : modelD l B b = (bB * algebraMap l (model l B) κ * aB⁻¹) • modelD l B a := by
    rw [← smul_modelDLog (hEB hbE) hb0, h, modelDLog_of_mem ha, smul_smul, smul_smul]
  have hfκ : algebraMap E (model l B) f = bB * algebraMap l (model l B) κ * aB⁻¹ :=
    smul_left_injective (model l B) hda (hfB.symm.trans hκB)
  have hκ : δ b' = algebraMap l E κ * b' := by
    apply (algebraMap E (model l B)).injective
    rw [hδ, map_mul, map_mul, hfκ, ← IsScalarTower.algebraMap_apply]
    change aB * (bB * algebraMap l (model l B) κ * aB⁻¹) = algebraMap l (model l B) κ * bB
    field_simp
  exact exists_intCast_eq_eigenvalue p a' ha' δ hδa b' hb'0 hsep κ hκ

/-- Blueprint `eq:Epower`: let `s ∈ L_B` with `d s ≠ 0` in `Ω_B`, and let `E ∋ s` be an
intermediate field contained in `L_B` and separable algebraic over `l(s)`. If `z ∈ L_B` and
`z^{p^j} ∈ E`, then `z ∈ E`; i.e. `E ∩ L_B^{p^j} = E^{p^j}`. (Since `Ω_{E|l} → Ω_B` is injective,
`dy = 0` for `y ∈ E ∩ L_B^p`, so `y ∈ E^p` by (S3); induction on `j`.) -/
theorem mem_of_pow_pow_mem {B : ι → L} {s : L} (hs : s ∈ model l B) (hds : modelD l B s ≠ 0)
    {E : IntermediateField l L} (hsE : s ∈ E) (hE : E ≤ model l B)
    (hsep : ∀ y ∈ E, IsSeparable l⟮s⟯ y) {z : L} (hz : z ∈ model l B) {j : ℕ}
    (hzj : z ^ p ^ j ∈ E) : z ∈ E := by
  induction j with
  | zero => simpa using hzj
  | succ j ih =>
    refine ih (mem_of_pow_mem_of_modelD_ne_zero p hs hds hsE hE hsep (pow_mem hz _) ?_)
    rwa [← pow_mul, ← pow_succ]

/-- Blueprint, proof of Proposition 6.12 (lines 713-714): let `E` be as in `mem_of_pow_pow_mem`.
If `v ∈ W` and `p^j • v = [b]` with `b ∈ E`, then `b^M = c • y^{p^j}` for some `M` prime to `p`,
`c ∈ lˣ` and `y ∈ E`. (If `v ≠ 0`, take a representative `(M, g)` of `v` with `g ∈ L_B`; then
`b^M = c g^{p^j}` and `g ∈ E` by `eq:Epower`. If `v = 0`, `b ∈ l`.) -/
theorem exists_pow_eq_mul_pow_pow {B : ι → L} {s : L} (hs : s ∈ model l B)
    (hds : modelD l B s ≠ 0) {E : IntermediateField l L} (hsE : s ∈ E) (hE : E ≤ model l B)
    (hsep : ∀ y ∈ E, IsSeparable l⟮s⟯ y) {v : V l L} (hv : v ∈ W l p B) {j : ℕ} {b : Lˣ}
    (hb : (b : L) ∈ E) (h : p ^ j • v = cls (constUnits l L) (.ofMul b)) :
    ∃ (M : ℕ) (c : l) (y : L), M.Coprime p ∧ c ≠ 0 ∧ y ∈ E ∧
      (b : L) ^ M = algebraMap l L c * y ^ p ^ j := by
  obtain ⟨N, g, hg, hgB⟩ := hv
  -- `[b ^ N] = N p ^ j v = [g ^ p ^ j]`
  have h1 : cls (constUnits l L) (.ofMul (b ^ N / g ^ p ^ j)) = 0 := by
    rw [cls_div, cls_pow, cls_pow, ← h, ← hg.nsmul_eq, smul_smul, smul_smul, mul_comm, sub_self]
  obtain ⟨c, hc⟩ := (V.cls_eq_zero_iff' _).1 h1
  rw [Units.val_div_eq_div_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at hc
  have hg0 : (g : L) ^ p ^ j ≠ 0 := pow_ne_zero _ g.ne_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, eq_comm, div_eq_zero_iff] at hc
    exact hc.elim (pow_ne_zero _ b.ne_zero) hg0
  have hbg : (b : L) ^ N = algebraMap l L c * (g : L) ^ p ^ j := by
    rw [hc, div_mul_cancel₀ _ hg0]
  refine ⟨N, c, g, hg.coprime, hc0, mem_of_pow_pow_mem p hs hds hsE hE hsep hgB (j := j) ?_, hbg⟩
  have hc0' : algebraMap l L c ≠ 0 := by simpa using hc0
  rw [show (g : L) ^ p ^ j = (algebraMap l L c)⁻¹ * (b : L) ^ N by
    rw [hbg, inv_mul_cancel_left₀ hc0']]
  exact mul_mem (inv_mem (IntermediateField.algebraMap_mem E c)) (pow_mem hb N)

omit [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L] in
/-- Blueprint, proof of Proposition 6.12 (lines 714-716), the norm argument: let `s` be
transcendental over `l`, `a ≠ 0` algebraic over `l(s)`, `E = l(s, a)`, and `e j` integers such
that for every `j`, `(a s^{-e_j})^{M_j} ∈ lˣ · E^{p^j}` for some `M_j` prime to `p`. Then there
are `M ≥ 1` (namely `[E : l(s)]`) and `ε` with `ε ≡ M e_j (mod p^j)` for all `j`. (Take norms to
`l(s)` and compare orders at `s` in `l[s]`. We use the degree in `l(s) ≅ l(X)` instead of the order
at `s`, so `ε` is the degree of `N_{E|l(s)}(a)`.) -/
theorem exists_dvd_sub_of_forall_pow_eq {s a : L} (hs : Transcendental l s) (ha0 : a ≠ 0)
    (ha : IsAlgebraic l⟮s⟯ a) (e : ℕ → ℤ)
    (h : ∀ j : ℕ, ∃ (M : ℕ) (c : l) (y : L), M.Coprime p ∧ c ≠ 0 ∧ y ∈ l⟮s, a⟯ ∧
      (a * s ^ (-e j)) ^ M = algebraMap l L c * y ^ p ^ j) :
    ∃ (M : ℕ) (ε : ℤ), 0 < M ∧ ∀ j : ℕ, (p : ℤ) ^ j ∣ ε - M * e j := by
  set K := l⟮s⟯
  set E : IntermediateField K L := K⟮a⟯
  have : FiniteDimensional K E := adjoin.finiteDimensional ha.isIntegral
  set σ : K ≃+* RatFunc l := (RatFunc.algEquivOfTranscendental s hs).symm.toRingEquiv
  set χ := normDegHom E σ
  have hs0 : s ≠ 0 := fun h0 ↦ hs (h0 ▸ isAlgebraic_zero)
  set ua : Eˣ := Units.mk0 (AdjoinSimple.gen K a) fun h0 ↦ ha0 (congrArg Subtype.val h0)
  set us : Kˣ := Units.mk0 (AdjoinSimple.gen l s) fun h0 ↦ hs0 (congrArg Subtype.val h0)
  have hus : (intDegreeHom (Units.map σ.toMonoidHom us)).toAdd = 1 := by
    change RatFunc.intDegree ((RatFunc.algEquivOfTranscendental s hs).symm
      (AdjoinSimple.gen l s)) = 1
    rw [RatFunc.algEquivOfTranscendental_symm_gen, RatFunc.intDegree_X]
  refine ⟨Module.finrank K E, (χ ua).toAdd, Module.finrank_pos, fun j ↦ ?_⟩
  obtain ⟨M, c, y, hM, hc, hy, heq⟩ := h j
  have hyE : y ∈ E := by
    rw [← adjoin_simple_adjoin_simple] at hy
    exact hy
  -- replace `y` by a non-zero element of `E` with the same `p ^ j`-th power
  obtain ⟨y', hy'E, hy'0, hy'⟩ : ∃ y' ∈ E, y' ≠ 0 ∧ y' ^ p ^ j = y ^ p ^ j := by
    by_cases hy0 : y = 0
    · refine ⟨1, one_mem _, one_ne_zero, ?_⟩
      by_cases hn : p ^ j = 0
      · rw [hn, pow_zero, pow_zero]
      · rw [hy0, zero_pow hn, mul_zero] at heq
        exact absurd heq (pow_ne_zero _ (mul_ne_zero ha0 (zpow_ne_zero _ hs0)))
    · exact ⟨y, hyE, hy0, rfl⟩
  set uy : Eˣ := Units.mk0 ⟨y', hy'E⟩ fun h0 ↦ hy'0 (congrArg Subtype.val h0)
  set uc : Kˣ := Units.mk0 (algebraMap l K c) (by simpa using hc)
  have key : (ua * Units.map (algebraMap K E : K →* E) us ^ (-e j)) ^ M =
      Units.map (algebraMap K E : K →* E) uc * uy ^ p ^ j := by
    refine Units.ext ((algebraMap E L).injective ?_)
    simp only [Units.val_pow_eq_pow_val, Units.val_mul, Units.val_zpow_eq_zpow_val, map_pow,
      map_mul, map_zpow₀, Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0, ua, us, uy, uc,
      ← IsScalarTower.algebraMap_apply]
    rw [AdjoinSimple.algebraMap_gen, AdjoinSimple.algebraMap_gen]
    change (a * s ^ (-e j)) ^ M = algebraMap l L c * y' ^ p ^ j
    rw [hy', heq]
  have huc : (intDegreeHom (Units.map σ.toMonoidHom uc)).toAdd = 0 := by
    change RatFunc.intDegree ((RatFunc.algEquivOfTranscendental s hs).symm
      (algebraMap l K c)) = 0
    rw [AlgEquiv.commutes, RatFunc.algebraMap_eq_C, RatFunc.intDegree_C]
  have := congrArg (fun u ↦ (χ u).toAdd) key
  simp only [map_pow, map_mul, map_zpow, toAdd_pow, toAdd_mul, toAdd_zpow, χ,
    normDegHom_algebraMap, hus, huc, smul_eq_mul, nsmul_eq_mul, mul_one, mul_zero,
    zero_add] at this
  have hcop : IsCoprime (M : ℤ) ((p : ℤ) ^ j) :=
    (Nat.isCoprime_iff_coprime.2 hM).pow_right
  refine hcop.symm.dvd_of_dvd_mul_left ⟨(normDegHom E σ uy).toAdd, ?_⟩
  push_cast at this
  linear_combination this

omit [CharP L p] [PerfectField L] [IsRelAlgClosed l L] in
/-- Blueprint, proof of Proposition 6.12 (lines 717-718), arithmetic: if `ε ≡ M r_j (mod p^j)`
for all `j`, with `M ≥ 1`, write `M = p^β n'` with `p ∤ n'`; then `p^β ∣ ε`, say `ε = p^β m'`, and
`n' r_j ≡ m' (mod p^{j-β})` for all `j ≥ β`. -/
theorem exists_dvd_sub_of_dvd {M : ℕ} (hM : 0 < M) {ε : ℤ} {r : ℕ → ℤ}
    (h : ∀ j : ℕ, (p : ℤ) ^ j ∣ ε - M * r j) :
    ∃ (n' : ℕ) (m' : ℤ) (β : ℕ), 0 < n' ∧ ∀ j : ℕ, β ≤ j → (p : ℤ) ^ (j - β) ∣ n' * r j - m' := by
  have hp : p.Prime := Fact.out
  obtain ⟨β, n', -, hMn⟩ := Nat.exists_eq_pow_mul_and_not_dvd hM.ne' p hp.ne_one
  have hn' : 0 < n' := Nat.pos_of_ne_zero fun h0 ↦ hM.ne' (by rw [hMn, h0, mul_zero])
  have hMn' : (M : ℤ) = (p : ℤ) ^ β * n' := by rw [hMn]; push_cast; ring
  -- `p ^ β ∣ ε`
  obtain ⟨m', hm'⟩ : (p : ℤ) ^ β ∣ ε := by
    have h1 : (p : ℤ) ^ β ∣ M * r β := by rw [hMn', mul_assoc]; exact dvd_mul_right _ _
    simpa using dvd_add (h β) h1
  refine ⟨n', m', β, hn', fun j hj ↦ ?_⟩
  have hp0 : (p : ℤ) ^ β ≠ 0 := pow_ne_zero _ (Int.natCast_ne_zero.2 hp.ne_zero)
  rw [← mul_dvd_mul_iff_left hp0, ← pow_add, Nat.add_sub_cancel' hj, ← dvd_neg]
  convert h j using 1
  rw [hm', hMn']
  ring

end Fields

end MilnorAlgDep
