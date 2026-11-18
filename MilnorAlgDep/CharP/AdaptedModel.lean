module

public import MilnorAlgDep.CharP.StepA
public import MilnorAlgDep.StepB.Abstract

/-!
# The adapted model, `dlog_A`, `K₀` and `Δ`

Blueprint Section 6.3 (`ss:model`) with `Γ = ℤ`, and the application of the abstract Step B
(Sections 6.4, 6.5) to it.

## The logarithmic derivative on `W` (Lemma 6.4)

Let `B` be a transcendence basis of `L / l`, `F = L_B = model l B` and `Ω = Ω_B = Ω[F⁄l]`.

* `modelDLog l B y = y⁻¹ • d y ∈ Ω_B` for `y ∈ L_B` (`0` otherwise).
* `W l p B ≤ V_{L|l}`: the elements having a representative `(N, a)` (with `N` prime to `p`) with
  `a ∈ L_B`. By Lemma 4.3 this is the blueprint's `W = {0} ∪ {v ≠ 0 : ht(v) ≥ 0}`
  (`mem_W_iff`). With this definition `W` is visibly a subgroup.
* `dlogA p B v = N⁻¹ • dlog a` for every representative `(N, a)` of `v ∈ W`, `a ∈ L_B`
  (`dlogA_eq`); it is `0` off `W`. `dlogAHom l p B : W l p B →+ Ω_B` is the bundled version.
* Lemma 6.4: (a) `dlogA_eq`, `dlogA_add`; (b) `dlogA_ne_zero_iff`, `span_dlogA_eq_omega`;
  (c) `dlogA_eq_zero_iff` (`ker dlog_A = p W`), `exists_pow_nsmul_mem_W`
  (`V = ⋃ p^{-j} W`), `eq_zero_of_forall_mem_pow_nsmul_W` (`⋂ p^j W = 0`).

## The field `K₀` and `Δ` (Lemma 6.5)

For `H : CharPHyp K l L`:

* `CharPHyp.trBasis p`, `CharPHyp.B p`: a transcendence basis of `L / l` containing the chosen
  representatives `ρ p (x i)` of `ψ(x i)`; `CharPHyp.F p = L_B`.
* `CharPHyp.K₀ p : Subfield K`: `K₀ = {0} ∪ ψ⁻¹(W)` (Lemma 6.5(a); closure under addition uses
  Proposition 6.1, `CharPHyp.K₀_add_mem`).
* `CharPHyp.Δhom p : K₀ˣ → Ω_B`, `Δ = dlog_A ∘ ψ`, and the hypotheses (H0)-(H3) of the abstract
  Step B: `Δhom_neg_one`, `Δhom_eq_zero_iff_one_sub` and `Δhom_one_sub_mem_span` (Lemma 6.5(b)),
  `linearIndependent_Δhom_x` and `exists_Δhom_notMem_span` (Lemma 6.5(c)).
* `CharPHyp.data p : StepBData K₀ F Ω_B`; `CharPHyp.μ_mem_pointV` (Lemma 6.5(b), `μ(x) ∈ Q_x`).
* `CharPHyp.τ p : K₀ →+* L`, the field embedding of Proposition 6.9, and
  `CharPHyp.ringChar_eq`: `char K = char L`.

## Deviation from the blueprint

Lemma 6.5(c) is proved with the four monomials `x₀, x₁, x₂, x₀ x₁ x₂` instead of all
`p² + p + 1` lines `(i₀ : i₁ : i₂) ∈ P²(F_p)`: their `Δ`'s are pairwise non-proportional, and a
line contains at most one of them, so one of them avoids any three given lines.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf IntermediateField KaehlerDifferential

variable {l L : Type*} [Field l] [Field L] [Algebra l L] {ι : Type*}

/-! ### The logarithmic derivative in a model -/

section ModelDLog

variable (l) in
open Classical in
/-- The logarithmic derivative `dlog y = y⁻¹ • d y ∈ Ω_B = Ω[L_B⁄l]` of `y ∈ L_B`; by convention
`0` if `y ∉ L_B`. -/
noncomputable def modelDLog (B : ι → L) (y : L) : Ω[model l B⁄l] :=
  if h : y ∈ model l B then (⟨y, h⟩ : model l B)⁻¹ • D l (model l B) ⟨y, h⟩ else 0

variable {B : ι → L} {x y : L}

theorem modelDLog_of_mem (h : y ∈ model l B) :
    modelDLog l B y = (⟨y, h⟩ : model l B)⁻¹ • modelD l B y := by
  rw [modelDLog, dite_eq_left h, modelD_of_mem h]

theorem modelDLog_of_notMem (h : y ∉ model l B) : modelDLog l B y = 0 := by
  rw [modelDLog, dite_eq_right h]

/-- `y • dlog y = d y` for `y ∈ L_B`, `y ≠ 0`. -/
theorem smul_modelDLog (h : y ∈ model l B) (hy : y ≠ 0) :
    (⟨y, h⟩ : model l B) • modelDLog l B y = modelD l B y := by
  have hy' : (⟨y, h⟩ : model l B) ≠ 0 := fun h0 ↦ hy (congrArg Subtype.val h0)
  rw [modelDLog_of_mem h, smul_smul, mul_inv_cancel₀ hy', one_smul]

theorem modelDLog_eq_zero_iff (h : y ∈ model l B) (hy : y ≠ 0) :
    modelDLog l B y = 0 ↔ modelD l B y = 0 := by
  have hy' : (⟨y, h⟩ : model l B) ≠ 0 := fun h0 ↦ hy (congrArg Subtype.val h0)
  rw [modelDLog_of_mem h, smul_eq_zero, or_iff_right (inv_ne_zero hy')]

theorem modelDLog_mul (hx : x ∈ model l B) (hy : y ∈ model l B) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    modelDLog l B (x * y) = modelDLog l B x + modelDLog l B y := by
  have hx' : (⟨x, hx⟩ : model l B) ≠ 0 := fun h0 ↦ hx0 (congrArg Subtype.val h0)
  have hy' : (⟨y, hy⟩ : model l B) ≠ 0 := fun h0 ↦ hy0 (congrArg Subtype.val h0)
  rw [modelDLog_of_mem hx, modelDLog_of_mem hy, modelDLog_of_mem (mul_mem hx hy),
    modelD_mul hx hy, smul_add, smul_smul, smul_smul]
  have e : (⟨x * y, mul_mem hx hy⟩ : model l B) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [e, mul_inv, add_comm]
  congr 1 <;> congr 1 <;> field_simp

@[simp]
theorem modelDLog_one : modelDLog l B 1 = 0 := by
  rw [modelDLog_of_mem (one_mem _), modelD_of_mem (one_mem _)]
  have : (⟨1, one_mem _⟩ : model l B) = 1 := rfl
  rw [this, Derivation.map_one_eq_zero, smul_zero]

@[simp]
theorem modelDLog_algebraMap (c : l) : modelDLog l B (algebraMap l L c) = 0 := by
  rw [modelDLog_of_mem (IntermediateField.algebraMap_mem _ c), modelD_algebraMap, smul_zero]

theorem modelDLog_pow (hy : y ∈ model l B) (hy0 : y ≠ 0) (n : ℕ) :
    modelDLog l B (y ^ n) = (n : model l B) • modelDLog l B y := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, modelDLog_mul (pow_mem hy n) hy (pow_ne_zero n hy0) hy0, ih, Nat.cast_succ,
      add_smul, one_smul]

theorem modelDLog_inv (hy : y ∈ model l B) (hy0 : y ≠ 0) :
    modelDLog l B y⁻¹ = -modelDLog l B y := by
  have := modelDLog_mul (inv_mem hy) hy (inv_ne_zero hy0) hy0
  rw [inv_mul_cancel₀ hy0, modelDLog_one] at this
  exact eq_neg_of_add_eq_zero_left this.symm

theorem modelDLog_algebraMap_mul (c : l) (hc : c ≠ 0) (hy : y ∈ model l B) (hy0 : y ≠ 0) :
    modelDLog l B (algebraMap l L c * y) = modelDLog l B y := by
  rw [modelDLog_mul (IntermediateField.algebraMap_mem _ c) hy (by simpa using hc) hy0,
    modelDLog_algebraMap,
    zero_add]

end ModelDLog

/-! ### The group `W` and `dlog_A` (Lemma 6.4) -/

section W

variable (p : ℕ)

/-- Blueprint Section 6.3: the subgroup `W ≤ V_{L|l}` of elements of non-negative height. We
define it as the set of `v` having a representative `(N, a)`, `N` prime to `p`, with `a ∈ L_B`;
for `B` a transcendence basis this is `{0} ∪ {v ≠ 0 : ht(v) ≥ 0}` (`mem_W_iff`, from Lemma 4.3).
-/
def W (l : Type*) {L : Type*} [Field l] [Field L] [Algebra l L] (p : ℕ) {ι : Type*}
    (B : ι → L) : AddSubgroup (V l L) where
  carrier := {v | ∃ (N : ℕ) (a : Lˣ), IsVRep p v N a ∧ (a : L) ∈ model l B}
  zero_mem' := ⟨1, 1, ⟨one_pos, Nat.coprime_one_left p, by simp⟩, by simp⟩
  add_mem' := by
    rintro v w ⟨N, a, hv, ha⟩ ⟨M, b, hw, hb⟩
    refine ⟨N * M, a ^ M * b ^ N,
      ⟨Nat.mul_pos hv.pos hw.pos, Nat.coprime_mul_iff_left.2 ⟨hv.coprime, hw.coprime⟩, ?_⟩, ?_⟩
    · rw [cls_mul, cls_pow, cls_pow, ← hv.nsmul_eq, ← hw.nsmul_eq, smul_add, smul_smul,
        smul_smul, mul_comm M N]
    · push_cast
      exact mul_mem (pow_mem ha M) (pow_mem hb N)
  neg_mem' := by
    rintro v ⟨N, a, hv, ha⟩
    refine ⟨N, a⁻¹, ⟨hv.pos, hv.coprime, ?_⟩, ?_⟩
    · rw [smul_neg, hv.nsmul_eq, cls_inv]
    · push_cast
      exact inv_mem ha

variable {p} {B : ι → L} {v w : V l L}

theorem mem_W_iff_exists :
    v ∈ W l p B ↔ ∃ (N : ℕ) (a : Lˣ), IsVRep p v N a ∧ (a : L) ∈ model l B :=
  Iff.rfl

theorem cls_mem_W {a : Lˣ} (ha : (a : L) ∈ model l B) :
    cls (constUnits l L) (.ofMul a) ∈ W l p B :=
  ⟨1, a, isVRep_cls p a, ha⟩

variable (p)

open Classical in
/-- Blueprint Lemma 6.4(a): the logarithmic derivative `dlog_A : W → Ω_B`, with
`dlog_A(v) = N⁻¹ • dlog a` for every representative `(N, a)` of `v ∈ W` with `a ∈ L_B`
(`dlogA_eq`). It is `0` off `W` (`dlogA_of_notMem`). -/
noncomputable def dlogA (B : ι → L) (v : V l L) : Ω[model l B⁄l] :=
  if h : ∃ (N : ℕ) (a : Lˣ), IsVRep p v N a ∧ (a : L) ∈ model l B then
    ((h.choose : ℕ) : model l B)⁻¹ • modelDLog l B (h.choose_spec.choose : L)
  else 0

theorem dlogA_of_notMem (hv : v ∉ W l p B) : dlogA p B v = 0 :=
  dite_eq_right hv

variable [CharP L p] [IsRelAlgClosed l L]

omit [IsRelAlgClosed l L] in
theorem natCast_model_ne_zero {N : ℕ} {a : Lˣ} (hv : IsVRep p v N a) :
    ((N : ℕ) : model l B) ≠ 0 := fun h ↦
  hv.natCast_ne_zero p (by simpa using congrArg Subtype.val h)

/-- **Blueprint Lemma 6.4(a)**: `dlog_A(v) = N⁻¹ • da/a` for every representative `(N, a)` of
`v ∈ W` (`N` prime to `p`, `a ∈ L_B`). -/
theorem dlogA_eq {N : ℕ} {a : Lˣ} (hv : IsVRep p v N a) (ha : (a : L) ∈ model l B) :
    dlogA p B v = ((N : model l B))⁻¹ • modelDLog l B a := by
  have hex : ∃ (N : ℕ) (a : Lˣ), IsVRep p v N a ∧ (a : L) ∈ model l B := ⟨N, a, hv, ha⟩
  rw [dlogA, dite_eq_left hex]
  obtain ⟨hv₀, ha₀⟩ := hex.choose_spec.choose_spec
  obtain ⟨c, hc⟩ := V.rep_unique hv₀.nsmul_eq hv.nsmul_eq
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul] at hc
    exact pow_ne_zero _ (Units.ne_zero _) hc
  have key : (N : model l B) • modelDLog l B (hex.choose_spec.choose : L) =
      (hex.choose : model l B) • modelDLog l B a := by
    rw [← modelDLog_pow ha₀ (Units.ne_zero _), ← modelDLog_pow ha a.ne_zero, hc,
      modelDLog_algebraMap_mul c hc0 (pow_mem ha _) (pow_ne_zero _ a.ne_zero)]
  have hN := natCast_model_ne_zero p (B := B) hv
  have hN₀ := natCast_model_ne_zero p (B := B) hv₀
  calc ((hex.choose : ℕ) : model l B)⁻¹ • modelDLog l B (hex.choose_spec.choose : L)
      = ((hex.choose : model l B)⁻¹ * (N : model l B)⁻¹) •
          ((N : model l B) • modelDLog l B (hex.choose_spec.choose : L)) := by
        rw [smul_smul, mul_assoc, inv_mul_cancel₀ hN, mul_one]
    _ = (N : model l B)⁻¹ • modelDLog l B a := by
        rw [key, smul_smul, mul_comm, ← mul_assoc, mul_inv_cancel₀ hN₀, one_mul]

theorem dlogA_cls {a : Lˣ} (ha : (a : L) ∈ model l B) :
    dlogA p B (cls (constUnits l L) (.ofMul a)) = modelDLog l B a := by
  rw [dlogA_eq p (isVRep_cls p a) ha, Nat.cast_one, inv_one, one_smul]

theorem dlogA_zero : dlogA p B (0 : V l L) = 0 := by
  have h1 : ((1 : Lˣ) : L) ∈ model l B := by simp
  have := dlogA_cls p h1
  rwa [cls_one, Units.val_one, modelDLog_one] at this

/-- **Blueprint Lemma 6.4(a)**: `dlog_A` is additive on `W`. -/
theorem dlogA_add (hv : v ∈ W l p B) (hw : w ∈ W l p B) :
    dlogA p B (v + w) = dlogA p B v + dlogA p B w := by
  obtain ⟨N, a, hva, ha⟩ := mem_W_iff_exists.1 hv
  obtain ⟨M, b, hwb, hb⟩ := mem_W_iff_exists.1 hw
  have hrep : IsVRep p (v + w) (N * M) (a ^ M * b ^ N) :=
    ⟨Nat.mul_pos hva.pos hwb.pos, Nat.coprime_mul_iff_left.2 ⟨hva.coprime, hwb.coprime⟩, by
      rw [cls_mul, cls_pow, cls_pow, ← hva.nsmul_eq, ← hwb.nsmul_eq, smul_add, smul_smul,
        smul_smul, mul_comm M N]⟩
  have hmem : ((a ^ M * b ^ N : Lˣ) : L) ∈ model l B := by
    push_cast
    exact mul_mem (pow_mem ha M) (pow_mem hb N)
  have hN := natCast_model_ne_zero p (B := B) hva
  have hM := natCast_model_ne_zero p (B := B) hwb
  rw [dlogA_eq p hrep hmem, dlogA_eq p hva ha, dlogA_eq p hwb hb]
  push_cast
  rw [modelDLog_mul (pow_mem ha M) (pow_mem hb N) (pow_ne_zero _ a.ne_zero)
    (pow_ne_zero _ b.ne_zero), modelDLog_pow ha a.ne_zero, modelDLog_pow hb b.ne_zero, smul_add,
    smul_smul, smul_smul]
  congr 1 <;> congr 1 <;> field_simp

/-- **Blueprint Lemma 6.4(a)**: `dlog_A : W → Ω_B` as a homomorphism. -/
noncomputable def dlogAHom (l : Type*) {L : Type*} [Field l] [Field L] [Algebra l L] (p : ℕ)
    [CharP L p] [IsRelAlgClosed l L] {ι : Type*} (B : ι → L) : W l p B →+ Ω[model l B⁄l] where
  toFun v := dlogA p B v
  map_zero' := dlogA_zero p
  map_add' v w := dlogA_add p v.2 w.2

theorem dlogAHom_apply (v : W l p B) : dlogAHom l p B v = dlogA p B v :=
  rfl

theorem dlogA_neg (hv : v ∈ W l p B) : dlogA p B (-v) = -dlogA p B v :=
  map_neg (dlogAHom l p B) ⟨v, hv⟩

theorem dlogA_zsmul (hv : v ∈ W l p B) (n : ℤ) : dlogA p B (n • v) = n • dlogA p B v :=
  map_zsmul (dlogAHom l p B) n ⟨v, hv⟩

theorem dlogA_sub (hv : v ∈ W l p B) (hw : w ∈ W l p B) :
    dlogA p B (v - w) = dlogA p B v - dlogA p B w :=
  map_sub (dlogAHom l p B) ⟨v, hv⟩ ⟨w, hw⟩

variable [Fact p.Prime] [PerfectField L]

/-- The chosen representative of `v ∈ W` lies in `L_B`. -/
theorem vRep_mem_model (hv : v ∈ W l p B) : (vRep p v : L) ∈ model l B := by
  obtain ⟨N, a, hva, ha⟩ := mem_W_iff_exists.1 hv
  have h' := isVRep_vRep p v
  obtain ⟨c, hc⟩ := V.rep_unique h'.nsmul_eq hva.nsmul_eq
  set t : model l B :=
    ⟨algebraMap l L c * (a : L) ^ vRepNat p v,
      mul_mem (IntermediateField.algebraMap_mem _ c) (pow_mem ha _)⟩
  have ht0 : t ≠ 0 := fun h0 ↦ by
    have : (vRep p v : L) ^ N = 0 := by
      rw [hc]
      exact congrArg Subtype.val h0
    exact pow_ne_zero _ (Units.ne_zero _) this
  have hroot : Polynomial.aeval (vRep p v : L) (Polynomial.X ^ N - Polynomial.C t) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      IntermediateField.algebraMap_apply, hc, sub_self]
  have hsep : IsSeparable (model l B) (vRep p v : L) :=
    (Polynomial.separable_X_pow_sub_C t (natCast_model_ne_zero p hva) ht0).of_dvd
      (minpoly.dvd _ _ hroot)
  exact mem_model_of_isSeparable le_rfl hsep

/-- Blueprint Section 6.3: `W = {0} ∪ {v ≠ 0 : ht(v) ≥ 0}` (by Lemma 4.3(a)). -/
theorem mem_W_iff (hB : IsTranscendenceBasis l B) : v ∈ W l p B ↔ v = 0 ∨ 0 ≤ hgtV p B v := by
  constructor
  · intro hv
    by_cases hv0 : v = 0
    · exact Or.inl hv0
    exact Or.inr ((mem_model_iff_hgt_nonneg p hB ((isVRep_vRep p v).transcendental p hv0)).1
      (vRep_mem_model p hv))
  · rintro (rfl | h)
    · exact zero_mem _
    by_cases hv0 : v = 0
    · rw [hv0]
      exact zero_mem _
    exact ⟨_, _, isVRep_vRep p v,
      (mem_model_iff_hgt_nonneg p hB ((isVRep_vRep p v).transcendental p hv0)).2 h⟩

/-- **Blueprint Lemma 6.4(b)**: for `v ∈ W \ 0`, `dlog_A(v) ≠ 0` iff `ht(v) = 0`. -/
theorem dlogA_ne_zero_iff (hB : IsTranscendenceBasis l B) (hv : v ∈ W l p B) (hv0 : v ≠ 0) :
    dlogA p B v ≠ 0 ↔ hgtV p B v = 0 := by
  have h' := isVRep_vRep p v
  have hm := vRep_mem_model p hv
  have hN := natCast_model_ne_zero p (B := B) h'
  rw [dlogA_eq p h' hm, hgtV, hgt_eq_zero_iff p hB (h'.transcendental p hv0), Ne, smul_eq_zero,
    not_or, modelDLog_eq_zero_iff hm (Units.ne_zero _)]
  simp [hN, hm]

/-- **Blueprint Lemma 6.4(b)**: if `ht(v) = 0`, then `F · dlog_A(v) = ω_B(Q_v)`. (For `v = 0`
both sides are `0`.) -/
theorem span_dlogA_eq_omega (hB : IsTranscendenceBasis l B) (hv : hgtV p B v = 0) :
    (model l B) ∙ dlogA p B v = omega l p B (vRep p v : L) := by
  have hW : v ∈ W l p B := (mem_W_iff p hB).2 (Or.inr hv.ge)
  have h' := isVRep_vRep p v
  have hm := vRep_mem_model p hW
  have hN := natCast_model_ne_zero p (B := B) h'
  have ha0 : (⟨(vRep p v : L), hm⟩ : model l B) ≠ 0 :=
    fun h0 ↦ Units.ne_zero _ (congrArg Subtype.val h0)
  rw [omega_eq_span_of_hgt_eq_zero p hv, dlogA_eq p h' hm, modelDLog_of_mem hm, smul_smul]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 _ (mul_ne_zero (inv_ne_zero hN)
    (inv_ne_zero ha0))) _

/-- **Blueprint Lemma 6.4(c)**: `ker dlog_A = p W`. -/
theorem dlogA_eq_zero_iff (hB : IsTranscendenceBasis l B) (hv : v ∈ W l p B) :
    dlogA p B v = 0 ↔ ∃ w ∈ W l p B, v = p • w := by
  have hp := (Fact.out : p.Prime)
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  constructor
  · intro h0
    by_cases hv0 : v = 0
    · exact ⟨0, zero_mem _, by rw [hv0, smul_zero]⟩
    have hh : hgtV p B v ≠ 0 := fun h ↦ (dlogA_ne_zero_iff p hB hv hv0).2 h h0
    have hpos : 0 ≤ hgtV p B v := ((mem_W_iff p hB).1 hv).resolve_left hv0
    refine ⟨(p : ℚ)⁻¹ • v, (mem_W_iff p hB).2 (Or.inr ?_), ?_⟩
    · rw [hgtV_smul p hB hv0 (inv_ne_zero hp0), padicValRat.inv, padicValRat.self hp.one_lt]
      omega
    · rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, mul_inv_cancel₀ hp0, one_smul]
  · rintro ⟨w, hw, rfl⟩
    have : CharP (model l B) p := (Algebra.charP_iff (model l B) L p).mpr inferInstance
    have e : dlogA p B (p • w) = p • dlogA p B w := map_nsmul (dlogAHom l p B) p ⟨w, hw⟩
    rw [e, ← Nat.cast_smul_eq_nsmul (model l B), CharP.cast_eq_zero, zero_smul]

/-- **Blueprint Lemma 6.4(c)**: `V = ⋃_j p^{-j} W`. -/
theorem exists_pow_nsmul_mem_W (hB : IsTranscendenceBasis l B) (v : V l L) :
    ∃ j : ℕ, p ^ j • v ∈ W l p B := by
  by_cases hv0 : v = 0
  · exact ⟨0, by rw [hv0, smul_zero]; exact zero_mem _⟩
  refine ⟨(-hgtV p B v).toNat, (mem_W_iff p hB).2 (Or.inr ?_)⟩
  rw [hgtV_pow_nsmul p hB hv0]
  omega

/-- **Blueprint Lemma 6.4(c)**: `⋂_j p^j W = 0`. -/
theorem eq_zero_of_forall_mem_pow_nsmul_W (hB : IsTranscendenceBasis l B)
    (h : ∀ j : ℕ, ∃ w ∈ W l p B, v = p ^ j • w) : v = 0 := by
  by_contra hv0
  obtain ⟨w, hw, hvw⟩ := h ((hgtV p B v).toNat + 1)
  have hw0 : w ≠ 0 := fun h0 ↦ hv0 (by rw [hvw, h0, smul_zero])
  have hpos : 0 ≤ hgtV p B w := ((mem_W_iff p hB).1 hw).resolve_left hw0
  have e := hgtV_pow_nsmul p hB hw0 ((hgtV p B v).toNat + 1)
  rw [← hvw] at e
  omega

end W

/-! ### The adapted model, `K₀` and `Δ` (Lemma 6.5) -/

namespace CharPHyp

variable {K : Type*} [Field K] (H : CharPHyp K l L)
variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L]

/-- Blueprint Section 6.3: the representatives `ρ p (x i)` of `ψ(x i)` extend to a transcendence
basis of `L / l`. -/
theorem exists_trBasis : ∃ s : Set L, IsTranscendenceBasis l ((↑) : s → L) ∧
    ∀ i, (H.ρ p (H.x i) : L) ∈ s := by
  have h := (vAlgIndep_iff_algebraicIndependent_vRep p).1 H.vAlgIndep_x
  obtain ⟨t, hst, ht⟩ := exists_isTranscendenceBasis_superset h.to_subtype_range
  exact ⟨t, ht, fun i ↦ hst ⟨i, rfl⟩⟩

/-- Blueprint Section 6.3: the transcendence basis `A ⊇ {a₁, a₂, a₃}` of `L / l`, as a set. -/
noncomputable def trBasis : Set L :=
  (H.exists_trBasis p).choose

/-- The transcendence basis `A`, as a family. -/
def B : H.trBasis p → L :=
  Subtype.val

theorem isTranscendenceBasis_B : IsTranscendenceBasis l (H.B p) :=
  (H.exists_trBasis p).choose_spec.1

theorem ρ_x_mem_trBasis (i : Fin 3) : (H.ρ p (H.x i) : L) ∈ H.trBasis p :=
  (H.exists_trBasis p).choose_spec.2 i

/-- Blueprint Section 6.3: the adapted model `F = L_A`. -/
noncomputable abbrev F : IntermediateField l L :=
  model l (H.B p)

variable [IsRelAlgClosed l L]

/-- The `x i` have height `0` (their representatives belong to `A`). -/
theorem hgtV_x (i : Fin 3) : hgtV p (H.B p) (H.ψK (H.x i)) = 0 :=
  hgt_apply p (H.isTranscendenceBasis_B p) ⟨_, H.ρ_x_mem_trBasis p i⟩

variable [PerfectField K]

/-- Blueprint Lemma 6.5(a): `{0} ∪ ψ⁻¹(W)` is closed under addition (this uses
Proposition 6.1 through Lemma 6.5(b)). -/
theorem K₀_add_mem {x y : K} (hx : H.ψK x ∈ W l p (H.B p)) (hy : H.ψK y ∈ W l p (H.B p)) :
    H.ψK (x + y) ∈ W l p (H.B p) := by
  sorry

/-- **Blueprint Lemma 6.5(a)**: the subfield `K₀ = {0} ∪ ψ⁻¹(W)` of `K`. (Since `ψK 0 = 0 ∈ W`,
its carrier is `{x | ψK x ∈ W}`.) -/
noncomputable def K₀ : Subfield K where
  carrier := {x | H.ψK x ∈ W l p (H.B p)}
  mul_mem' {x y} hx hy := by
    change H.ψK (x * y) ∈ W l p (H.B p)
    rcases eq_or_ne x 0 with rfl | hx0
    · simp
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    rw [H.ψK_mul hx0 hy0]
    exact add_mem hx hy
  one_mem' := by
    change H.ψK 1 ∈ W l p (H.B p)
    rw [ψK_one]
    exact zero_mem _
  add_mem' hx hy := H.K₀_add_mem p hx hy
  zero_mem' := by
    change H.ψK 0 ∈ W l p (H.B p)
    rw [ψK_zero]
    exact zero_mem _
  neg_mem' {x} hx := by
    change H.ψK (-x) ∈ W l p (H.B p)
    rw [ψK_neg]
    exact hx
  inv_mem' x hx := by
    change H.ψK x⁻¹ ∈ W l p (H.B p)
    rw [ψK_inv]
    exact neg_mem hx

theorem mem_K₀_iff {x : K} : x ∈ H.K₀ p ↔ H.ψK x ∈ W l p (H.B p) :=
  Iff.rfl

theorem mem_K₀_iff_hgtV {x : K} (hx : x ∉ H.k) :
    x ∈ H.K₀ p ↔ 0 ≤ hgtV p (H.B p) (H.ψK x) := by
  rw [mem_K₀_iff, mem_W_iff p (H.isTranscendenceBasis_B p), or_iff_right (H.ψK_ne_zero hx)]

/-- `k ⊆ K₀` (Lemma 6.5(a)). -/
theorem mem_K₀_of_mem {x : K} (hx : x ∈ H.k) : x ∈ H.K₀ p := by
  rw [mem_K₀_iff, H.ψK_eq_zero_iff.2 hx]
  exact zero_mem _

theorem x_mem_K₀ (i : Fin 3) : (H.x i : K) ∈ H.K₀ p := by
  rw [H.mem_K₀_iff_hgtV p (H.x_notMem i), H.hgtV_x p i]

/-- The elements `x i` of (A3), as units of `K₀`. -/
noncomputable def xK₀ (i : Fin 3) : (H.K₀ p)ˣ :=
  Units.mk0 ⟨H.x i, H.x_mem_K₀ p i⟩ fun h ↦ (H.x i).ne_zero (congrArg Subtype.val h)

theorem ψ_units_map_subtype (u : (H.K₀ p)ˣ) :
    H.ψ (.ofMul (Units.map ((H.K₀ p).subtype : H.K₀ p →* K) u)) = H.ψK ((u : H.K₀ p) : K) := by
  rw [← ψK_units, Units.coe_map]
  rfl

/-- `ψ` restricted to `K₀ˣ`, as a homomorphism to `W`. -/
noncomputable def ψW : Additive (H.K₀ p)ˣ →+ W l p (H.B p) :=
  (H.ψ.comp (MonoidHom.toAdditive (Units.map ((H.K₀ p).subtype : H.K₀ p →* K)))).codRestrict
    _ fun x ↦ by
      change H.ψ (.ofMul (Units.map ((H.K₀ p).subtype : H.K₀ p →* K) (Additive.toMul x))) ∈ _
      rw [ψ_units_map_subtype]
      exact (Additive.toMul x : (H.K₀ p)ˣ).val.2

/-- Blueprint Section 6.3: `Δ = dlog_A ∘ ψ : K₀ˣ → Ω_A`. -/
noncomputable def Δhom : Additive (H.K₀ p)ˣ →+ Ω[H.F p⁄l] :=
  (dlogAHom l p (H.B p)).comp (H.ψW p)

theorem Δhom_apply (x : (H.K₀ p)ˣ) :
    H.Δhom p (.ofMul x) = dlogA p (H.B p) (H.ψK ((x : H.K₀ p) : K)) := by
  rw [← ψ_units_map_subtype]
  rfl

/-- (H0): `Δ(-1) = 0`. -/
theorem Δhom_neg_one : H.Δhom p (.ofMul (-1)) = 0 := by
  rw [Δhom_apply, Units.val_neg, Units.val_one, Subfield.coe_neg, Subfield.coe_one, ψK_neg_one,
    dlogA_zero]

/-- (H1), **Blueprint Lemma 6.5(b)**: for `x ∈ K₀`, `x` is primitive iff `1 - x` is (by
Proposition 6.1, `ψ(x)` and `ψ(1 - x)` have the same height). -/
theorem Δhom_eq_zero_iff_one_sub (x : (H.K₀ p)ˣ) (hx : (1 : H.K₀ p) - x ≠ 0) :
    H.Δhom p (.ofMul x) = 0 ↔ H.Δhom p (.ofMul (Units.mk0 (1 - x) hx)) = 0 := by
  sorry

/-- (H2), **Blueprint Lemma 6.5(b)**: for primitive `x`, `Δ(1 - x) ∈ F · Δ(x)` (both span
`ω_A(Q_x)`, by Lemma 6.4(b) and Proposition 6.1). -/
theorem Δhom_one_sub_mem_span (x : (H.K₀ p)ˣ) (hx : (1 : H.K₀ p) - x ≠ 0)
    (h : H.Δhom p (.ofMul x) ≠ 0) :
    H.Δhom p (.ofMul (Units.mk0 (1 - x) hx)) ∈ (H.F p) ∙ H.Δhom p (.ofMul x) := by
  sorry

/-- **Blueprint Lemma 6.5(c)**: the `x i` are primitive and `Δ(x₀), Δ(x₁), Δ(x₂)` are linearly
independent (`Δ(x i) = N_i⁻¹ • dlog a_i` with `a_i ∈ A`). -/
theorem linearIndependent_Δhom_x :
    LinearIndependent (H.F p) fun i ↦ H.Δhom p (.ofMul (H.xK₀ p i)) := by
  sorry

/-- (H3), **Blueprint Lemma 6.5(c)**: for any three lines (or vectors) in `Ω_A` there is a
primitive `z` (a monomial in the `x i`) such that `F · Δ(z)` is none of them. -/
theorem exists_Δhom_notMem_span (v₁ v₂ v₃ : Ω[H.F p⁄l]) : ∃ z : (H.K₀ p)ˣ,
    H.Δhom p (.ofMul z) ∉ (H.F p) ∙ v₁ ∧ H.Δhom p (.ofMul z) ∉ (H.F p) ∙ v₂ ∧
      H.Δhom p (.ofMul z) ∉ (H.F p) ∙ v₃ := by
  sorry

/-- The data of the abstract Step B (blueprint Sections 6.4, 6.5) for `Δ = dlog_A ∘ ψ`, with
`K₀`, `F = L_A` and `Ω = Ω_A`. -/
noncomputable def data : StepBData (H.K₀ p) (H.F p) Ω[H.F p⁄l] :=
  StepBData.ofAddMonoidHom (H.Δhom p) (H.Δhom_neg_one p) (H.Δhom_eq_zero_iff_one_sub p)
    (H.Δhom_one_sub_mem_span p) (H.exists_Δhom_notMem_span p)

theorem data_Δ (x : H.K₀ p) : (H.data p).Δ x = dlogA p (H.B p) (H.ψK x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · rw [(H.data p).Δ_zero, ZeroMemClass.coe_zero, ψK_zero, dlogA_zero]
  · rw [data, StepBData.ofAddMonoidHom_Δ_of_ne_zero _ _ _ _ _ hx, Δhom_apply, Units.val_mk0]

/-- Blueprint Section 6.3: `x ∈ K₀` is *primitive* (`Δ(x) ≠ 0`) iff `x ∉ k` and `ht ψ(x) = 0`. -/
theorem data_Δ_ne_zero_iff (x : H.K₀ p) :
    (H.data p).Δ x ≠ 0 ↔ (x : K) ∉ H.k ∧ hgtV p (H.B p) (H.ψK x) = 0 := by
  rw [data_Δ]
  by_cases hx : (x : K) ∈ H.k
  · simp [hx, H.ψK_eq_zero_iff.2 hx, dlogA_zero]
  · rw [dlogA_ne_zero_iff p (H.isTranscendenceBasis_B p) x.2 (H.ψK_ne_zero hx)]
    simp [hx]

/-- **Blueprint Lemma 6.5(b)**: for primitive `x`, the scalar `μ(x) ∈ F` with
`Δ(1 - x) = μ(x) Δ(x)` lies in the point `Q_x`. -/
theorem μ_mem_pointV {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) :
    ((H.data p).μ x : L) ∈ pointV l (H.ψK x) := by
  sorry

/-- **Blueprint Proposition 6.9** (`prop:tau`): the field embedding `τ : K₀ → F ⊆ L`, with
`τ(x) = t(x) = μ(x)/(μ(x) - 1)` for primitive `x` (`τ_eq_μ_div`). -/
noncomputable def τ : H.K₀ p →+* L :=
  (algebraMap (H.F p) L).comp (H.data p).τ

theorem τ_apply (x : H.K₀ p) : H.τ p x = ((H.data p).τ x : L) :=
  rfl

theorem τ_mem_F (x : H.K₀ p) : H.τ p x ∈ H.F p :=
  ((H.data p).τ x).2

theorem τ_eq_μ_div {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) :
    H.τ p x = ((H.data p).μ x : L) / ((H.data p).μ x - 1 : L) := by
  rw [τ_apply, (H.data p).τ_eq_μ_div hx]
  push_cast
  rfl

include H p in
/-- **Blueprint Proposition 6.9**: `K` and `L` have the same characteristic (`K₀` embeds into
`L`). -/
theorem ringChar_eq : ringChar K = ringChar L := by
  have : CharP (H.K₀ p) p := (H.τ p).charP (H.τ p).injective p
  have : CharP K p := charP_of_injective_ringHom (H.K₀ p).subtype_injective p
  rw [ringChar.eq K p, ringChar.eq L p]

include H in
/-- `K` has characteristic `p` (Proposition 6.9). -/
theorem charP_K : CharP K p := by
  rw [← ringChar.eq_iff, H.ringChar_eq p, ringChar.eq L p]

end CharPHyp

end MilnorAlgDep
