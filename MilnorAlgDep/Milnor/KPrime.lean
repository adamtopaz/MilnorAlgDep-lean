module

public import MilnorAlgDep.Milnor.DegOne
public import MilnorAlgDep.Char0.DLog
public import MilnorAlgDep.Milnor.PrimeField

/-!
# The subfield `k'` of the proof of Theorem C

Blueprint Section 7.3: the statement (`eq:dep`) and Lemma 7.3 (`lem:kprime`).

Let `K, L` be fields, `l₀` the algebraic closure of the prime field in `L`, and
`φ : 𝒦_*(K) → 𝒦_*(L)` a graded homomorphism with `φ₁` injective. Let `ψ : K^× → V_{L|l₀}` be the
composition of `φ₁ ∘ [·]` with the projection `L^×_ℚ → V_{L|l₀}` (`TheoremC.psi`). Then:

* (`eq:dep`, `TheoremC.not_vAlgIndep_psi`) for `x + y = 1`, `ψ(x)` and `ψ(y)` are algebraically
  dependent over `l₀` (or one of them is `0`);
* (Lemma 7.3, `TheoremC.psi_eq_zero_of_add_eq_one`) if `ψ(z) = 0` and `z + y = 1`, then
  `ψ(y) = 0`, provided `ψ` satisfies (A3), (A4) holds and `K` contains a transcendental element;
  hence `k' = {0} ∪ ker ψ` is a subfield of `K` (`subfieldOfKer`).

The proof of Lemma 7.3 distinguishes three cases: (i) `z` is not a root of unity
(`TheoremC.psi_eq_zero_of_not_root`, using Lemma 7.2(b)); (ii) `z` is a root of unity and
`char K > 0` (`TheoremC.psi_eq_zero_of_ringChar_ne_zero`); (iii) `z` is a root of unity and
`char K = 0` (`TheoremC.psi_eq_zero_of_root`, using the logarithmic derivative
`Δ = dlog ∘ ψ : K^× → Ω[L⁄l₀]`, `TheoremC.delta`).

## Remarks on the blueprint

* In the blueprint, `ker ψ` is shown to be closed under `z ↦ 1 - z` (for `z ≠ 1`); here this is
  stated for pairs of units `z + y = 1`. Case (i) uses that `φ₁[z] ≠ 0` (injectivity of `φ₁` and
  `[z] ≠ 0` in `K^×_ℚ` when `z` is not a root of unity) and that `φ₁[z] ∈ C_L = ker(L^×_ℚ → V)` is
  then `(1/N)[c]` with `c ∈ l₀` not a root of unity.
* In case (iii), the blueprint's `u = c(1 - x)/(c - 1)` is the unit `c · (1 - x) · (-ζ)⁻¹`, and
  `1 - u = (1 - cx) ζ⁻¹`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf MilnorKQ

variable {K L : Type*} [Field K] [Field L]

/-- An additive homomorphism into `VOf H` kills the roots of unity. -/
theorem map_eq_zero_of_pow_eq_one {H : Subgroup Lˣ} (f : Additive Kˣ →+ VOf H) {z : Kˣ} {n : ℕ}
    (hn : 0 < n) (hz : z ^ n = 1) : f (.ofMul z) = 0 := by
  apply nsmul_left_cancel hn.ne'
  rw [← map_nsmul, ← ofMul_pow, hz, ofMul_one, map_zero, smul_zero]

/-- Blueprint (S2), characteristic `0`: if `v ≠ 0` and `v, w ∈ V_{L|l}` are algebraically
dependent over `l`, then `dlog w` is an `L`-multiple of `dlog v`. -/
theorem exists_dlog_eq_smul_of_not_vAlgIndep {l : Type*} [Field l] [Algebra l L] [CharZero L]
    [IsRelAlgClosed l L] {v w : V l L} (h : ¬ VAlgIndep l ![v, w]) (hv : v ≠ 0) :
    ∃ μ : L, dlog l L w = μ • dlog l L v := by
  rw [vAlgIndep_pair_iff_linearIndependent_dlog, LinearIndependent.pair_iff] at h
  push Not at h
  obtain ⟨s, t, hst, hne⟩ := h
  have hv' : dlog l L v ≠ 0 := fun h0 ↦ hv (dlog_eq_zero_iff.1 h0)
  have ht : t ≠ 0 := by
    rintro rfl
    rw [zero_smul, add_zero, smul_eq_zero] at hst
    exact hne (hst.resolve_right hv') rfl
  refine ⟨-(t⁻¹ * s), ?_⟩
  rw [neg_smul, ← smul_smul, ← smul_neg, eq_inv_smul_iff₀ ht, eq_neg_iff_add_eq_zero, add_comm,
    hst]

section subfieldOfKer

variable {H : Subgroup Lˣ} (f : Additive Kˣ →+ VOf H)
  (hf : ∀ z y : Kˣ, (z : K) + y = 1 → f (.ofMul z) = 0 → f (.ofMul y) = 0)

/-- Blueprint Lemma 7.3: if `ker f` is closed under `z ↦ 1 - z`, then `{0} ∪ ker f` is a subfield
of `K`. -/
def subfieldOfKer : Subfield K where
  carrier := {x | ∀ hx : x ≠ 0, f (.ofMul (Units.mk0 x hx)) = 0}
  zero_mem' h := absurd rfl h
  one_mem' h := by
    rw [show Units.mk0 (1 : K) h = 1 from Units.ext rfl, ofMul_one, map_zero]
  mul_mem' {x y} hx hy h := by
    have hx0 : x ≠ 0 := left_ne_zero_of_mul h
    have hy0 : y ≠ 0 := right_ne_zero_of_mul h
    rw [show Units.mk0 (x * y) h = Units.mk0 x hx0 * Units.mk0 y hy0 from Units.ext rfl,
      ofMul_mul, map_add, hx hx0, hy hy0, add_zero]
  inv_mem' {x} hx h := by
    have hx0 : x ≠ 0 := fun h0 ↦ h (by rw [h0, inv_zero])
    rw [show Units.mk0 x⁻¹ h = (Units.mk0 x hx0)⁻¹ from Units.ext rfl, ofMul_inv, map_neg,
      hx hx0, neg_zero]
  neg_mem' {x} hx h := by
    have hx0 : x ≠ 0 := neg_ne_zero.1 h
    rw [show Units.mk0 (-x) h = -1 * Units.mk0 x hx0 from Units.ext (by simp), ofMul_mul,
      map_add, hx hx0, add_zero, map_eq_zero_of_pow_eq_one f two_pos (by simp)]
  add_mem' {x y} hx hy h := by
    by_cases hx0 : x = 0
    · subst hx0
      simp only [zero_add] at h ⊢
      exact hy h
    by_cases hy0 : y = 0
    · subst hy0
      simp only [add_zero] at h ⊢
      exact hx h
    have hz0 : -y / x ≠ 0 := div_ne_zero (neg_ne_zero.2 hy0) hx0
    have hw0 : 1 + y / x ≠ 0 := by
      rwa [← div_self hx0, ← add_div, div_ne_zero_iff, and_iff_left hx0]
    have hzw : ((Units.mk0 _ hz0 : Kˣ) : K) + Units.mk0 _ hw0 = 1 := by
      simp only [Units.val_mk0, neg_div]
      ring
    have hz : f (.ofMul (Units.mk0 _ hz0)) = 0 := by
      rw [show Units.mk0 (-y / x) hz0 = -1 * Units.mk0 y hy0 * (Units.mk0 x hx0)⁻¹ from
          Units.ext (by simp [div_eq_mul_inv]),
        ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg, hx hx0, hy hy0,
        map_eq_zero_of_pow_eq_one f two_pos (by simp)]
      simp
    rw [show Units.mk0 (x + y) h = Units.mk0 x hx0 * Units.mk0 _ hw0 from
        Units.ext (by simp [mul_add, mul_div_cancel₀ _ hx0]),
      ofMul_mul, map_add, hx hx0, hf _ _ hzw hz, add_zero]

theorem mem_subfieldOfKer {x : Kˣ} : (x : K) ∈ subfieldOfKer f hf ↔ f (.ofMul x) = 0 :=
  ⟨fun h ↦ by simpa using h x.ne_zero, fun h hx ↦ by simpa using h⟩

end subfieldOfKer

namespace TheoremC

variable (l₀ : Subfield L) (φ : MilnorKQ (⊥ : Subgroup Kˣ) →ₐ[ℚ] MilnorKQ (⊥ : Subgroup Lˣ))

/-- Blueprint 7.3: the homomorphism `ψ : K^× → V_{L|l₀}`, the composition of `φ₁ ∘ [·]` with the
projection `L^×_ℚ → V_{L|l₀}`. -/
noncomputable def psi : Additive Kˣ →+ V l₀ L :=
  (VOf.proj (bot_le : ⊥ ≤ constUnits l₀ L) ∘ₗ degOne φ).toAddMonoidHom.comp (cls ⊥)

theorem psi_apply (x : Kˣ) :
    psi l₀ φ (.ofMul x) = VOf.proj (bot_le : ⊥ ≤ constUnits l₀ L) (degOne φ 〚x〛) :=
  rfl

variable {l₀} (hl₀ : ∀ x : L, x ∈ l₀ ↔ IsAlgebraic (⊥ : Subfield L) x) {φ}
include hl₀

theorem isRelAlgClosed_of_hl₀ : IsRelAlgClosed l₀ L :=
  IsRelAlgClosed.of_subfield (isRelAlgClosed_of_forall_mem_iff hl₀)

/-- `C_L`: an element of `L^×_ℚ` in the kernel of the projection to `V_{L|l₀}` is `(1/N)[c]` with
`c ∈ l₀`, i.e. `c` algebraic over the prime field. -/
theorem isAlgebraic_of_proj_eq_zero {w : VOf (⊥ : Subgroup Lˣ)}
    (hw : VOf.proj (bot_le : ⊥ ≤ constUnits l₀ L) w = 0) {N : ℕ} {c : Lˣ}
    (hc : N • w = cls ⊥ (.ofMul c)) : IsAlgebraic (⊥ : Subfield L) (c : L) := by
  have h0 : VOf.proj (bot_le : ⊥ ≤ constUnits l₀ L) (cls ⊥ (.ofMul c)) = 0 := by
    rw [← hc, map_nsmul, hw, smul_zero]
  rw [proj_cls] at h0
  exact isAlgebraic_bot_of_isAlgebraic hl₀ (V.isAlgebraic_of_cls_eq_zero h0)

variable (hφ : IsGraded φ)
include hφ

/-- Blueprint 7.3, (`eq:dep`): for units `x, y` with `x + y = 1`, the elements `ψ(x)` and `ψ(y)`
of `V_{L|l₀}` are algebraically dependent (or one of them is `0`). -/
theorem not_vAlgIndep_psi {x y : Kˣ} (hxy : (x : K) + y = 1) :
    ¬ VAlgIndep l₀ ![psi l₀ φ (.ofMul x), psi l₀ φ (.ofMul y)] := by
  have := isRelAlgClosed_of_hl₀ hl₀
  apply not_vAlgIndep_of_ι_mul_ι_eq_zero
  rw [psi_apply, psi_apply, ← MilnorKQ.proj_ι, ← MilnorKQ.proj_ι, ← map_mul, ← hφ.apply_ι,
    ← hφ.apply_ι, ← map_mul, ι_mul_ι_eq_zero _ hxy, map_zero, map_zero]

variable (hφ₁ : Function.Injective (degOne φ))
include hφ₁

/-- Blueprint Lemma 7.3, case (i): if `ψ(z) = 0`, `z + y = 1` and `z` is not a root of unity, then
`ψ(y) = 0`. Indeed `φ₁[z] = (1/N)[c]` is non-zero with `c ∈ l₀` not a root of unity; writing
`φ₁[y] = (1/N')[b]`, we get `{c, b} = N N' φ {z, y} = 0`, so `b ∈ l₀` by Lemma 7.2(b). -/
theorem psi_eq_zero_of_not_root {z y : Kˣ} (hzy : (z : K) + y = 1)
    (hz : psi l₀ φ (.ofMul z) = 0) (hz' : ∀ n : ℕ, 0 < n → z ^ n ≠ 1) :
    psi l₀ φ (.ofMul y) = 0 := by
  have hz0 : degOne φ 〚z〛 ≠ 0 := by
    rw [Ne, ← map_zero (degOne φ), hφ₁.eq_iff, VOf.cls_eq_zero_iff]
    rintro ⟨n, hn, h⟩
    exact hz' n hn (Subgroup.mem_bot.1 h)
  obtain ⟨N, c, hN, hc⟩ := exists_nsmul_eq_cls (degOne φ 〚z〛)
  obtain ⟨N', b, hN', hb⟩ := exists_nsmul_eq_cls (degOne φ 〚y〛)
  have hcalg : IsAlgebraic (⊥ : Subfield L) (c : L) := isAlgebraic_of_proj_eq_zero hl₀ hz hc
  have hcroot : ∀ n : ℕ, 0 < n → c ^ n ≠ 1 := by
    intro n hn h
    apply hz0
    apply nsmul_left_cancel hN.ne'
    rw [hc, smul_zero, VOf.cls_eq_zero_iff]
    exact ⟨n, hn, Subgroup.mem_bot.2 h⟩
  have hsym : symbol ⊥ c b = 0 := by
    rw [symbol, ← hc, ← hb, map_nsmul, map_nsmul, smul_mul_smul_comm, ← hφ.apply_ι,
      ← hφ.apply_ι, ← map_mul, ι_mul_ι_eq_zero _ hzy, map_zero, smul_zero]
  have hbalg : IsAlgebraic (⊥ : Subfield L) (b : L) := by
    by_contra hb'
    exact symbol_ne_zero_of_isAlgebraic_of_transcendental hcalg hcroot hb' hsym
  apply nsmul_left_cancel hN'.ne'
  rw [smul_zero, psi_apply, ← map_nsmul, hb, proj_cls]
  exact VOf.cls_eq_zero_of_mem (mem_constUnits_subfield.2 ((hl₀ _).2 hbalg))

omit hl₀ hφ hφ₁ in
/-- Blueprint Lemma 7.3, case (ii): if `char K > 0` and `y` is algebraic over the prime field (for
instance `y = 1 - ζ` with `ζ` a root of unity), then `y` is a root of unity, so `ψ(y) = 0`. -/
theorem psi_eq_zero_of_ringChar_ne_zero (hK : ringChar K ≠ 0) {y : Kˣ}
    (hy : IsAlgebraic (⊥ : Subfield K) (y : K)) : psi l₀ φ (.ofMul y) = 0 := by
  obtain ⟨n, hn, h⟩ := exists_pow_eq_one_of_isAlgebraic_bot hK y.ne_zero hy
  exact map_eq_zero_of_pow_eq_one _ hn (Units.ext (by simpa using h))

section CharZero

variable [CharZero L]

variable (l₀ φ) in
/-- Blueprint Lemma 7.3 (iii): `Δ = dlog ∘ ψ : K^× → Ω[L⁄l₀]` (characteristic `0`). -/
noncomputable def delta : Additive Kˣ →+ Ω[L⁄l₀] :=
  (dlog l₀ L).comp (psi l₀ φ)

omit hl₀ hφ hφ₁ in
theorem delta_apply (x : Kˣ) : delta l₀ φ (.ofMul x) = dlog l₀ L (psi l₀ φ (.ofMul x)) :=
  rfl

omit hl₀ hφ hφ₁ in
theorem delta_mul (x y : Kˣ) :
    delta l₀ φ (.ofMul (x * y)) = delta l₀ φ (.ofMul x) + delta l₀ φ (.ofMul y) := by
  rw [ofMul_mul, map_add]

omit hl₀ hφ hφ₁ in
theorem delta_inv (x : Kˣ) : delta l₀ φ (.ofMul x⁻¹) = -delta l₀ φ (.ofMul x) := by
  rw [ofMul_inv, map_neg]

omit hl₀ hφ hφ₁ in
theorem delta_eq_zero_of_pow_eq_one {z : Kˣ} {n : ℕ} (hn : 0 < n) (hz : z ^ n = 1) :
    delta l₀ φ (.ofMul z) = 0 := by
  rw [delta_apply, map_eq_zero_of_pow_eq_one _ hn hz, map_zero]

omit hφ hφ₁ in
/-- `ker Δ = ker ψ`, since `dlog` is injective (Lemma 6.3(c)). -/
theorem delta_eq_zero_iff (x : Kˣ) : delta l₀ φ (.ofMul x) = 0 ↔ psi l₀ φ (.ofMul x) = 0 := by
  have := isRelAlgClosed_of_hl₀ hl₀
  exact dlog_eq_zero_iff

omit hφ₁ in
/-- (`eq:dep`) in terms of `Δ`: if `x + y = 1` and `Δ(x) ≠ 0`, then `Δ(y) ∈ L Δ(x)`. -/
theorem exists_delta_eq_smul {x y : Kˣ} (hxy : (x : K) + y = 1)
    (hx : delta l₀ φ (.ofMul x) ≠ 0) :
    ∃ μ : L, delta l₀ φ (.ofMul y) = μ • delta l₀ φ (.ofMul x) := by
  have := isRelAlgClosed_of_hl₀ hl₀
  exact exists_dlog_eq_smul_of_not_vAlgIndep (not_vAlgIndep_psi hl₀ hφ hxy)
    fun h ↦ hx (by rw [delta_apply, h, map_zero])

omit hl₀ hφ hφ₁ in
/-- Blueprint Lemma 7.3 (iii), the claim: there is `x ∈ K`, transcendental over the prime field,
with `Δ(x) ∉ L Δ(c)`. By (A3) there is `x₁` with `Δ(x₁) ∉ L Δ(c)`; if `x₁` is algebraic, one of
`z₀`, `z₀ x₁` works, for any transcendental `z₀`. -/
theorem exists_transcendental_delta_not_mem
    (A3 : ∃ x : Fin 2 → Kˣ, VAlgIndep l₀ fun i ↦ psi l₀ φ (.ofMul (x i)))
    (hK : ∃ x : K, Transcendental (⊥ : Subfield K) x) (c : Kˣ) :
    ∃ x : Kˣ, Transcendental (⊥ : Subfield K) (x : K) ∧
      ∀ μ : L, delta l₀ φ (.ofMul x) ≠ μ • delta l₀ φ (.ofMul c) := by
  obtain ⟨x, hx⟩ := A3
  have hli : LinearIndependent L
      ![delta l₀ φ (.ofMul (x 0)), delta l₀ φ (.ofMul (x 1))] := by
    convert vAlgIndep_iff_linearIndependent_dlog.1 hx using 1
    ext i
    fin_cases i <;> rfl
  have h1 : ∃ x₁ : Kˣ, ∀ μ : L, delta l₀ φ (.ofMul x₁) ≠ μ • delta l₀ φ (.ofMul c) := by
    by_contra! h
    obtain ⟨μ₀, h₀⟩ := h (x 0)
    obtain ⟨μ₁, h₁⟩ := h (x 1)
    have h01 := LinearIndependent.pair_iff.1 hli μ₁ (-μ₀) (by
      rw [h₀, h₁, smul_smul, smul_smul, neg_mul, neg_smul, mul_comm, add_neg_cancel])
    refine hli.ne_zero 0 ?_
    simp only [Matrix.cons_val_zero]
    rw [h₀, neg_eq_zero.1 h01.2, zero_smul]
  obtain ⟨x₁, hx₁⟩ := h1
  by_cases ht : Transcendental (⊥ : Subfield K) (x₁ : K)
  · exact ⟨x₁, ht, hx₁⟩
  rw [Transcendental, not_not] at ht
  obtain ⟨z₀, hz₀⟩ := hK
  have hz₀0 : z₀ ≠ 0 := fun h ↦ hz₀ (h ▸ isAlgebraic_zero)
  let u₀ := Units.mk0 z₀ hz₀0
  by_cases hu₀ : ∀ μ : L, delta l₀ φ (.ofMul u₀) ≠ μ • delta l₀ φ (.ofMul c)
  · exact ⟨u₀, hz₀, hu₀⟩
  push Not at hu₀
  obtain ⟨μ, hμ⟩ := hu₀
  refine ⟨u₀ * x₁, fun h ↦ hz₀ ?_, fun μ' h ↦ hx₁ (μ' - μ) ?_⟩
  · have : z₀ = ((u₀ * x₁ : Kˣ) : K) * (x₁ : K)⁻¹ := by simp [u₀]
    rw [this]
    exact h.mul (IsAlgebraic.inv_iff.2 ht)
  · rw [delta_mul, hμ] at h
    rw [sub_smul, ← h]
    abel

/-- Blueprint Lemma 7.3, case (iii): if `char L = 0`, `ζ` is a root of unity and `ζ + c = 1`,
then `ψ(c) = 0`. -/
theorem psi_eq_zero_of_root
    (A3 : ∃ x : Fin 2 → Kˣ, VAlgIndep l₀ fun i ↦ psi l₀ φ (.ofMul (x i)))
    (hK : ∃ x : K, Transcendental (⊥ : Subfield K) x) {ζ c : Kˣ} (hζc : (ζ : K) + c = 1) {n : ℕ}
    (hn : 0 < n) (hζ : ζ ^ n = 1) : psi l₀ φ (.ofMul c) = 0 := by
  rw [← delta_eq_zero_iff hl₀]
  by_contra hc
  set Δ : Kˣ → Ω[L⁄l₀] := fun x ↦ delta l₀ φ (.ofMul x) with hΔ
  have hΔmul (x y : Kˣ) : Δ (x * y) = Δ x + Δ y := delta_mul x y
  have hΔinv (x : Kˣ) : Δ x⁻¹ = -Δ x := delta_inv x
  obtain ⟨x, hxt, hxc⟩ := exists_transcendental_delta_not_mem A3 hK c
  change ∀ μ : L, Δ x ≠ μ • Δ c at hxc
  change Δ c ≠ 0 at hc
  -- `Δ(c)` and `Δ(x)` are linearly independent
  have hind (s t : L) (h : s • Δ c + t • Δ x = 0) : s = 0 ∧ t = 0 := by
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero, smul_eq_zero] at h
      exact ⟨h.resolve_right hc, rfl⟩
    · refine absurd ?_ (hxc (-(t⁻¹ * s)))
      rw [neg_smul, ← smul_smul, ← smul_neg, eq_inv_smul_iff₀ ht, eq_neg_iff_add_eq_zero,
        add_comm, h]
  have hx0 : Δ x ≠ 0 := fun h ↦ hxc 0 (by rw [h, zero_smul])
  -- algebraicity of `ζ` and `c`
  have hζalg : IsAlgebraic (⊥ : Subfield K) (ζ : K) :=
    isAlgebraic_bot_of_pow_eq_one hn (by rw [← Units.val_pow_eq_pow_val, hζ, Units.val_one])
  have hc' : (c : K) = 1 - ζ := eq_sub_of_add_eq' hζc
  have hcalg : IsAlgebraic (⊥ : Subfield K) (c : K) := hc' ▸ isAlgebraic_one.sub hζalg
  have hζ0 : (ζ : K) ≠ 0 := ζ.ne_zero
  have hc0 : (c : K) ≠ 0 := c.ne_zero
  -- the units `1 - x` and `1 - c x`
  have hx1 : (1 : K) - x ≠ 0 := fun h ↦ hxt (by rw [← sub_eq_zero.1 h]; exact isAlgebraic_one)
  have hcx1 : (1 : K) - c * x ≠ 0 := by
    intro h
    refine hxt ?_
    have : (x : K) = (c : K)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact (sub_eq_zero.1 h).symm)
    rw [this]
    exact IsAlgebraic.inv_iff.2 hcalg
  let x' := Units.mk0 _ hx1
  let w := Units.mk0 _ hcx1
  have hxx' : (x : K) + x' = 1 := by simp [x']
  have hcxw : ((c * x : Kˣ) : K) + w = 1 := by simp [w]
  have hcx0 : Δ (c * x) ≠ 0 := fun h ↦ by
    rw [hΔmul] at h
    exact one_ne_zero (hind 1 1 (by rw [one_smul, one_smul, h])).1
  obtain ⟨μ, hμ⟩ := exists_delta_eq_smul hl₀ hφ hxx' hx0
  obtain ⟨μ', hμ'⟩ := exists_delta_eq_smul hl₀ hφ hcxw hcx0
  change Δ x' = μ • Δ x at hμ
  change Δ w = μ' • Δ (c * x) at hμ'
  -- `u = c (1 - x) / (c - 1)` and `1 - u = (1 - c x) / ζ`
  let u : Kˣ := c * x' * (-ζ)⁻¹
  let v : Kˣ := w * ζ⁻¹
  have huv : (u : K) + v = 1 := by
    simp only [u, v, x', w, Units.val_mul, Units.val_inv_eq_inv_val, Units.val_neg, Units.val_mk0]
    rw [hc']
    field_simp
    ring
  have hζ2 : (-ζ) ^ (2 * n) = 1 := by
    rw [pow_mul, neg_sq, ← pow_mul, mul_comm, pow_mul, hζ, one_pow]
  have hΔu : Δ u = Δ c + μ • Δ x := by
    simp only [u, hΔmul, hΔinv, ← hμ]
    rw [show Δ (-ζ) = 0 from delta_eq_zero_of_pow_eq_one (by omega) hζ2, neg_zero, add_zero]
  have hΔv : Δ v = μ' • (Δ c + Δ x) := by
    simp only [v, hΔmul, hΔinv, hμ']
    rw [show Δ ζ = 0 from delta_eq_zero_of_pow_eq_one hn hζ, neg_zero, add_zero]
  have hu0 : Δ u ≠ 0 := fun h ↦ by
    rw [hΔu] at h
    exact one_ne_zero (hind 1 μ (by rw [one_smul, h])).1
  obtain ⟨ν, hν⟩ := exists_delta_eq_smul hl₀ hφ huv hu0
  change Δ v = ν • Δ u at hν
  rw [hΔv, hΔu] at hν
  have hcoef := hind (μ' - ν) (μ' - ν * μ) (by
    have : (μ' - ν) • Δ c + (μ' - ν * μ) • Δ x =
        μ' • (Δ c + Δ x) - ν • (Δ c + μ • Δ x) := by
      simp only [smul_add, sub_smul, mul_smul]
      abel
    rw [this, hν, sub_self])
  have key : μ' * (1 - μ) = 0 := by
    have h1 := sub_eq_zero.1 hcoef.1
    have h2 := sub_eq_zero.1 hcoef.2
    rw [mul_sub, mul_one, sub_eq_zero]
    nth_rw 1 [h2]
    rw [h1]
  rcases mul_eq_zero.1 key with h | h
  · -- `μ' = 0`: `1 - c x ∈ ker ψ`, so `1 - c x` is a root of unity by (i)
    have hw : psi l₀ φ (.ofMul w) = 0 := (delta_eq_zero_iff hl₀ w).1 (by
      change Δ w = 0
      rw [hμ', h, zero_smul])
    by_cases hwroot : ∃ m : ℕ, 0 < m ∧ w ^ m = 1
    · obtain ⟨m, hm, hwm⟩ := hwroot
      have hwalg : IsAlgebraic (⊥ : Subfield K) (w : K) :=
        isAlgebraic_bot_of_pow_eq_one hm (by rw [← Units.val_pow_eq_pow_val, hwm, Units.val_one])
      refine hxt ?_
      have : (x : K) = (1 - w) * (c : K)⁻¹ := by
        simp only [w, Units.val_mk0]
        field_simp
        ring
      rw [this]
      exact (isAlgebraic_one.sub hwalg).mul (IsAlgebraic.inv_iff.2 hcalg)
    · push Not at hwroot
      have := psi_eq_zero_of_not_root hl₀ hφ hφ₁ (by rw [add_comm]; exact hcxw) hw hwroot
      exact hcx0 ((delta_eq_zero_iff hl₀ _).2 this)
  · -- `μ = 1`: `1 - 1/x ∈ ker ψ`, so `1 - 1/x` is a root of unity by (i)
    have hμ1 : μ = 1 := (sub_eq_zero.1 h).symm
    have ht0 : (1 : K) - (x : K)⁻¹ ≠ 0 := by
      intro h0
      refine hxt ?_
      have : (x : K) = 1 := by rw [← inv_inj, inv_one]; exact (sub_eq_zero.1 h0).symm
      rw [this]
      exact isAlgebraic_one
    let t := Units.mk0 _ ht0
    have htx : (t : K) + ((x⁻¹ : Kˣ) : K) = 1 := by simp [t]
    have htdecomp : t = -1 * x' * x⁻¹ := by
      ext
      simp only [t, x', Units.val_mk0, Units.val_mul, Units.val_neg, Units.val_one,
        Units.val_inv_eq_inv_val]
      field_simp
      ring
    have ht : psi l₀ φ (.ofMul t) = 0 := (delta_eq_zero_iff hl₀ t).1 (by
      change Δ t = 0
      rw [htdecomp, hΔmul, hΔmul, hΔinv, hμ, hμ1, one_smul,
        show Δ (-1) = 0 from delta_eq_zero_of_pow_eq_one two_pos (by simp)]
      abel)
    by_cases htroot : ∃ m : ℕ, 0 < m ∧ t ^ m = 1
    · obtain ⟨m, hm, htm⟩ := htroot
      have htalg : IsAlgebraic (⊥ : Subfield K) (t : K) :=
        isAlgebraic_bot_of_pow_eq_one hm (by rw [← Units.val_pow_eq_pow_val, htm, Units.val_one])
      refine hxt (IsAlgebraic.inv_iff.1 ?_)
      rw [show (x : K)⁻¹ = 1 - t by simp [t]]
      exact isAlgebraic_one.sub htalg
    · push Not at htroot
      have hxinv := psi_eq_zero_of_not_root hl₀ hφ hφ₁ htx ht htroot
      refine hx0 ?_
      change delta l₀ φ (.ofMul x) = 0
      rw [delta_apply, show (psi l₀ φ) (.ofMul x) = 0 by
        rw [← neg_eq_zero, ← map_neg, ← ofMul_inv, hxinv], map_zero]

end CharZero

/-- **Blueprint Lemma 7.3** (`lem:kprime`), key step: if `ψ(z) = 0` and `z + y = 1`, then
`ψ(y) = 0`. So `k' = {0} ∪ ker ψ` is a subfield of `K` (`subfieldOfKer`). -/
theorem psi_eq_zero_of_add_eq_one
    (A3 : ∃ x : Fin (if ringChar L = 0 then 2 else 3) → Kˣ,
      VAlgIndep l₀ fun i ↦ psi l₀ φ (.ofMul (x i)))
    (A4 : ringChar L ≠ 0 → ringChar K ≠ 0) (hK : ∃ x : K, Transcendental (⊥ : Subfield K) x)
    {z y : Kˣ} (hzy : (z : K) + y = 1) (hz : psi l₀ φ (.ofMul z) = 0) :
    psi l₀ φ (.ofMul y) = 0 := by
  by_cases hroot : ∃ n : ℕ, 0 < n ∧ z ^ n = 1
  · obtain ⟨n, hn, hzn⟩ := hroot
    by_cases hKc : ringChar K = 0
    · have hLc : ringChar L = 0 := by
        by_contra h
        exact A4 h hKc
      have : CharZero L := (CharP.ringChar_zero_iff_CharZero L).1 hLc
      obtain ⟨x, hx⟩ := A3
      have h2 : (if ringChar L = 0 then 2 else 3) = 2 := by simp
      exact psi_eq_zero_of_root hl₀ hφ hφ₁
        ⟨x ∘ Fin.cast h2.symm, hx.comp _ (Fin.cast_injective _)⟩ hK hzy hn hzn
    · have hzalg : IsAlgebraic (⊥ : Subfield K) (z : K) :=
        isAlgebraic_bot_of_pow_eq_one hn (by rw [← Units.val_pow_eq_pow_val, hzn, Units.val_one])
      apply psi_eq_zero_of_ringChar_ne_zero hKc
      rw [eq_sub_of_add_eq' hzy]
      exact isAlgebraic_one.sub hzalg
  · push Not at hroot
    exact psi_eq_zero_of_not_root hl₀ hφ hφ₁ hzy hz hroot

end TheoremC

end MilnorAlgDep
