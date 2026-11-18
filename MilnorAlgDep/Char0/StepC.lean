module

public import MilnorAlgDep.Char0.Delta

/-!
# Step C in characteristic zero: identification of `ψ`

Blueprint Section 6.6 read with `Γ = 0` (`F = L`, `K₀ = K`, `e₀ = 0`, `σ_x = τ x`):

* `Char0Hyp.τ_mem_pointV`, `Char0Hyp.τ_mem_range_of_mem`, `Char0Hyp.τ_notMem_range`:
  **Lemma 6.10** (`lem:tauinQ`): `τ(x) ∈ Q_x \ l` for `x ∉ k`, and `τ(k) ⊆ l`;
* `Char0Hyp.exists_rat_Δ_eq_smul_dlogL_τ`: **Lemma 6.11** (`lem:theta`): there is `θ ∈ ℚˣ` with
  `Δ x = θ • dlog τ(x)` for all `x ∉ k`;
* `Char0Hyp.exists_rat_ψ_eq`: **Proposition 6.12** (`prop:rational`), case `Γ = 0`:
  `ψ = θ • [τ ·]`, by injectivity of `dlog`.

In characteristic `0` the parts of Lemma 6.11 about the height `e(x)` and the normalized triples
are vacuous (`σ_x = τ x`), and so is the final step `e₀ = 0` of its proof.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf KaehlerDifferential Submodule IntermediateField

namespace Char0Hyp

variable {K l L : Type*} [Field K] [Field l] [Field L] [Algebra l L] [CharZero L]
  [IsRelAlgClosed l L] (H : Char0Hyp K l L)

/-! ### Lemma 6.10 -/

/-- **Blueprint Lemma 6.10** (`lem:tauinQ`), first part: `τ(x) ∈ Q_x` for `x ∉ k`
(from `τ x = μ x / (μ x - 1)` and `μ(x) ∈ Q_x`, Lemma 6.5(b)). -/
theorem τ_mem_pointV {x : K} (hx : x ∉ H.k) : H.τ x ∈ pointV l (H.ψK x) := by
  have hμ := H.μ_mem_pointV hx
  rw [H.τ_eq_μ_div hx]
  exact div_mem hμ (sub_mem hμ (one_mem _))

omit [CharZero L] in
/-- The points `Q_{x₁}`, `Q_{x₂}` meet in `l`. -/
theorem mem_range_of_mem_pointV_x {z : L} (h₁ : z ∈ pointV l (H.ψK H.x₁))
    (h₂ : z ∈ pointV l (H.ψK H.x₂)) : z ∈ (algebraMap l L).range := by
  have : z ∈ pointV l (H.ψK H.x₁) ⊓ pointV l (H.ψK H.x₂) := ⟨h₁, h₂⟩
  rw [ψK_units, ψK_units, pointV_inf_pointV_eq_bot H.A3, IntermediateField.mem_bot] at this
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc⟩

/-- **Blueprint Lemma 6.10** (`lem:tauinQ`), second part: `τ(k) ⊆ l`. For `c ∈ kˣ` and `x ∉ k`,
`τ(c) = τ(c x) / τ(x) ∈ Q_x`; take `x = x₁, x₂`. -/
theorem τ_mem_range_of_mem {c : K} (hc : c ∈ H.k) : H.τ c ∈ (algebraMap l L).range := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [map_zero]
    exact zero_mem _
  have key : ∀ x : K, x ∉ H.k → H.τ c ∈ pointV l (H.ψK x) := by
    intro x hx
    have hx0 := H.ne_zero_of_notMem hx
    have hcx : c * x ∉ H.k := fun h ↦ hx (by
      have := mul_mem (inv_mem hc) h
      rwa [inv_mul_cancel_left₀ hc0] at this)
    have h1 := H.τ_mem_pointV hcx
    rw [H.ψK_mul hc0 hx0, H.ψK_eq_zero_iff.2 hc, zero_add, map_mul] at h1
    have := div_mem h1 (H.τ_mem_pointV hx)
    rwa [mul_div_cancel_right₀ _ (H.τ_ne_zero hx0)] at this
  exact H.mem_range_of_mem_pointV_x (key _ H.x₁_notMem) (key _ H.x₂_notMem)

/-- **Blueprint Lemma 6.10** (`lem:tauinQ`), third part: `τ(x) ∉ l` for `x ∉ k`.

If `τ x ∈ l`, then `μ x ∈ l` and `dlog b = (M μ(x) / N) • dlog a` for representatives `(N, a)` of
`ψ x` and `(M, b)` of `ψ (1 - x)`, with `b ∈ Q_a`. By the eigenvalue lemma (Lemma 2.2) `μ x` is
rational, so `τ x = τ(r)` for a rational number `r`, and `x = r ∈ k`. -/
theorem τ_notMem_range {x : K} (hx : x ∉ H.k) : H.τ x ∉ (algebraMap l L).range := by
  rintro ⟨c₀, hc₀⟩
  have : CharZero K := H.charZero
  have hΔ := H.data_Δ_ne_zero hx
  -- `μ x ∈ l`
  obtain ⟨κ, hμ⟩ : ∃ κ : l, H.data.μ x = algebraMap l L κ :=
    ⟨c₀ / (c₀ - 1), by rw [H.μ_eq_τ_div hx, ← hc₀, map_div₀, map_sub, map_one]⟩
  -- representatives of `ψ x` and `ψ (1 - x)`
  obtain ⟨N, a, hN, ha, hva⟩ := V.exists_rep (H.ψK_ne_zero hx)
  obtain ⟨M, b, hM, hwb⟩ := exists_nsmul_eq_cls (H.ψK (1 - x))
  have hb : (b : L) ∈ point l (a : L) := by
    rw [← pointV_eq_point hN hva, ← H.pointV_ψK_one_sub hx, pointV_eq_point hM hwb]
    exact self_mem_point _
  have hM0 : (M : L) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  -- `dlog b = (M κ / N) • dlog a`
  have hrel : dlogL l (b : L) = algebraMap l L (M * κ / N) • dlogL l (a : L) := by
    have e := H.data.Δ_one_sub hΔ
    rw [data_Δ, data_Δ, hμ, dlog_of_nsmul_eq_cls hM hwb, dlog_of_nsmul_eq_cls hN hva] at e
    have := congrArg ((M : L) • ·) e
    simp only [smul_smul, mul_inv_cancel₀ hM0, one_smul] at this
    rw [this, map_div₀, map_mul, map_natCast, map_natCast]
    congr 1
    ring
  obtain ⟨q, hq⟩ := exists_ratCast_of_dlogL_eq (IsRelAlgClosed.transcendental ha) hb b.ne_zero
    hrel
  -- so `μ x` is rational
  have hμq : H.data.μ x = ((q * N / M : ℚ) : L) := by
    have : CharZero l := (algebraMap l L).charZero
    have hN0' : (N : l) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have hM0' : (M : l) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
    have : κ = ((q * N / M : ℚ) : l) := by
      rw [Rat.cast_div, Rat.cast_mul, hq, Rat.cast_natCast, Rat.cast_natCast]
      field_simp
    rw [hμ, this, map_ratCast]
  -- hence `τ x = τ r` for a rational number `r`, and `x = r ∈ k`
  have hτ : H.τ x = H.τ (((q * N / M) / (q * N / M - 1) : ℚ) : K) := by
    rw [map_ratCast, H.τ_eq_μ_div hx, hμq, Rat.cast_div _ (q * N / M - 1), Rat.cast_sub,
      Rat.cast_one]
  exact hx (by rw [H.τ.injective hτ]; exact SubfieldClass.ratCast_mem H.k _)

/-- `τ x` is transcendental over `l` for `x ∉ k`. -/
theorem τ_transcendental {x : K} (hx : x ∉ H.k) : Transcendental l (H.τ x) :=
  IsRelAlgClosed.transcendental (H.τ_notMem_range hx)

/-- `Q_{τ x} = Q_x` for `x ∉ k`. -/
theorem point_τ {x : K} (hx : x ∉ H.k) : point l (H.τ x) = pointV l (H.ψK x) := by
  obtain ⟨N, a, hN, ha, hva⟩ := V.exists_rep (H.ψK_ne_zero hx)
  have h := H.τ_mem_pointV hx
  rw [pointV_eq_point hN hva] at h ⊢
  exact point_eq_of_mem (IsRelAlgClosed.transcendental ha) (H.τ_transcendental hx) h

/-! ### Lemma 6.11 -/

/-- For `x ∉ k`, `Δ x = c • dlog τ(x)` for some `c ∈ Q_x` (blueprint, proof of Lemma 6.11:
`Δ x` and `dlog σ_x` span the same line, and `θ(x) ∈ Q_x`). -/
theorem exists_Δ_eq_smul_dlogL_τ {x : K} (hx : x ∉ H.k) :
    ∃ c ∈ pointV l (H.ψK x), H.data.Δ x = c • dlogL l (H.τ x) := by
  have hx0 := H.ne_zero_of_notMem hx
  set σ : Lˣ := Units.mk0 (H.τ x) (H.τ_ne_zero hx0)
  have hu : cls (constUnits l L) (.ofMul σ) ≠ 0 := fun h ↦
    H.τ_notMem_range hx ((V.cls_eq_zero_iff' σ).1 h)
  have hp : pointV l (H.ψK x) = pointV l (cls (constUnits l L) (.ofMul σ)) := by
    rw [pointV_cls, Units.val_mk0, H.point_τ hx]
  obtain ⟨c, hc, he⟩ := exists_mem_pointV_dlog_eq_smul hu hp
  refine ⟨c, by rw [hp]; exact hc, ?_⟩
  rw [data_Δ, he, dlog_cls, Units.val_mk0]

/-- Blueprint, proof of Lemma 6.11: for transverse `x, y`, the coefficients `θ(x)`, `θ(y)` with
`Δ x = θ(x) • dlog τ(x)`, `Δ y = θ(y) • dlog τ(y)` agree (compare with `Δ (x y)`, using
`τ(x y) = τ(x) τ(y)`). -/
theorem coeff_eq_of_transverse {x y : K} (h : H.data.Transverse x y) {c c' : L}
    (hc : H.data.Δ x = c • dlogL l (H.τ x)) (hc' : H.data.Δ y = c' • dlogL l (H.τ y)) :
    c = c' := by
  have hx0 := H.data.ne_zero_of_Δ_ne_zero h.Δ_ne_zero_left
  have hy0 := H.data.ne_zero_of_Δ_ne_zero h.Δ_ne_zero_right
  obtain ⟨c'', -, hc''⟩ := H.exists_Δ_eq_smul_dlogL_τ (H.notMem_of_data_Δ_ne_zero h.Δ_mul_ne_zero)
  rw [h.Δ_mul, map_mul, dlogL_mul (H.τ_ne_zero hx0) (H.τ_ne_zero hy0), hc, hc', smul_add] at hc''
  have hc0 : c ≠ 0 := fun h0 ↦ h.Δ_ne_zero_left (by rw [hc, h0, zero_smul])
  have hc'0 : c' ≠ 0 := fun h0 ↦ h.Δ_ne_zero_right (by rw [hc', h0, zero_smul])
  have hli : LinearIndependent L ![dlogL l (H.τ x), dlogL l (H.τ y)] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have := h.smul_add_smul_eq_zero (a := s / c) (b := t / c') (by
      rw [hc, hc', smul_smul, smul_smul, div_mul_cancel₀ s hc0, div_mul_cancel₀ t hc'0, hst])
    exact ⟨(div_eq_zero_iff.1 this.1).resolve_right hc0,
      (div_eq_zero_iff.1 this.2).resolve_right hc'0⟩
  obtain ⟨h₁, h₂⟩ := LinearIndependent.pair_iff.1 hli (c - c'') (c' - c'') (by
    rw [sub_smul, sub_smul, sub_add_sub_comm, hc'', sub_self])
  linear_combination h₁ - h₂

/-- **Blueprint Lemma 6.11** (`lem:theta`), characteristic `0`: there is `θ ∈ ℚ`, `θ ≠ 0`, with
`Δ x = θ • dlog τ(x)` for every `x ∉ k`.

The coefficient is constant by `coeff_eq_of_transverse` (any two primitive elements are
transverse to a common third one), lies in `Q_{x₁} ∩ Q_{x₂} = l`, and is rational by the
eigenvalue lemma applied to `τ(x₁)` and a representative of `ψ(x₁)`. -/
theorem exists_rat_Δ_eq_smul_dlogL_τ :
    ∃ r : ℚ, r ≠ 0 ∧ ∀ x : K, x ∉ H.k → H.data.Δ x = (r : L) • dlogL l (H.τ x) := by
  obtain ⟨θ, hθ₁, hθ⟩ := H.exists_Δ_eq_smul_dlogL_τ H.x₁_notMem
  obtain ⟨θ₂, hθ₂, hθ'⟩ := H.exists_Δ_eq_smul_dlogL_τ H.x₂_notMem
  have e₁₂ : θ = θ₂ := H.coeff_eq_of_transverse H.transverse_x hθ hθ'
  -- `θ` is constant
  have hconst : ∀ x : K, x ∉ H.k → H.data.Δ x = θ • dlogL l (H.τ x) := by
    intro x hx
    obtain ⟨c, -, hc⟩ := H.exists_Δ_eq_smul_dlogL_τ hx
    obtain ⟨z, hxz, hx₁z⟩ := H.data.exists_transverse_transverse (H.data_Δ_ne_zero hx)
      (H.data_Δ_ne_zero H.x₁_notMem)
    obtain ⟨cz, -, hcz⟩ :=
      H.exists_Δ_eq_smul_dlogL_τ (H.notMem_of_data_Δ_ne_zero hxz.Δ_ne_zero_right)
    rw [hc, H.coeff_eq_of_transverse hxz hc hcz, ← H.coeff_eq_of_transverse hx₁z hθ hcz]
  -- `θ ∈ l`
  obtain ⟨θ₀, rfl⟩ := H.mem_range_of_mem_pointV_x hθ₁ (e₁₂ ▸ hθ₂)
  -- `θ ∈ ℚ`, by the eigenvalue lemma for `τ x₁` and a representative of `ψ x₁`
  obtain ⟨N, a, hN, ha, hva⟩ := V.exists_rep (H.ψK_ne_zero H.x₁_notMem)
  have hamem : (a : L) ∈ point l (H.τ H.x₁) := by
    rw [H.point_τ H.x₁_notMem, pointV_eq_point hN hva]
    exact self_mem_point _
  have hN0 : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hrel : dlogL l (a : L) = algebraMap l L (N * θ₀) • dlogL l (H.τ H.x₁) := by
    have e := hθ
    rw [data_Δ, dlog_of_nsmul_eq_cls hN hva] at e
    have := congrArg ((N : L) • ·) e
    simp only [smul_smul, mul_inv_cancel₀ hN0, one_smul] at this
    rw [this, map_mul, map_natCast]
  obtain ⟨q, hq⟩ :=
    exists_ratCast_of_dlogL_eq (H.τ_transcendental H.x₁_notMem) hamem a.ne_zero hrel
  have hθq : algebraMap l L θ₀ = ((q / N : ℚ) : L) := by
    have : CharZero l := (algebraMap l L).charZero
    have hN0' : (N : l) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    have : θ₀ = ((q / N : ℚ) : l) := by
      rw [Rat.cast_div, hq, Rat.cast_natCast]
      field_simp
    rw [this, map_ratCast]
  refine ⟨q / N, fun h0 ↦ ?_, fun x hx ↦ by rw [hconst x hx, hθq]⟩
  apply H.data_Δ_ne_zero H.x₁_notMem
  rw [hconst _ H.x₁_notMem, hθq, h0, Rat.cast_zero, zero_smul]

/-! ### Proposition 6.12 -/

/-- **Blueprint Proposition 6.12** (`prop:rational`), case `Γ = 0`: there is `r ∈ ℚ`, `r ≠ 0`,
with `ψ(x) = r • [τ(x)]` for all `x ∈ Kˣ`. For `x ∉ k` this follows from Lemma 6.11 and the
injectivity of `dlog`; for `x ∈ k` both sides vanish by (A1) and `τ(k) ⊆ l`. -/
theorem exists_rat_ψ_eq :
    ∃ r : ℚ, r ≠ 0 ∧ ∀ x : Kˣ, H.ψ (.ofMul x) = r • 〚Units.map (H.τ : K →* L) x〛 := by
  obtain ⟨r, hr, h⟩ := H.exists_rat_Δ_eq_smul_dlogL_τ
  refine ⟨r, hr, fun x ↦ ?_⟩
  by_cases hx : (x : K) ∈ H.k
  · have h0 : cls (constUnits l L) (.ofMul (Units.map (H.τ : K →* L) x)) = 0 :=
      cls_eq_zero_of_mem (mem_constUnits.2 (by simpa using H.τ_mem_range_of_mem hx))
    rw [(H.A1 x).2 hx, h0, smul_zero]
  · apply dlog_injective
    rw [dlog_smul, dlog_cls, ← H.ψK_units, ← data_Δ, h _ hx, Units.coe_map]
    rfl

end Char0Hyp

end MilnorAlgDep
