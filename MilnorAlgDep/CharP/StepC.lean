module

public import MilnorAlgDep.CharP.StepCFields

/-!
# Step C in characteristic `p`: identification of `ψ` on `K₀`

Blueprint Section 6.6 with `Γ = ℤ`, and equation `eq:roots` from Section 6.5.

Throughout, `H : CharPHyp K l L` with `K`, `L` perfect, `L` of characteristic `p`, and `l`
relatively algebraically closed; `B = H.B p` is the adapted transcendence basis, `F = L_B` the
adapted model, `K₀ = H.K₀ p`, `Δ = (H.data p).Δ` and `τ = H.τ p : K₀ →+* L` the embedding of
Proposition 6.9. By Proposition 6.9 `K` has characteristic `p` (`CharPHyp.charP_K`).

## Main statements

* `eq:roots`: `CharPHyp.pow_mem_K₀` (`Frob(K₀) ⊆ K₀`), `CharPHyp.exists_pow_pow_mem_K₀`
  (`K = ⋃ Frob^{-j}(K₀)`), `CharPHyp.exists_primitive_root` and
  `CharPHyp.hgtV_pow_pow_of_primitive` (every `x ∈ K₀ \ k` is `Frob^j(x₀)` for a unique primitive
  `x₀`, with `j = ht ψ(x)`).
* **Lemma 6.10** (`lem:tauinQ`): `CharPHyp.τ_mem_pointV`, `CharPHyp.τ_mem_range_of_mem`,
  `CharPHyp.τ_notMem_range`.
* `exists_intCast_of_modelDLog_eq`: the eigenvalue lemma (Lemma 2.2) in the form used in
  Lemmas 6.10, 6.11 and `eq:lift`.
* **Lemma 6.11** (`lem:theta`): `CharPHyp.exists_θ`, through `CharPHyp.hgt_τ_eq_of_transverse`,
  `CharPHyp.exists_hgt_τ_coeff` (heights `e(x) = e₀` and coefficient `θ` constant) and
  `CharPHyp.hgt_τ_eq_zero` (`e₀ = 0`).
* `CharPHyp.exists_dlogA_eq_smul`, `CharPHyp.exists_intCast_of_dlogA_eq`: for primitive `x` and
  `v ∈ W ∩ G_{Q_x}`, `dlog_A(v) = c • dlog τ(x)` with `c ∈ F ∩ Q_x`, and `c ∈ F_p` if `c ∈ l`
  (eigenvalue lemma). These are shared by Lemma 6.11 (`v = ψ(x)`) and `eq:lift` (`v = ψ'(x)`).
* **Proposition 6.12** (`prop:rational`), case `Γ = ℤ`: `CharPHyp.exists_rat_ψ₀_eq`, broken into
  - `CharPHyp.exists_lift`: `eq:lift`;
  - `CharPHyp.exists_padic`: `eq:padic`, `ψ - r_j [τ] ∈ p^j W` on `K₀ˣ`;
  - `CharPHyp.exists_pow_eq_of_padic`: for one `j`, `(a s^{-N r_j})^M = c y^{p^j}` with
    `y ∈ E = l(s, a)` (from `exists_pow_eq_mul_pow_pow`, i.e. `eq:Epower`);
  - `exists_dvd_sub_of_forall_pow_eq`: the norm argument and unique factorization in `l[s]`
    (the `s`-adic order of `N_{E|l(s)}(a)`);
  - `exists_dvd_sub_of_dvd`: elementary arithmetic (`MN = p^β n'`, `ε = p^β m'`);
  - `CharPHyp.zsmul_ψ₀_eq_of_dvd`: the conclusion via `⋂ p^j W = 0`.

## Remarks on the blueprint

* In the proof of Proposition 6.12 the integers `r_j` need not be compatible
  (`r_{j+1} ≡ r_j`): only `eq:padic` for each `j` separately is used. We therefore state
  `eq:padic` as `∀ j, ∃ r, …`.
* The blueprint's representatives "with a common `N`" are replaced by the chosen representatives
  `(N, a)`, `(M, b)` and the powers `(N M, a^M)`, `(N M, b^N)` where a common denominator is needed
  (proof of Lemma 6.11).
* Lemma 6.10, `τ(k) ⊆ l`: `τ(c) ∈ Q_x` is shown for every `x ∈ K₀ \ k` (not only primitive `x`)
  and applied to `x 0`, `x 1`, whose points meet in `l`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf IntermediateField KaehlerDifferential

variable {l L : Type*} [Field l] [Field L] [Algebra l L] {ι : Type*}

/-! ### Auxiliary lemmas -/

section Aux

variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]

-- TODO(move): `CharP/Models.lean`.
/-- Two elements of the same point with the same height are `≈`-equivalent. -/
theorem sepEquiv_of_hgt_eq {B : ι → L} (hB : IsTranscendenceBasis l B) {s t : L}
    (h : SamePoint l s t) (hst : hgt l p B s = hgt l p B t) : SepEquiv l s t :=
  (levDiff_eq_zero_iff p h).1 (by rw [← hgt_sub_hgt p hB h, hst, sub_self])

-- TODO(move): `CharP/Models.lean`.
/-- If `s, t` lie in the same point and `ht s ≥ ht t`, then `s` is separable over `l(t)`. -/
theorem isSeparable_of_hgt_le {B : ι → L} (hB : IsTranscendenceBasis l B) {s t : L}
    (h : SamePoint l s t) (hst : hgt l p B t ≤ hgt l p B s) : IsSeparable l⟮t⟯ s :=
  (levDiff_nonneg_iff p h).1 (by rw [← hgt_sub_hgt p hB h]; omega)

omit [CharP L p] [PerfectField L] [IsRelAlgClosed l L] in
-- TODO(move): `Mathlib.Algebra.CharP.Defs`.
/-- An integer prime to `p` is invertible in a ring of characteristic `p`, with an inverse which
is the image of a natural number. -/
theorem exists_natCast_mul_eq_one (R : Type*) [Ring R] [CharP R p] {M : ℕ} (hM : M.Coprime p) :
    ∃ M' : ℕ, (M : R) * M' = 1 := by
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hM (Fact.out : p.Prime).one_lt
  exact ⟨m, by rw [← Nat.cast_mul, CharP.cast_eq_mod R p, hm, Nat.cast_one]⟩

omit [CharP L p] [PerfectField L] [IsRelAlgClosed l L] in
-- TODO(move): `Mathlib.Algebra.CharP.Defs`.
theorem natCast_ne_zero_of_coprime (R : Type*) [AddMonoidWithOne R] [CharP R p]
    {N : ℕ} (hN : N.Coprime p) : (N : R) ≠ 0 := by
  rw [ne_eq, CharP.cast_eq_zero_iff R p]
  exact fun hpN ↦ (Fact.out : p.Prime).one_lt.ne' (hN.symm.eq_one_of_dvd hpN)

omit [CharP L p] [PerfectField L] [IsRelAlgClosed l L] in
-- TODO(move): `Mathlib.Algebra.CharP.Defs`.
/-- In a field of characteristic `p`, an element `M • κ / N` with `M, N` prime to `p` is the image
of an integer iff `κ` is. -/
theorem exists_intCast_of_intCast_eq (R : Type*) [Field R] [CharP R p] {M N : ℕ}
    (hM : M.Coprime p) (hN : N.Coprime p) {κ : R} {m : ℤ} (h : (m : R) = M * κ * (N : R)⁻¹) :
    ∃ n : ℤ, (n : R) = κ := by
  obtain ⟨M', hM'⟩ := exists_natCast_mul_eq_one p R hM
  have hN0 : (N : R) ≠ 0 := natCast_ne_zero_of_coprime p R hN
  refine ⟨m * N * M', ?_⟩
  push_cast
  rw [h]
  field_simp
  linear_combination κ * hM'

omit [PerfectField L] [IsRelAlgClosed l L] in
-- TODO(move): `CharP/AdaptedModel.lean`.
/-- `dlog (1 - y) = -(y / (1 - y)) • dlog y` in `Ω_B`. -/
theorem modelDLog_one_sub {B : ι → L} {y : L} (hy : y ∈ model l B) (hy0 : y ≠ 0)
    (hy1 : 1 - y ≠ 0) :
    modelDLog l B (1 - y) = (-(⟨y, hy⟩ / (1 - ⟨y, hy⟩)) : model l B) • modelDLog l B y := by
  have h1y : 1 - y ∈ model l B := sub_mem (one_mem _) hy
  have e : (⟨1 - y, h1y⟩ : model l B) = 1 - ⟨y, hy⟩ := rfl
  have hy0' : (⟨y, hy⟩ : model l B) ≠ 0 := fun h0 ↦ hy0 (congrArg Subtype.val h0)
  have hy1' : (1 - ⟨y, hy⟩ : model l B) ≠ 0 := fun h0 ↦ hy1 (congrArg Subtype.val h0)
  rw [modelDLog_of_mem h1y, modelDLog_of_mem hy, smul_smul, modelD_of_mem h1y,
    modelD_of_mem hy, e, map_sub, Derivation.map_one_eq_zero, zero_sub, smul_neg, ← neg_smul]
  congr 1
  field_simp

omit [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L] in
/-- `t = μ/(μ - 1)` for `μ = -(s/(1 - s)) = s/(s - 1)` gives back `s` (end of the proof of
Lemma 6.11). -/
theorem neg_div_one_sub_div {F : Type*} [Field F] {s : F} (hs : 1 - s ≠ 0) :
    -(s / (1 - s)) / (-(s / (1 - s)) - 1) = s := by
  rw [show -(s / (1 - s)) - 1 = -(1 - s)⁻¹ by field_simp; ring]
  field_simp

end Aux

section LinearAlgebra

variable {K F Ω : Type*} [Field K] [Field F] [AddCommGroup Ω] [Module F Ω]

-- TODO(move): `StepB/Basic.lean`.
/-- If `x, y` are transverse and `Δ x = c • u`, `Δ y = c' • v`, then `u, v` are linearly
independent. -/
theorem StepBData.Transverse.linearIndependent_of_eq_smul {D : StepBData K F Ω} {x y : K}
    (h : D.Transverse x y) {u v : Ω} {c c' : F} (hc : D.Δ x = c • u) (hc' : D.Δ y = c' • v) :
    LinearIndependent F ![u, v] := by
  have hc0 : c ≠ 0 := fun h0 ↦ h.Δ_ne_zero_left (by rw [hc, h0, zero_smul])
  have hc'0 : c' ≠ 0 := fun h0 ↦ h.Δ_ne_zero_right (by rw [hc', h0, zero_smul])
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have := h.smul_add_smul_eq_zero (a := s / c) (b := t / c') (by
    rw [hc, hc', smul_smul, smul_smul, div_mul_cancel₀ s hc0, div_mul_cancel₀ t hc'0, hst])
  exact ⟨(div_eq_zero_iff.1 this.1).resolve_right hc0,
    (div_eq_zero_iff.1 this.2).resolve_right hc'0⟩

-- TODO(move): `StepB/Basic.lean`.
/-- Comparing coefficients: if `u, v` are linearly independent and
`c'' • (u + v) = c • u + c' • v`, then `c'' = c` and `c'' = c'`. -/
theorem eq_of_linearIndependent_pair {u v : Ω} (hli : LinearIndependent F ![u, v])
    {c c' c'' : F} (h : c'' • (u + v) = c • u + c' • v) : c'' = c ∧ c'' = c' := by
  obtain ⟨h₁, h₂⟩ := LinearIndependent.pair_iff.1 hli (c'' - c) (c'' - c') (by
    rw [sub_smul, sub_smul, sub_add_sub_comm, ← smul_add, h, sub_self])
  exact ⟨sub_eq_zero.1 h₁, sub_eq_zero.1 h₂⟩

end LinearAlgebra

namespace CharPHyp

variable {K : Type*} [Field K] [PerfectField K] (H : CharPHyp K l L)
variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]

/-! ### Primitive roots, `eq:roots` -/

/-- Blueprint `eq:roots`: `Frob(K₀) ⊆ K₀` (`ψ(x^p) = p ψ(x)` has height `ht ψ(x) + 1`). -/
theorem pow_mem_K₀ {x : K} (hx : x ∈ H.K₀ p) : x ^ p ∈ H.K₀ p :=
  pow_mem hx p

/-- Blueprint `eq:roots`: `K = ⋃_j Frob^{-j}(K₀)`, i.e. some `x^{p^j}` lies in `K₀`. -/
theorem exists_pow_pow_mem_K₀ (x : K) : ∃ j : ℕ, x ^ p ^ j ∈ H.K₀ p := by
  obtain ⟨j, hj⟩ := exists_pow_nsmul_mem_W p (H.isTranscendenceBasis_B p) (H.ψK x)
  exact ⟨j, by rw [mem_K₀_iff, ψK_pow]; exact hj⟩

theorem hgtV_nonneg {x : K} (hx : x ∈ H.K₀ p) (hxk : x ∉ H.k) :
    0 ≤ hgtV p (H.B p) (H.ψK x) :=
  (H.mem_K₀_iff_hgtV p hxk).1 hx

theorem notMem_of_primitive {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) : (x : K) ∉ H.k :=
  ((H.data_Δ_ne_zero_iff p x).1 hx).1

theorem hgtV_of_primitive {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) :
    hgtV p (H.B p) (H.ψK x) = 0 :=
  ((H.data_Δ_ne_zero_iff p x).1 hx).2

/-- Blueprint `eq:roots`: for a primitive `x₀`, `ht ψ(x₀^{p^j}) = j`. In particular the
decomposition `x = Frob^j(x₀)` of `exists_primitive_root` is unique. -/
theorem hgtV_pow_pow_of_primitive {x₀ : H.K₀ p} (hx₀ : (H.data p).Δ x₀ ≠ 0) (j : ℕ) :
    hgtV p (H.B p) (H.ψK ((x₀ : K) ^ p ^ j)) = j := by
  rw [ψK_pow, hgtV_pow_nsmul p (H.isTranscendenceBasis_B p)
    (H.ψK_ne_zero (H.notMem_of_primitive p hx₀)), H.hgtV_of_primitive p hx₀, zero_add]

/-- Blueprint `eq:roots`: every `x ∈ K₀ \ k` is `Frob^j(x₀)` with `x₀` primitive and
`j = ht ψ(x) ≥ 0` (the *primitive root* of `x`; `K` is perfect of characteristic `p`). -/
theorem exists_primitive_root (x : H.K₀ p) (hx : (x : K) ∉ H.k) :
    ∃ x₀ : H.K₀ p, (H.data p).Δ x₀ ≠ 0 ∧ x₀ ^ p ^ (hgtV p (H.B p) (H.ψK x)).toNat = x := by
  have : CharP K p := H.charP_K p
  set j := (hgtV p (H.B p) (H.ψK x)).toNat
  have hj : (j : ℤ) = hgtV p (H.B p) (H.ψK x) := Int.toNat_of_nonneg (H.hgtV_nonneg p x.2 hx)
  set y : K := (iterateFrobeniusEquiv K p j).symm x
  have hy : y ^ p ^ j = x := by
    rw [← iterateFrobeniusEquiv_def, RingEquiv.apply_symm_apply]
  have hyk : y ∉ H.k := fun h ↦ hx (hy ▸ pow_mem h _)
  have hhgt : hgtV p (H.B p) (H.ψK y) = 0 := by
    have := hgtV_pow_nsmul p (H.isTranscendenceBasis_B p) (H.ψK_ne_zero hyk) j
    rw [← ψK_pow, hy, ← hj] at this
    omega
  have hyK₀ : y ∈ H.K₀ p := (H.mem_K₀_iff_hgtV p hyk).2 hhgt.ge
  refine ⟨⟨y, hyK₀⟩, (H.data_Δ_ne_zero_iff p _).2 ⟨hyk, hhgt⟩, Subtype.ext ?_⟩
  rw [SubmonoidClass.coe_pow]
  exact hy

/-! ### Lemma 6.10 -/

omit [PerfectField K] [PerfectField L] [IsRelAlgClosed l L] in
theorem pointV_ψK_pow (x : K) {n : ℕ} (hn : n ≠ 0) :
    pointV l (H.ψK (x ^ n)) = pointV l (H.ψK x) := by
  rw [ψK_pow, ← Nat.cast_smul_eq_nsmul ℚ, pointV_smul (Nat.cast_ne_zero.2 hn)]

theorem τ_ne_zero {x : H.K₀ p} (hx : x ≠ 0) : H.τ p x ≠ 0 :=
  (map_ne_zero (H.τ p)).2 hx

/-- Lemma 6.10 for primitive `x`: `τ(x) = μ(x)/(μ(x) - 1) ∈ Q_x` (Lemma 6.5(b)). -/
theorem τ_mem_pointV_of_primitive {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) :
    H.τ p x ∈ pointV l (H.ψK x) := by
  have hμ := H.μ_mem_pointV p hx
  rw [H.τ_eq_μ_div p hx]
  exact div_mem hμ (sub_mem hμ (one_mem _))

/-- **Blueprint Lemma 6.10** (`lem:tauinQ`), first part: `τ(x) ∈ Q_x` for `x ∈ K₀ \ k` (from
`μ(x) ∈ Q_x`, Lemma 6.5(b), for primitive `x`, and `eq:roots` in general). -/
theorem τ_mem_pointV {x : H.K₀ p} (hx : (x : K) ∉ H.k) : H.τ p x ∈ pointV l (H.ψK x) := by
  obtain ⟨x₀, hx₀, hx₀x⟩ := H.exists_primitive_root p x hx
  generalize (hgtV p (H.B p) (H.ψK x)).toNat = j at hx₀x
  subst hx₀x
  rw [map_pow, SubmonoidClass.coe_pow,
    H.pointV_ψK_pow _ (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]
  exact pow_mem (H.τ_mem_pointV_of_primitive p hx₀) _

/-- For `c ∈ k` and `x ∈ K₀ \ k`, `τ(c) = τ(c x)/τ(x) ∈ Q_x`. -/
theorem τ_mem_pointV_of_mem {c : H.K₀ p} (hc : (c : K) ∈ H.k) {x : H.K₀ p}
    (hx : (x : K) ∉ H.k) : H.τ p c ∈ pointV l (H.ψK x) := by
  rcases eq_or_ne c 0 with rfl | hc0
  · rw [map_zero]
    exact zero_mem _
  have hc0' : (c : K) ≠ 0 := fun h ↦ hc0 (Subtype.ext h)
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx (zero_mem _)
  have hcx : ((c * x : H.K₀ p) : K) ∉ H.k := by
    intro h
    apply hx
    have := mul_mem (inv_mem hc) h
    rwa [Subfield.coe_mul, inv_mul_cancel_left₀ hc0'] at this
  have h1 := H.τ_mem_pointV p hcx
  rw [map_mul, Subfield.coe_mul, H.ψK_mul_of_mem hc hc0'] at h1
  have := div_mem h1 (H.τ_mem_pointV p hx)
  rwa [mul_div_cancel_right₀ _ (H.τ_ne_zero p hx0)] at this

omit [PerfectField K] [PerfectField L] in
/-- The points `Q_{x 0}` and `Q_{x 1}` meet in `l`. -/
theorem mem_range_of_mem_pointV_x {z : L} (h₀ : z ∈ pointV l (H.ψK (H.x 0)))
    (h₁ : z ∈ pointV l (H.ψK (H.x 1))) : z ∈ (algebraMap l L).range := by
  have hind : VAlgIndep l ![H.ψK (H.x 0), H.ψK (H.x 1)] := by
    have := H.vAlgIndep_x.comp ![0, 1] (by decide)
    convert this using 1
    ext i
    fin_cases i <;> rfl
  exact mem_range_of_mem_pointV_of_vAlgIndep hind h₀ h₁

/-- **Blueprint Lemma 6.10** (`lem:tauinQ`), second part: `τ(k) ⊆ l` (for `c ∈ kˣ` and primitive
`x`, `τ(c) = t(c x)/t(x) ∈ Q_x`; take two transverse `x`). -/
theorem τ_mem_range_of_mem {x : H.K₀ p} (hx : (x : K) ∈ H.k) :
    H.τ p x ∈ (algebraMap l L).range :=
  H.mem_range_of_mem_pointV_x
    (H.τ_mem_pointV_of_mem p hx (x := ⟨H.x 0, H.x_mem_K₀ p 0⟩) (H.x_notMem 0))
    (H.τ_mem_pointV_of_mem p hx (x := ⟨H.x 1, H.x_mem_K₀ p 1⟩) (H.x_notMem 1))

/-- For primitive `x`, the chosen representative `ρ x` of `ψ(x)` is a model generator. -/
theorem ρ_mem_F_of_primitive {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) :
    (H.ρ p x : L) ∈ H.F p ∧ modelD l (H.B p) (H.ρ p x) ≠ 0 :=
  (hgt_eq_zero_iff p (H.isTranscendenceBasis_B p)
    (H.transcendental_ρ p (H.notMem_of_primitive p hx))).1 (H.hgtV_of_primitive p hx)

/-- For primitive `x`, `Δ(x) = N⁻¹ • dlog a` for the chosen representative `(N, a)` of `ψ(x)`. -/
theorem Δ_eq_of_primitive {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) :
    (H.data p).Δ x = ((vRepNat p (H.ψK x) : H.F p))⁻¹ • modelDLog l (H.B p) (H.ρ p x) := by
  rw [data_Δ, dlogA_eq p (H.isVRep_ρ p x) (H.ρ_mem_F_of_primitive p hx).1]

/-- Lemma 6.10 for primitive `x`: `τ(x) ∉ l`. -/
theorem τ_notMem_range_of_primitive {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) :
    H.τ p x ∉ (algebraMap l L).range := by
  rintro ⟨c, hc⟩
  have : CharP l p := IsRelAlgClosed.charP l L p
  have hB := H.isTranscendenceBasis_B p
  have hxk := H.notMem_of_primitive p hx
  have h1x : (H.data p).Δ (1 - x) ≠ 0 := (H.data p).Δ_one_sub_ne_zero hx
  have h1xk := H.notMem_of_primitive p h1x
  -- `μ x ∈ l`
  obtain ⟨κ, hκ⟩ : ∃ κ : l, ((H.data p).μ x : L) = algebraMap l L κ := by
    refine ⟨c / (c - 1), ?_⟩
    rw [(H.data p).μ_eq_τ_div hx]
    push_cast
    rw [← τ_apply, ← hc, map_div₀, map_sub, map_one]
  -- the representatives `(N, a)` of `ψ x` and `(M, b)` of `ψ (1 - x)`
  have ha := (H.ρ_mem_F_of_primitive p hx).1
  have hda := (H.ρ_mem_F_of_primitive p hx).2
  set N := vRepNat p (H.ψK x) with hNdef
  set M := vRepNat p (H.ψK ((1 - x : H.K₀ p) : K)) with hMdef
  have hN := (H.isVRep_ρ p x).coprime
  have hM := (H.isVRep_ρ p ((1 - x : H.K₀ p) : K)).coprime
  have hsep : IsSeparable l⟮(H.ρ p x : L)⟯ (H.ρ p ((1 - x : H.K₀ p) : K) : L) := by
    refine (sepEquiv_of_hgt_eq p hB ⟨H.transcendental_ρ p h1xk, H.transcendental_ρ p hxk, ?_⟩
      ?_).1
    · rw [← pointV_eq_point_ρ, ← pointV_eq_point_ρ, Subfield.coe_sub, Subfield.coe_one,
        H.pointV_ψK_one_sub hxk]
    · exact (H.hgtV_of_primitive p h1x).trans (H.hgtV_of_primitive p hx).symm
  -- `dlog b = (M κ / N) • dlog a`
  have hM0 : (M : H.F p) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff (H.F p) p]
    exact fun hpM ↦ (Fact.out : p.Prime).one_lt.ne' (hM.symm.eq_one_of_dvd hpM)
  have hrel : modelDLog l (H.B p) (H.ρ p ((1 - x : H.K₀ p) : K)) =
      algebraMap l (H.F p) (M * κ * (N : l)⁻¹) • modelDLog l (H.B p) (H.ρ p x) := by
    have e := (H.data p).Δ_one_sub hx
    rw [H.Δ_eq_of_primitive p hx, H.Δ_eq_of_primitive p h1x, ← hNdef, ← hMdef] at e
    have := congrArg ((M : H.F p) • ·) e
    simp only [smul_smul, mul_inv_cancel₀ hM0, one_smul] at this
    rw [this]
    congr 1
    apply Subtype.ext
    push_cast [hκ, map_inv₀, map_natCast]
    ring
  -- by the eigenvalue lemma, `μ x` is the image of an integer `n`
  obtain ⟨m, hm⟩ := exists_intCast_of_modelDLog_eq p ha hda hsep (Units.ne_zero _) hrel
  obtain ⟨n, hn⟩ := exists_intCast_of_intCast_eq p l hM hN hm
  -- so `τ x = n / (n - 1) = τ (n / (n - 1))`, and `x = n / (n - 1) ∈ k`
  have hτ : H.τ p x = H.τ p ((n : H.K₀ p) / ((n : H.K₀ p) - 1)) := by
    rw [H.τ_eq_μ_div p hx, hκ, ← hn, map_intCast, map_div₀, map_sub, map_intCast, map_one]
  apply hxk
  rw [(H.τ p).injective hτ]
  push_cast
  exact div_mem (intCast_mem _ n) (sub_mem (intCast_mem _ n) (one_mem _))

/-- **Blueprint Lemma 6.10** (`lem:tauinQ`), third part: `τ(x) ∉ l` for `x ∈ K₀ \ k` (otherwise
`μ(x) ∈ l`, hence `μ(x) ∈ F_p` by the eigenvalue lemma, so `τ(x) ∈ F_p` and `x` lies in the prime
field of `K`, which is contained in `k`). -/
theorem τ_notMem_range {x : H.K₀ p} (hx : (x : K) ∉ H.k) :
    H.τ p x ∉ (algebraMap l L).range := by
  obtain ⟨x₀, hx₀, hx₀x⟩ := H.exists_primitive_root p x hx
  generalize (hgtV p (H.B p) (H.ψK x)).toNat = j at hx₀x
  subst hx₀x
  rintro ⟨c, hc⟩
  refine H.τ_notMem_range_of_primitive p hx₀ (IsRelAlgClosed.mem_range ?_)
  refine IsAlgebraic.of_pow (pow_pos (Fact.out : p.Prime).pos j) ?_
  rw [← map_pow, ← hc]
  exact isAlgebraic_algebraMap c

theorem transcendental_τ {x : H.K₀ p} (hx : (x : K) ∉ H.k) : Transcendental l (H.τ p x) :=
  IsRelAlgClosed.transcendental (H.τ_notMem_range p hx)

/-! ### Lemma 6.11 -/

/-- `Q_{τ(x)} = Q_x` for `x ∈ K₀ \ k`. -/
theorem point_τ {x : H.K₀ p} (hx : (x : K) ∉ H.k) :
    point l (H.τ p x) = point l (H.ρ p x : L) := by
  have h := H.τ_mem_pointV p hx
  rw [H.pointV_eq_point_ρ p] at h
  exact point_eq_of_mem (H.transcendental_ρ p hx) (H.transcendental_τ p hx) h

theorem samePoint_τ_ρ {x : H.K₀ p} (hx : (x : K) ∉ H.k) :
    SamePoint l (H.τ p x) (H.ρ p x : L) :=
  ⟨H.transcendental_τ p hx, H.transcendental_ρ p hx, H.point_τ p hx⟩

/-- Transverse elements have distinct points (blueprint Section 6.3, by Lemma 6.4(b)). -/
theorem pointV_ne_of_transverse {x y : H.K₀ p} (h : (H.data p).Transverse x y) :
    pointV l (H.ψK x) ≠ pointV l (H.ψK y) := by
  intro he
  have hB := H.isTranscendenceBasis_B p
  have hx := h.Δ_ne_zero_left
  have hy := h.Δ_ne_zero_right
  have hxk := H.notMem_of_primitive p hx
  have hyk := H.notMem_of_primitive p hy
  have hω : omega l p (H.B p) (H.ρ p x) = omega l p (H.B p) (H.ρ p y) :=
    omega_eq_of_samePoint p hB ⟨H.transcendental_ρ p hxk, H.transcendental_ρ p hyk, by
      rw [← H.pointV_eq_point_ρ, ← H.pointV_eq_point_ρ, he]⟩
  apply ((H.data p).transverse_iff.1 h).2
  rw [data_Δ, data_Δ, span_dlogA_eq_omega p hB (H.hgtV_of_primitive p hx)]
  change _ ∈ omega l p (H.B p) (H.ρ p x)
  rw [hω]
  change _ ∈ omega l p (H.B p) (vRep p (H.ψK y) : L)
  rw [← span_dlogA_eq_omega p hB (H.hgtV_of_primitive p hy)]
  exact Submodule.mem_span_singleton_self _

/-- The elements `x i` of (A3) are primitive. -/
theorem Δ_x_ne_zero (i : Fin 3) : (H.data p).Δ ⟨H.x i, H.x_mem_K₀ p i⟩ ≠ 0 :=
  (H.data_Δ_ne_zero_iff p _).2 ⟨H.x_notMem i, H.hgtV_x p i⟩

/-- Blueprint, proof of Lemma 6.11: for transverse `x, y`, the heights of `τ(x)` and `τ(y)`
agree (`(a, b, a b)` and `(τ x, τ y, τ x τ y)` are normalized triples of
`(Q_x, Q_y, Q_{xy})`; Lemma 3.5(b)). -/
theorem hgt_τ_eq_of_transverse {x y : H.K₀ p} (h : (H.data p).Transverse x y) :
    hgt l p (H.B p) (H.τ p x) = hgt l p (H.B p) (H.τ p y) := by
  have hB := H.isTranscendenceBasis_B p
  have hx := h.Δ_ne_zero_left
  have hy := h.Δ_ne_zero_right
  have hxk := H.notMem_of_primitive p hx
  have hyk := H.notMem_of_primitive p hy
  have hxyk : ((x * y : H.K₀ p) : K) ∉ H.k := H.notMem_of_primitive p h.Δ_mul_ne_zero
  have hx0 : (x : K) ≠ 0 := H.ne_zero_of_notMem hxk
  have hy0 : (y : K) ≠ 0 := H.ne_zero_of_notMem hyk
  set N := vRepNat p (H.ψK x)
  set M := vRepNat p (H.ψK y)
  have hN := (H.isVRep_ρ p x).coprime
  have hM := (H.isVRep_ρ p y).coprime
  set a := (H.ρ p x : L)
  set b := (H.ρ p y : L)
  have ha := H.transcendental_ρ p hxk
  have hb := H.transcendental_ρ p hyk
  -- `a ^ M ≈ a` and `b ^ N ≈ b`
  have hNpos := (H.isVRep_ρ p x).pos
  have hMpos := (H.isVRep_ρ p y).pos
  have haM' : SepEquiv l (a ^ M) a := sepEquiv_pow (natCast_ne_zero_of_coprime p L hM) a
  have hbN' : SepEquiv l (b ^ N) b := sepEquiv_pow (natCast_ne_zero_of_coprime p L hN) b
  have haM : SamePoint l (a ^ M) a := haM'.samePoint (ha.pow hMpos)
  have hbN : SamePoint l (b ^ N) b := hbN'.samePoint (hb.pow hNpos)
  have hgta : hgt l p (H.B p) (a ^ M) = 0 := by
    rw [hgt_eq_of_sepEquiv p haM']
    exact H.hgtV_of_primitive p hx
  have hgtb : hgt l p (H.B p) (b ^ N) = 0 := by
    rw [hgt_eq_of_sepEquiv p hbN']
    exact H.hgtV_of_primitive p hy
  -- `Q_x ≠ Q_y`, so `(a^M, b^N)` and `(τ x, τ y)` are algebraically independent
  have hpne : point l a ≠ point l b := by
    rw [← H.pointV_eq_point_ρ, ← H.pointV_eq_point_ρ]
    exact H.pointV_ne_of_transverse p h
  have hindab : AlgebraicIndependent l ![a ^ M, b ^ N] := by
    refine not_not.1 fun hdep ↦ hpne ?_
    rw [← haM.point_eq, ← hbN.point_eq]
    exact (point_eq_point_iff_not_algebraicIndependent (ha.pow hMpos) (hb.pow hNpos)).2 hdep
  have hindτ : AlgebraicIndependent l ![H.τ p x, H.τ p y] := by
    refine not_not.1 fun hdep ↦ hpne ?_
    rw [← H.point_τ p hxk, ← H.point_τ p hyk]
    exact (point_eq_point_iff_not_algebraicIndependent (H.transcendental_τ p hxk)
      (H.transcendental_τ p hyk)).2 hdep
  have hN₁ := isNormalized_mul hindτ
  have hN₂ := isNormalized_mul hindab
  -- `(N M, a^M b^N)` is a representative of `ψ(x y)`
  have hpt : pointV l (H.ψK ((x * y : H.K₀ p) : K)) = point l (a ^ M * b ^ N) := by
    have := pointV_eq_point (l := l) (v := H.ψK ((x * y : H.K₀ p) : K)) (N := N * M)
      (a := H.ρ p x ^ M * H.ρ p y ^ N) (Nat.mul_pos hNpos hMpos) (by
        rw [Subfield.coe_mul, H.ψK_mul hx0 hy0, cls_mul, cls_pow, cls_pow,
          ← (H.isVRep_ρ p x).nsmul_eq, ← (H.isVRep_ρ p y).nsmul_eq, smul_add, smul_smul,
          smul_smul, mul_comm M N])
    rw [this, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
  have hz : SamePoint l (H.τ p x * H.τ p y) (a ^ M * b ^ N) := by
    rw [← map_mul]
    refine ⟨H.transcendental_τ p hxyk, hN₂.transcendental₃, ?_⟩
    refine point_eq_of_mem hN₂.transcendental₃ (H.transcendental_τ p hxyk) ?_
    rw [← hpt]
    exact H.τ_mem_pointV p hxyk
  have hxa : SamePoint l (H.τ p x) (a ^ M) := (H.samePoint_τ_ρ p hxk).trans haM.symm
  have hyb : SamePoint l (H.τ p y) (b ^ N) := (H.samePoint_τ_ρ p hyk).trans hbN.symm
  -- Lemma 3.5(b): the level shifts agree
  obtain ⟨hlev, -⟩ := (hN₂.isNormalized_iff p hxa hyb hz).1 hN₁
  have e₁ := hgt_sub_hgt p hB hxa
  have e₂ := hgt_sub_hgt p hB hyb
  rw [hgta] at e₁
  rw [hgtb] at e₂
  omega

/-- The height of `τ(x)` is the same for all primitive `x` (any two primitive elements are
transverse to a common third one). -/
theorem hgt_τ_eq_of_primitive {x y : H.K₀ p} (hx : (H.data p).Δ x ≠ 0)
    (hy : (H.data p).Δ y ≠ 0) : hgt l p (H.B p) (H.τ p x) = hgt l p (H.B p) (H.τ p y) := by
  obtain ⟨z, hxz, hyz⟩ := (H.data p).exists_transverse_transverse hx hy
  rw [H.hgt_τ_eq_of_transverse p hxz, H.hgt_τ_eq_of_transverse p hyz]

theorem frobZ_τ_ne_zero {x : H.K₀ p} (hx : (x : K) ∉ H.k) (j : ℤ) :
    frobZ L p j (H.τ p x) ≠ 0 := fun h0 ↦
  (transcendental_frobZ_iff p j).2 (H.transcendental_τ p hx) (h0 ▸ isAlgebraic_zero)

/-- `σ_x = Frob^{-ht τ(x)}(τ x)` is a model generator. -/
theorem frobZ_τ_mem_F {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) {e₀ : ℤ}
    (he : hgt l p (H.B p) (H.τ p x) = e₀) :
    frobZ L p (-e₀) (H.τ p x) ∈ H.F p ∧ modelD l (H.B p) (frobZ L p (-e₀) (H.τ p x)) ≠ 0 := by
  have hB := H.isTranscendenceBasis_B p
  have htr := H.transcendental_τ p (H.notMem_of_primitive p hx)
  subst he
  exact (hgt_eq_zero_iff p hB ((transcendental_frobZ_iff p _).2 htr)).1
    (hgt_frobZ_neg_hgt p hB htr)

/-- Blueprint, proof of Lemma 6.11: for primitive `x`, `Δ(x)` and `dlog σ_x` span the line
`ω_A(Q_x)`, where `σ_x = Frob^{-ht τ(x)}(τ x)` is a model generator of `Q_x`. -/
theorem exists_Δ_eq_smul_modelDLog_frobZ {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) :
    ∃ θ : H.F p, (H.data p).Δ x =
      θ • modelDLog l (H.B p) (frobZ L p (-hgt l p (H.B p) (H.τ p x)) (H.τ p x)) := by
  have hB := H.isTranscendenceBasis_B p
  have hxk := H.notMem_of_primitive p hx
  set σ := frobZ L p (-hgt l p (H.B p) (H.τ p x)) (H.τ p x)
  have hσtr : Transcendental l σ := (transcendental_frobZ_iff p _).2 (H.transcendental_τ p hxk)
  have hσ0 : hgt l p (H.B p) σ = 0 := hgt_frobZ_neg_hgt p hB (H.transcendental_τ p hxk)
  obtain ⟨hσF, -⟩ := H.frobZ_τ_mem_F p hx rfl
  have hspan : (H.F p) ∙ (H.data p).Δ x = (H.F p) ∙ modelD l (H.B p) σ := by
    rw [data_Δ, span_dlogA_eq_omega p hB (H.hgtV_of_primitive p hx),
      ← omega_eq_span_of_hgt_eq_zero p hσ0]
    refine omega_eq_of_samePoint p hB ⟨H.transcendental_ρ p hxk, hσtr, ?_⟩
    rw [point_frobZ, H.point_τ p hxk]
    rfl
  have hmem : (H.data p).Δ x ∈ (H.F p) ∙ modelD l (H.B p) σ := by
    rw [← hspan]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  refine ⟨c * ⟨σ, hσF⟩, ?_⟩
  rw [← hc, mul_smul, smul_modelDLog hσF (H.frobZ_τ_ne_zero p hxk _)]

/-- Blueprint, proof of Lemma 6.11: the height `e(x)` of `τ(x)` is a constant `e₀` on primitive
elements, and with `σ_x = Frob^{-e₀}(τ x)` (a model generator of `Q_x`) there is a constant
`θ ∈ Fˣ` with `Δ(x) = θ • dlog σ_x` for all primitive `x`. -/
theorem exists_hgt_τ_coeff : ∃ (e₀ : ℤ) (θ : H.F p), θ ≠ 0 ∧ ∀ x : H.K₀ p,
    (H.data p).Δ x ≠ 0 → hgt l p (H.B p) (H.τ p x) = e₀ ∧
      (H.data p).Δ x = θ • modelDLog l (H.B p) (frobZ L p (-e₀) (H.τ p x)) := by
  set x₀ : H.K₀ p := ⟨H.x 0, H.x_mem_K₀ p 0⟩
  have hx₀ : (H.data p).Δ x₀ ≠ 0 := H.Δ_x_ne_zero p 0
  set e₀ := hgt l p (H.B p) (H.τ p x₀)
  have he : ∀ x, (H.data p).Δ x ≠ 0 → hgt l p (H.B p) (H.τ p x) = e₀ := fun x hx ↦
    H.hgt_τ_eq_of_primitive p hx hx₀
  have hcoef : ∀ x, (H.data p).Δ x ≠ 0 → ∃ θ : H.F p,
      (H.data p).Δ x = θ • modelDLog l (H.B p) (frobZ L p (-e₀) (H.τ p x)) := fun x hx ↦ by
    have := H.exists_Δ_eq_smul_modelDLog_frobZ p hx
    rwa [he x hx] at this
  -- the coefficients of transverse elements agree
  have htr : ∀ x y, (H.data p).Transverse x y → ∀ θ θ' : H.F p,
      (H.data p).Δ x = θ • modelDLog l (H.B p) (frobZ L p (-e₀) (H.τ p x)) →
      (H.data p).Δ y = θ' • modelDLog l (H.B p) (frobZ L p (-e₀) (H.τ p y)) → θ = θ' := by
    intro x y h θ θ' hθ hθ'
    obtain ⟨θ'', hθ''⟩ := hcoef (x * y) h.Δ_mul_ne_zero
    obtain ⟨hσx, -⟩ := H.frobZ_τ_mem_F p h.Δ_ne_zero_left (he x h.Δ_ne_zero_left)
    obtain ⟨hσy, -⟩ := H.frobZ_τ_mem_F p h.Δ_ne_zero_right (he y h.Δ_ne_zero_right)
    have hσx0 := H.frobZ_τ_ne_zero p (H.notMem_of_primitive p h.Δ_ne_zero_left) (-e₀)
    have hσy0 := H.frobZ_τ_ne_zero p (H.notMem_of_primitive p h.Δ_ne_zero_right) (-e₀)
    rw [map_mul, map_mul, modelDLog_mul hσx hσy hσx0 hσy0, h.Δ_mul, hθ, hθ'] at hθ''
    have hli := h.linearIndependent_of_eq_smul hθ hθ'
    obtain ⟨h₁, h₂⟩ := eq_of_linearIndependent_pair hli hθ''.symm
    exact h₁.symm.trans h₂
  obtain ⟨θ, hθ⟩ := hcoef x₀ hx₀
  refine ⟨e₀, θ, ?_, fun x hx ↦ ⟨he x hx, ?_⟩⟩
  · rintro rfl
    rw [zero_smul] at hθ
    exact hx₀ hθ
  · obtain ⟨θx, hθx⟩ := hcoef x hx
    obtain ⟨z, hxz, hx₀z⟩ := (H.data p).exists_transverse_transverse hx hx₀
    obtain ⟨θz, hθz⟩ := hcoef z hxz.Δ_ne_zero_right
    rw [hθx, htr x z hxz θx θz hθx hθz, ← htr x₀ z hx₀z θ θz hθ hθz]

/-- Blueprint, end of the proof of Lemma 6.11: `e₀ = 0`, i.e. `τ(x)` is a model generator of
`Q_x` for primitive `x` (`σ_{1-x} = 1 - σ_x` gives `μ(x) = σ_x/(σ_x - 1)`, so `τ(x) = σ_x`). -/
theorem hgt_τ_eq_zero {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) :
    hgt l p (H.B p) (H.τ p x) = 0 := by
  have hB := H.isTranscendenceBasis_B p
  have hxk := H.notMem_of_primitive p hx
  obtain ⟨e₀, θ, -, h⟩ := H.exists_hgt_τ_coeff p
  obtain ⟨he, hΔ⟩ := h x hx
  have h1x := (H.data p).Δ_one_sub_ne_zero hx
  obtain ⟨-, hΔ1⟩ := h (1 - x) h1x
  set σ := frobZ L p (-e₀) (H.τ p x) with hσdef
  obtain ⟨hσF, -⟩ := H.frobZ_τ_mem_F p hx he
  have hσtr : Transcendental l σ := (transcendental_frobZ_iff p _).2 (H.transcendental_τ p hxk)
  have hσ0 : σ ≠ 0 := fun h0 ↦ hσtr (h0 ▸ isAlgebraic_zero)
  have hσ1 : 1 - σ ≠ 0 := fun h0 ↦ hσtr (by
    rw [show σ = 1 by linear_combination -h0]
    exact isAlgebraic_one)
  -- `σ_{1-x} = 1 - σ_x`
  have e1 : frobZ L p (-e₀) (H.τ p (1 - x)) = 1 - σ := by
    rw [map_sub, map_one, map_sub, map_one]
  rw [e1, modelDLog_one_sub hσF hσ0 hσ1, smul_comm, ← hΔ] at hΔ1
  -- so `μ(x) = σ/(σ - 1)` and `τ(x) = σ`
  have hμ := (H.data p).μ_eq_of_Δ_one_sub hx hΔ1
  have hτσ : H.τ p x = σ := by
    rw [τ_apply, (H.data p).τ_eq_μ_div hx, hμ, neg_div_one_sub_div]
    exact fun h0 ↦ hσ1 (by simpa using congrArg Subtype.val h0)
  have := hgt_frobZ p hB (H.transcendental_τ p hxk) (-e₀)
  rw [← hσdef, ← hτσ, he] at this
  rw [he]
  omega

/-- For primitive `x`, `τ(x)` is a model generator of `Q_x` (Lemma 6.11). -/
theorem τ_mem_F_of_primitive {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) :
    H.τ p x ∈ H.F p ∧ modelD l (H.B p) (H.τ p x) ≠ 0 :=
  (hgt_eq_zero_iff p (H.isTranscendenceBasis_B p)
    (H.transcendental_τ p (H.notMem_of_primitive p hx))).1 (H.hgt_τ_eq_zero p hx)

theorem modelDLog_τ_ne_zero {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) :
    modelDLog l (H.B p) (H.τ p x) ≠ 0 := by
  rw [Ne, modelDLog_eq_zero_iff (H.τ_mem_F_of_primitive p hx).1
    (H.τ_ne_zero p ((H.data p).ne_zero_of_Δ_ne_zero hx))]
  exact (H.τ_mem_F_of_primitive p hx).2

/-- Blueprint, proof of `eq:lift`: for primitive `x` and `v ∈ W ∩ G_{Q_x}`, `v ≠ 0`, a
representative `(N, a)` of `v` has `a ∈ Q_x ∩ F`, so `a` is separable over `l(τ(x))` (`τ(x)` is a
model generator of `Q_x`, Lemma 4.3). -/
theorem exists_rep_of_mem_pointGroup {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) {v : V l L}
    (hvW : v ∈ W l p (H.B p)) (hvG : v ∈ pointGroup (pointV l (H.ψK x))) (hv0 : v ≠ 0) :
    ∃ (N : ℕ) (a : Lˣ), IsVRep p v N a ∧ (a : L) ∈ H.F p ∧ SamePoint l (a : L) (H.τ p x) ∧
      IsSeparable l⟮H.τ p x⟯ (a : L) := by
  have hB := H.isTranscendenceBasis_B p
  have hxk := H.notMem_of_primitive p hx
  have hrep := isVRep_vRep p v
  have ha : (vRep p v : L) ∈ H.F p := vRep_mem_model p hvW
  have hatr : Transcendental l (vRep p v : L) := hrep.transcendental p hv0
  have hpt : pointV l v = pointV l (H.ψK x) :=
    ((mem_pointGroup_pointV_iff (H.ψK_ne_zero hxk)).1 hvG).resolve_left hv0
  have hsp : SamePoint l (vRep p v : L) (H.τ p x) := ⟨hatr, H.transcendental_τ p hxk, by
    rw [← hrep.pointV_eq, hpt, H.pointV_eq_point_ρ, H.point_τ p hxk]⟩
  refine ⟨_, _, hrep, ha, hsp, isSeparable_of_hgt_le p hB hsp ?_⟩
  rw [H.hgt_τ_eq_zero p hx]
  exact (mem_model_iff_hgt_nonneg p hB hatr).1 ha

/-- Blueprint, proofs of Lemma 6.11 and of `eq:lift`: for primitive `x` and `v ∈ W ∩ G_{Q_x}`,
`dlog_A(v) = c • dlog τ(x)` for some `c ∈ F ∩ Q_x`. (A representative `(N, a)` of `v ≠ 0` has
`a ∈ Q_x ∩ F`, hence is separable over `l(τ(x))` since `τ(x)` is a model generator, and
`d a ∈ F_{τ(x)} · d τ(x)` with `F_{τ(x)} ⊆ Q_x` the field of elements separable over `l(τ(x))`.) -/
theorem exists_dlogA_eq_smul {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) {v : V l L}
    (hvW : v ∈ W l p (H.B p)) (hvG : v ∈ pointGroup (pointV l (H.ψK x))) :
    ∃ c : H.F p, (c : L) ∈ pointV l (H.ψK x) ∧
      dlogA p (H.B p) v = c • modelDLog l (H.B p) (H.τ p x) := by
  have hxk := H.notMem_of_primitive p hx
  obtain ⟨hτF, -⟩ := H.τ_mem_F_of_primitive p hx
  rcases eq_or_ne v 0 with rfl | hv0
  · exact ⟨0, zero_mem _, by rw [dlogA_zero, zero_smul]⟩
  obtain ⟨N, a, hrep, ha, hsp, hsep⟩ := H.exists_rep_of_mem_pointGroup p hx hvW hvG hv0
  obtain ⟨c', hc'F, hc'mem, hdc⟩ := exists_modelD_eq_smul_of_isSeparable hsep hτF
  refine ⟨(N : H.F p)⁻¹ * (⟨a, ha⟩ : H.F p)⁻¹ * ⟨c', hc'F⟩ * ⟨H.τ p x, hτF⟩, ?_, ?_⟩
  · rw [H.pointV_eq_point_ρ, ← H.point_τ p hxk]
    push_cast
    exact mul_mem (mul_mem (mul_mem (inv_mem (_root_.natCast_mem _ N)) (inv_mem hsp.mem_point))
      (model_le_point _ hc'mem)) (self_mem_point _)
  · rw [dlogA_eq p hrep ha, modelDLog_of_mem ha, hdc,
      ← smul_modelDLog hτF (H.τ_ne_zero p ((H.data p).ne_zero_of_Δ_ne_zero hx))]
    simp only [smul_smul, mul_assoc]

/-- Blueprint, proofs of Lemma 6.11 and of `eq:lift` (eigenvalue step): for primitive `x` and
`v ∈ W ∩ G_{Q_x}`, if `dlog_A(v) = c • dlog τ(x)` with `c ∈ l`, then `c ∈ F_p` (Lemma 2.2). -/
theorem exists_intCast_of_dlogA_eq {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) {v : V l L}
    (hvW : v ∈ W l p (H.B p)) (hvG : v ∈ pointGroup (pointV l (H.ψK x))) {c : l}
    (h : dlogA p (H.B p) v = algebraMap l (H.F p) c • modelDLog l (H.B p) (H.τ p x)) :
    ∃ n : ℤ, (n : l) = c := by
  have : CharP l p := IsRelAlgClosed.charP l L p
  obtain ⟨hτF, hdτ⟩ := H.τ_mem_F_of_primitive p hx
  rcases eq_or_ne v 0 with rfl | hv0
  · refine ⟨0, ?_⟩
    rw [dlogA_zero, eq_comm, smul_eq_zero, map_eq_zero] at h
    rw [Int.cast_zero, h.resolve_right (H.modelDLog_τ_ne_zero p hx)]
  obtain ⟨N, a, hrep, ha, -, hsep⟩ := H.exists_rep_of_mem_pointGroup p hx hvW hvG hv0
  have hrel : modelDLog l (H.B p) (a : L) =
      algebraMap l (H.F p) ((N : l) * c) • modelDLog l (H.B p) (H.τ p x) := by
    rw [dlogA_eq p hrep ha] at h
    have := congrArg ((N : H.F p) • ·) h
    simp only [smul_smul, mul_inv_cancel₀ (natCast_ne_zero_of_coprime p (H.F p) hrep.coprime),
      one_smul] at this
    rw [this, map_mul, map_natCast]
  obtain ⟨m, hm⟩ := exists_intCast_of_modelDLog_eq p hτF hdτ hsep (Units.ne_zero _) hrel
  exact exists_intCast_of_intCast_eq p l (M := N) (N := 1) hrep.coprime
    (Nat.coprime_one_left p) (by rw [hm, Nat.cast_one, inv_one, mul_one])

/-- **Blueprint Lemma 6.11** (`lem:theta`): there is `θ ∈ F_pˣ` (an integer prime to `p`) such
that for every primitive `x`, `d τ(x) ≠ 0` and `Δ(x) = θ • dlog τ(x)`. -/
theorem exists_θ : ∃ θ : ℤ, (θ : L) ≠ 0 ∧ ∀ x : H.K₀ p, (H.data p).Δ x ≠ 0 →
    modelD l (H.B p) (H.τ p x) ≠ 0 ∧
      (H.data p).Δ x = (θ : H.F p) • modelDLog l (H.B p) (H.τ p x) := by
  have hB := H.isTranscendenceBasis_B p
  have : CharP l p := IsRelAlgClosed.charP l L p
  obtain ⟨e₀, θ, hθ0, h⟩ := H.exists_hgt_τ_coeff p
  have hx₀ := H.Δ_x_ne_zero p 0
  have he₀ : e₀ = 0 := (h _ hx₀).1.symm.trans (H.hgt_τ_eq_zero p hx₀)
  subst he₀
  simp only [neg_zero, frobZ_zero_apply] at h
  -- `θ ∈ Q_x` for primitive `x`
  have hθQ : ∀ x, (H.data p).Δ x ≠ 0 → (θ : L) ∈ pointV l (H.ψK x) := fun x hx ↦ by
    obtain ⟨c, hcQ, hc⟩ := H.exists_dlogA_eq_smul p hx x.2 (mem_pointGroup_pointV _)
    rw [← data_Δ, (h x hx).2] at hc
    have hθc : θ = c := smul_left_injective (H.F p) (H.modelDLog_τ_ne_zero p hx) hc
    rw [hθc]
    exact hcQ
  -- so `θ ∈ Q_{x 0} ∩ Q_{x 1} = l`
  obtain ⟨θ₀, hθ₀⟩ := H.mem_range_of_mem_pointV_x (hθQ ⟨H.x 0, H.x_mem_K₀ p 0⟩ hx₀)
    (hθQ ⟨H.x 1, H.x_mem_K₀ p 1⟩ (H.Δ_x_ne_zero p 1))
  have hθθ₀ : θ = algebraMap l (H.F p) θ₀ :=
    Subtype.ext (by rw [IntermediateField.coe_algebraMap_apply, hθ₀])
  -- and `θ ∈ F_p`, by the eigenvalue lemma for `τ(x 0)` and the representative of `ψ(x 0)`
  generalize (⟨H.x 0, H.x_mem_K₀ p 0⟩ : H.K₀ p) = x₀ at hx₀
  obtain ⟨n, hn⟩ := H.exists_intCast_of_dlogA_eq p hx₀ x₀.2
    (mem_pointGroup_pointV _) (c := θ₀) (by rw [← data_Δ, (h _ hx₀).2, hθθ₀])
  have hnθ : (n : H.F p) = θ := by rw [hθθ₀, ← hn, map_intCast]
  refine ⟨n, fun h0 ↦ hθ0 ?_, fun x hx ↦ ⟨(H.τ_mem_F_of_primitive p hx).2, ?_⟩⟩
  · rw [← hnθ]
    exact Subtype.ext (by push_cast; exact h0)
  · rw [hnθ]
    exact (h x hx).2

/-! ### Proposition 6.12 -/

/-- `ψ` on `K₀ˣ`. -/
noncomputable def ψ₀ : Additive (H.K₀ p)ˣ →+ V l L :=
  H.ψ.comp (MonoidHom.toAdditive (Units.map ((H.K₀ p).subtype : H.K₀ p →* K)))

theorem ψ₀_apply (x : (H.K₀ p)ˣ) : H.ψ₀ p (.ofMul x) = H.ψK ((x : H.K₀ p) : K) :=
  H.ψ_units_map_subtype p x

/-- `x ↦ [τ(x)]` on `K₀ˣ`. -/
noncomputable def τV : Additive (H.K₀ p)ˣ →+ V l L :=
  (cls (constUnits l L)).comp (MonoidHom.toAdditive (Units.map (H.τ p : H.K₀ p →* L)))

theorem τV_apply (x : (H.K₀ p)ˣ) :
    H.τV p (.ofMul x) = cls (constUnits l L) (.ofMul (Units.map (H.τ p : H.K₀ p →* L) x)) :=
  rfl

/-- `[τ(x)] ∈ W` (`τ(x) ∈ F`). -/
theorem τV_mem_W (x : (H.K₀ p)ˣ) : H.τV p (.ofMul x) ∈ W l p (H.B p) :=
  cls_mem_W (H.τ_mem_F p x)

/-- `dlog_A [τ(x)] = dlog τ(x)` (blueprint, proof of Proposition 6.12). -/
theorem dlogA_τV (x : (H.K₀ p)ˣ) :
    dlogA p (H.B p) (H.τV p (.ofMul x)) = modelDLog l (H.B p) (H.τ p x) :=
  dlogA_cls p (H.τ_mem_F p x)

/-- Blueprint `eq:lift`: if `ψ' : K₀ˣ → W` vanishes on `kˣ` and `ψ'(x) ∈ G_{Q_x}` for
`x ∈ K₀ \ k`, then there is an integer `m` with `ψ' - m [τ] ∈ p W` on `K₀ˣ`. -/
theorem exists_lift (ψ' : Additive (H.K₀ p)ˣ →+ V l L) (hW : ∀ x, ψ' x ∈ W l p (H.B p))
    (hk : ∀ x : (H.K₀ p)ˣ, ((x : H.K₀ p) : K) ∈ H.k → ψ' (.ofMul x) = 0)
    (hG : ∀ x : (H.K₀ p)ˣ, ((x : H.K₀ p) : K) ∉ H.k →
      ψ' (.ofMul x) ∈ pointGroup (pointV l (H.ψK ((x : H.K₀ p) : K)))) :
    ∃ m : ℤ, ∀ x : (H.K₀ p)ˣ, ∃ w ∈ W l p (H.B p),
      ψ' (.ofMul x) - m • H.τV p (.ofMul x) = p • w := by
  have hB := H.isTranscendenceBasis_B p
  obtain ⟨θ, -, hθ⟩ := H.exists_θ p
  -- for primitive `x`, `dlog_A ψ'(x) = c • dlog τ(x)` with `c ∈ Q_x`
  have hc : ∀ x : (H.K₀ p)ˣ, (H.data p).Δ x ≠ 0 → ∃ c : H.F p,
      (c : L) ∈ pointV l (H.ψK ((x : H.K₀ p) : K)) ∧
        dlogA p (H.B p) (ψ' (.ofMul x)) = c • modelDLog l (H.B p) (H.τ p x) := fun x hx ↦
    H.exists_dlogA_eq_smul p hx (hW _) (hG x (H.notMem_of_primitive p hx))
  -- the coefficients of transverse elements agree
  have htr : ∀ x y : (H.K₀ p)ˣ, (H.data p).Transverse x y → ∀ c c' : H.F p,
      dlogA p (H.B p) (ψ' (.ofMul x)) = c • modelDLog l (H.B p) (H.τ p x) →
      dlogA p (H.B p) (ψ' (.ofMul y)) = c' • modelDLog l (H.B p) (H.τ p y) → c = c' := by
    intro x y h c c' hcx hcy
    have hx := h.Δ_ne_zero_left
    have hy := h.Δ_ne_zero_right
    have hxy : (H.data p).Δ ((x * y : (H.K₀ p)ˣ) : H.K₀ p) ≠ 0 := by
      rw [Units.val_mul]
      exact h.Δ_mul_ne_zero
    obtain ⟨c'', -, hc''⟩ := hc (x * y) hxy
    rw [ofMul_mul, map_add, dlogA_add p (hW _) (hW _), hcx, hcy, Units.val_mul, map_mul,
      modelDLog_mul (H.τ_mem_F p x) (H.τ_mem_F p y)
        (H.τ_ne_zero p ((H.data p).ne_zero_of_Δ_ne_zero hx))
        (H.τ_ne_zero p ((H.data p).ne_zero_of_Δ_ne_zero hy))] at hc''
    have hli := h.linearIndependent_of_eq_smul (hθ x hx).2 (hθ y hy).2
    obtain ⟨h₁, h₂⟩ := eq_of_linearIndependent_pair hli hc''.symm
    exact h₁.symm.trans h₂
  -- so all primitive elements have the same coefficient `c₀`
  have hu₀ : (H.data p).Δ ((H.xK₀ p 0 : (H.K₀ p)ˣ) : H.K₀ p) ≠ 0 := H.Δ_x_ne_zero p 0
  have hu₁ : (H.data p).Δ ((H.xK₀ p 1 : (H.K₀ p)ˣ) : H.K₀ p) ≠ 0 := H.Δ_x_ne_zero p 1
  obtain ⟨c₀, hc₀Q, hc₀⟩ := hc _ hu₀
  have hall : ∀ x : (H.K₀ p)ˣ, (H.data p).Δ x ≠ 0 →
      dlogA p (H.B p) (ψ' (.ofMul x)) = c₀ • modelDLog l (H.B p) (H.τ p x) := by
    intro x hx
    obtain ⟨c, -, hcx⟩ := hc x hx
    obtain ⟨z, hxz, hx₀z⟩ := (H.data p).exists_transverse_transverse hx hu₀
    have hu : (Units.mk0 z ((H.data p).ne_zero_of_Δ_ne_zero hxz.Δ_ne_zero_right) : H.K₀ p) = z :=
      Units.val_mk0 _
    rw [← hu] at hxz hx₀z
    obtain ⟨cz, -, hcz⟩ := hc _ hxz.Δ_ne_zero_right
    rw [hcx, htr _ _ hxz c cz hcx hcz, ← htr _ _ hx₀z c₀ cz hc₀ hcz]
  -- `c₀ ∈ Q_{x 0} ∩ Q_{x 1} = l`
  have hc₁Q : (c₀ : L) ∈ pointV l (H.ψK (H.x 1)) := by
    obtain ⟨c₁, hc₁Q, hc₁⟩ := hc _ hu₁
    rw [smul_left_injective (H.F p) (H.modelDLog_τ_ne_zero p hu₁)
      ((hall _ hu₁).symm.trans hc₁)]
    exact hc₁Q
  obtain ⟨c, hc⟩ := H.mem_range_of_mem_pointV_x hc₀Q hc₁Q
  have hcc : c₀ = algebraMap l (H.F p) c :=
    Subtype.ext (by rw [IntermediateField.coe_algebraMap_apply, hc])
  -- `c ∈ F_p` by the eigenvalue lemma
  obtain ⟨m, hm⟩ := H.exists_intCast_of_dlogA_eq p hu₀ (hW (.ofMul (H.xK₀ p 0)))
    (hG (H.xK₀ p 0) (H.x_notMem 0)) (c := c) (by rw [← hcc]; exact hc₀)
  have hmF : (m : H.F p) = c₀ := by rw [hcc, ← hm, map_intCast]
  -- `ψ' - m [τ] ∈ p W`: for primitive `x` since `dlog_A` vanishes, in general by `eq:roots`
  have hprim : ∀ x : (H.K₀ p)ˣ, (H.data p).Δ x ≠ 0 → ∃ w ∈ W l p (H.B p),
      ψ' (.ofMul x) - m • H.τV p (.ofMul x) = p • w := by
    intro x hx
    have hmW := zsmul_mem (H.τV_mem_W p x) m
    obtain ⟨w, hw, he⟩ := (dlogA_eq_zero_iff p hB (sub_mem (hW _) hmW)).1 (by
      rw [dlogA_sub p (hW _) hmW, dlogA_zsmul p (H.τV_mem_W p x), dlogA_τV, hall x hx, ← hmF,
        Int.cast_smul_eq_zsmul, sub_self])
    exact ⟨w, hw, he⟩
  refine ⟨m, fun x ↦ ?_⟩
  by_cases hxk : ((x : H.K₀ p) : K) ∈ H.k
  · refine ⟨0, zero_mem _, ?_⟩
    rw [hk x hxk, τV_apply, cls_eq_zero_of_mem (mem_constUnits.2 ?_), smul_zero, sub_zero,
      smul_zero]
    rw [Units.coe_map]
    exact H.τ_mem_range_of_mem p hxk
  · obtain ⟨x₀, hx₀, hx₀x⟩ := H.exists_primitive_root p x hxk
    generalize (hgtV p (H.B p) (H.ψK ((x : H.K₀ p) : K))).toNat = j at hx₀x
    have hxu : x = Units.mk0 x₀ ((H.data p).ne_zero_of_Δ_ne_zero hx₀) ^ p ^ j :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hx₀x])
    obtain ⟨w, hw, hwe⟩ := hprim (Units.mk0 x₀ ((H.data p).ne_zero_of_Δ_ne_zero hx₀))
      (by rwa [Units.val_mk0])
    refine ⟨p ^ j • w, nsmul_mem hw _, ?_⟩
    rw [hxu, ofMul_pow, map_nsmul, map_nsmul, smul_comm m, ← smul_sub, hwe, smul_comm]

/-- Blueprint `eq:padic`: for every `j` there is an integer `r_j` with
`ψ - r_j [τ] ∈ p^j W` on `K₀ˣ` (by induction on `j`, applying `eq:lift` to
`ψ_j = p^{-j}(ψ - r_j [τ])`). -/
theorem exists_padic (j : ℕ) : ∃ r : ℤ, ∀ x : (H.K₀ p)ˣ, ∃ w ∈ W l p (H.B p),
    H.ψ₀ p (.ofMul x) - r • H.τV p (.ofMul x) = p ^ j • w := by
  have hp0 : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  induction j with
  | zero =>
    refine ⟨0, fun x ↦ ⟨H.ψ₀ p (.ofMul x), ?_, by rw [zero_smul, sub_zero, pow_zero, one_smul]⟩⟩
    rw [ψ₀_apply]
    exact (x : H.K₀ p).2
  | succ j ih =>
    obtain ⟨r, hr⟩ := ih
    -- `ψ_j = p^{-j} (ψ - r [τ])`
    let ψj : Additive (H.K₀ p)ˣ →+ V l L := ((p : ℚ) ^ j)⁻¹ • (H.ψ₀ p - r • H.τV p)
    have hψj : ∀ x, p ^ j • ψj x = H.ψ₀ p x - r • H.τV p x := fun x ↦ by
      rw [← Nat.cast_smul_eq_nsmul ℚ, AddMonoidHom.smul_apply, smul_smul, Nat.cast_pow,
        mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.2 hp0)), one_smul,
        AddMonoidHom.sub_apply, AddMonoidHom.smul_apply]
    have hψjW : ∀ x, ψj x ∈ W l p (H.B p) := fun x ↦ by
      obtain ⟨w, hw, he⟩ := hr (Additive.toMul x)
      rwa [nsmul_left_cancel (pow_ne_zero j hp0) ((hψj x).trans he)]
    have hk : ∀ x : (H.K₀ p)ˣ, ((x : H.K₀ p) : K) ∈ H.k → ψj (.ofMul x) = 0 := fun x hx ↦ by
      refine nsmul_left_cancel (pow_ne_zero j hp0) ?_
      rw [hψj, smul_zero, ψ₀_apply, H.ψK_eq_zero_iff.2 hx, τV_apply,
        cls_eq_zero_of_mem (mem_constUnits.2 ?_), smul_zero, sub_zero]
      rw [Units.coe_map]
      exact H.τ_mem_range_of_mem p hx
    have hG : ∀ x : (H.K₀ p)ˣ, ((x : H.K₀ p) : K) ∉ H.k →
        ψj (.ofMul x) ∈ pointGroup (pointV l (H.ψK ((x : H.K₀ p) : K))) := fun x hx ↦ by
      have hτ : H.τV p (.ofMul x) ∈ pointGroup (pointV l (H.ψK ((x : H.K₀ p) : K))) := by
        rw [τV_apply]
        exact mem_pointGroup_iff.2 ⟨1, _, one_pos, H.τ_mem_pointV p hx, one_nsmul _⟩
      have hψ : H.ψ₀ p (.ofMul x) ∈ pointGroup (pointV l (H.ψK ((x : H.K₀ p) : K))) := by
        rw [ψ₀_apply]
        exact mem_pointGroup_pointV _
      rw [AddMonoidHom.smul_apply, AddMonoidHom.sub_apply, AddMonoidHom.smul_apply]
      exact Submodule.smul_mem _ _ (sub_mem hψ (Submodule.smul_of_tower_mem _ r hτ))
    obtain ⟨m, hm⟩ := H.exists_lift p ψj hψjW hk hG
    refine ⟨r + p ^ j * m, fun x ↦ ?_⟩
    obtain ⟨w, hw, he⟩ := hm x
    refine ⟨w, hw, ?_⟩
    calc H.ψ₀ p (.ofMul x) - (r + p ^ j * m) • H.τV p (.ofMul x)
        = (H.ψ₀ p (.ofMul x) - r • H.τV p (.ofMul x)) - p ^ j • (m • H.τV p (.ofMul x)) := by
          rw [add_smul, mul_smul, ← sub_sub, ← Nat.cast_pow, natCast_zsmul]
      _ = p ^ j • (ψj (.ofMul x) - m • H.τV p (.ofMul x)) := by rw [smul_sub, hψj]
      _ = p ^ (j + 1) • w := by rw [he, smul_smul, ← pow_succ]

/-- Blueprint, end of the proof of Proposition 6.12: if `ψ - r_j [τ] ∈ p^j W` for all `j` and
`n' r_j ≡ m' (mod p^{j-β})` for `j ≥ β`, then `n' ψ = m' [τ]` on `K₀ˣ` (as
`n' ψ - m' [τ] ∈ ⋂_j p^j W = 0`). -/
theorem zsmul_ψ₀_eq_of_dvd {r : ℕ → ℤ}
    (hr : ∀ (j : ℕ) (x : (H.K₀ p)ˣ), ∃ w ∈ W l p (H.B p),
      H.ψ₀ p (.ofMul x) - r j • H.τV p (.ofMul x) = p ^ j • w)
    {n' : ℕ} {m' : ℤ} {β : ℕ} (h : ∀ j : ℕ, β ≤ j → (p : ℤ) ^ (j - β) ∣ n' * r j - m')
    (x : (H.K₀ p)ˣ) : (n' : ℤ) • H.ψ₀ p (.ofMul x) = m' • H.τV p (.ofMul x) := by
  rw [← sub_eq_zero]
  refine eq_zero_of_forall_mem_pow_nsmul_W p (H.isTranscendenceBasis_B p) fun i ↦ ?_
  obtain ⟨w, hw, he⟩ := hr (i + β) x
  obtain ⟨c, hc⟩ := h (i + β) (Nat.le_add_left β i)
  rw [Nat.add_sub_cancel] at hc
  refine ⟨(n' * p ^ β) • w + c • H.τV p (.ofMul x),
    add_mem (nsmul_mem hw _) (zsmul_mem (H.τV_mem_W p x) c), ?_⟩
  rw [sub_eq_iff_eq_add'.1 he, show m' = n' * r (i + β) - p ^ i * c by linear_combination -hc]
  module

/-- For primitive `x`, the representative `a` of `ψ(x)` is separable over `l(τ(x))` (both are
model generators of `Q_x`). -/
theorem isSeparable_ρ_of_primitive {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) :
    IsSeparable l⟮H.τ p x⟯ (H.ρ p x : L) :=
  (sepEquiv_of_hgt_eq p (H.isTranscendenceBasis_B p)
    (H.samePoint_τ_ρ p (H.notMem_of_primitive p hx)) (by
      rw [H.hgt_τ_eq_zero p hx]
      exact (H.hgtV_of_primitive p hx).symm)).2

/-- Blueprint, proof of Proposition 6.12 (lines 718-725), for one `j`: let `u` be primitive,
`s = τ(u)`, `(N, a)` the representative of `ψ(u)` and `E = l(s, a)`. If
`ψ(u) - r [τ(u)] = p^j • w` with `w ∈ W`, then `(a s^{-N r})^M = c y^{p^j}` with `M` prime to
`p`, `c ∈ lˣ` and `y ∈ E` (by `eq:Epower`, as `p^j • (N • w) = [a s^{-N r}]`). -/
theorem exists_pow_eq_of_padic {u : (H.K₀ p)ˣ} (hu : (H.data p).Δ u ≠ 0) {j : ℕ} {r : ℤ}
    {w : V l L} (hw : w ∈ W l p (H.B p))
    (he : H.ψ₀ p (.ofMul u) - r • H.τV p (.ofMul u) = p ^ j • w) :
    ∃ (M : ℕ) (c : l) (y : L), M.Coprime p ∧ c ≠ 0 ∧
      y ∈ l⟮H.τ p u, (H.ρ p ((u : H.K₀ p) : K) : L)⟯ ∧
      ((H.ρ p ((u : H.K₀ p) : K) : L) *
        H.τ p u ^ (-((vRepNat p (H.ψK ((u : H.K₀ p) : K)) : ℤ) * r))) ^ M =
        algebraMap l L c * y ^ p ^ j := by
  have hrep := H.isVRep_ρ p ((u : H.K₀ p) : K)
  -- `p^j • (N • w) = [a σ^{-N r}]` with `σ = τ(u)` as a unit
  have hcls : p ^ j • (vRepNat p (H.ψK ((u : H.K₀ p) : K)) • w) =
      cls (constUnits l L) (.ofMul (H.ρ p ((u : H.K₀ p) : K) * Units.map (H.τ p : H.K₀ p →* L) u ^
        (-((vRepNat p (H.ψK ((u : H.K₀ p) : K)) : ℤ) * r)))) := by
    rw [smul_comm, ← he, smul_sub, ψ₀_apply, hrep.nsmul_eq, τV_apply, cls_mul, cls_zpow]
    module
  obtain ⟨hsF, hds⟩ := H.τ_mem_F_of_primitive p hu
  obtain ⟨haF, -⟩ := H.ρ_mem_F_of_primitive p hu
  have hsE : H.τ p u ∈ l⟮H.τ p u, (H.ρ p ((u : H.K₀ p) : K) : L)⟯ :=
    subset_adjoin _ _ (Set.mem_insert _ _)
  have haE : (H.ρ p ((u : H.K₀ p) : K) : L) ∈ l⟮H.τ p u, (H.ρ p ((u : H.K₀ p) : K) : L)⟯ :=
    subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
  have hEs : l⟮H.τ p u, (H.ρ p ((u : H.K₀ p) : K) : L)⟯ ≤ model l ![H.τ p u] := by
    rw [adjoin_le_iff]
    rintro _ (rfl | rfl)
    exacts [self_mem_model_singleton _,
      mem_model_singleton_iff.2 (H.isSeparable_ρ_of_primitive p hu)]
  have hEF : l⟮H.τ p u, (H.ρ p ((u : H.K₀ p) : K) : L)⟯ ≤ H.F p := by
    rw [adjoin_le_iff]
    rintro _ (rfl | rfl)
    exacts [hsF, haF]
  have hb : ((H.ρ p ((u : H.K₀ p) : K) * Units.map (H.τ p : H.K₀ p →* L) u ^
      (-((vRepNat p (H.ψK ((u : H.K₀ p) : K)) : ℤ) * r)) : Lˣ) : L) =
      (H.ρ p ((u : H.K₀ p) : K) : L) *
        H.τ p u ^ (-((vRepNat p (H.ψK ((u : H.K₀ p) : K)) : ℤ) * r)) := by
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, Units.coe_map]
    rfl
  rw [← hb]
  exact exists_pow_eq_mul_pow_pow p hsF hds hsE hEF (fun y hy ↦ mem_model_singleton_iff.1 (hEs hy))
    (nsmul_mem hw _) (by rw [hb]; exact mul_mem haE (zpow_mem hsE _)) hcls

/-- **Blueprint Proposition 6.12** (`prop:rational`), case `Γ = ℤ`: there is `r ∈ ℚˣ` with
`ψ(x) = r • [τ(x)]` for all `x ∈ K₀ˣ`.

Proof from the lemmas above: choose `r_j` by `exists_padic`; fix the primitive element
`x = x₀` of (A3), `s = τ(x)` (a model generator by `exists_θ`) and the representative `(N, a)` of
`ψ(x)`; `a` is separable over `l(s)` (`a ≈ s`). Let `E = l(s, a)`. For each `j`,
`p^j • (N w_j) = [a s^{-N r_j}]` with `w_j ∈ W`, so `exists_pow_eq_mul_pow_pow` applies; then
`exists_dvd_sub_of_forall_pow_eq` (with `e_j = N r_j`), `exists_dvd_sub_of_dvd` and
`zsmul_ψ₀_eq_of_dvd` give `n' ψ = m' [τ]`, and `r = m'/n' ≠ 0` as `ψ ≠ 0`. -/
theorem exists_rat_ψ₀_eq : ∃ r : ℚ, r ≠ 0 ∧ ∀ x : (H.K₀ p)ˣ,
    H.ψ₀ p (.ofMul x) = r • H.τV p (.ofMul x) := by
  choose r hr using H.exists_padic p
  -- the primitive element `u = x 0`, `s = τ(u)` and the representative `(N, a)` of `ψ(u)`
  have hu : (H.data p).Δ ((H.xK₀ p 0 : (H.K₀ p)ˣ) : H.K₀ p) ≠ 0 := H.Δ_x_ne_zero p 0
  generalize H.xK₀ p 0 = u at hu
  have huk := H.notMem_of_primitive p hu
  have hrep := H.isVRep_ρ p ((u : H.K₀ p) : K)
  -- the norm argument: `ε ≡ M N r_j (mod p^j)` for all `j`
  obtain ⟨M, ε, hM, hε⟩ := exists_dvd_sub_of_forall_pow_eq p (H.transcendental_τ p huk)
    (Units.ne_zero _) (H.isSeparable_ρ_of_primitive p hu).isIntegral.isAlgebraic
    (fun j ↦ (vRepNat p (H.ψK ((u : H.K₀ p) : K)) : ℤ) * r j) fun j ↦ by
      obtain ⟨w, hw, he⟩ := hr j u
      exact H.exists_pow_eq_of_padic p hu hw he
  obtain ⟨n', m', β, hn', hβ⟩ := exists_dvd_sub_of_dvd p (Nat.mul_pos hM hrep.pos) (r := r)
    fun j ↦ by
      rw [Nat.cast_mul, mul_assoc]
      exact hε j
  have key : ∀ x : (H.K₀ p)ˣ,
      ((n' : ℚ)) • H.ψ₀ p (.ofMul x) = (m' : ℚ) • H.τV p (.ofMul x) := fun x ↦ by
    have := H.zsmul_ψ₀_eq_of_dvd p hr hβ x
    rwa [← Int.cast_smul_eq_zsmul ℚ, ← Int.cast_smul_eq_zsmul ℚ, Int.cast_natCast] at this
  have hn'0 : (n' : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn'.ne'
  refine ⟨(m' : ℚ) / n', fun h0 ↦ ?_, fun x ↦ ?_⟩
  · -- `r ≠ 0` since `ψ(u) ≠ 0`
    rw [div_eq_zero_iff, or_iff_left hn'0] at h0
    have := key u
    rw [h0, zero_smul, smul_eq_zero, or_iff_right hn'0, ψ₀_apply] at this
    exact H.ψK_ne_zero huk this
  · rw [div_eq_inv_mul, mul_smul, ← key x, smul_smul, inv_mul_cancel₀ hn'0, one_smul]

end CharPHyp

end MilnorAlgDep
