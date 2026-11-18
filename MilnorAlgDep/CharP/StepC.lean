module

public import MilnorAlgDep.CharP.AdaptedModel
public import MilnorAlgDep.Standard.Eigenvalue

/-!
# Step C in characteristic `p`: identification of `ψ` on `K₀`

Blueprint Section 6.6 with `Γ = ℤ`, and equation (6.6) `eq:roots` from Section 6.5.

Throughout, `H : CharPHyp K l L` with `K`, `L` perfect, `L` of characteristic `p`, and `l`
relatively algebraically closed; `B = H.B p` is the adapted transcendence basis, `F = L_B` the
adapted model, `K₀ = H.K₀ p`, `Δ = (H.data p).Δ` and `τ = H.τ p : K₀ →+* L` the embedding of
Proposition 6.9. By Proposition 6.9 `K` has characteristic `p` (`CharPHyp.charP_K`).

## Main statements

* (6.6) `eq:roots`: `CharPHyp.pow_mem_K₀` (`Frob(K₀) ⊆ K₀`), `CharPHyp.exists_pow_pow_mem_K₀`
  (`K = ⋃ Frob^{-j}(K₀)`), `CharPHyp.exists_primitive_root` and
  `CharPHyp.hgtV_pow_pow_of_primitive` (every `x ∈ K₀ \ k` is `Frob^j(x₀)` for a unique primitive
  `x₀`, with `j = ht ψ(x)`).
* **Lemma 6.10** (`lem:tauinQ`): `CharPHyp.τ_mem_pointV`, `CharPHyp.τ_mem_range_of_mem`,
  `CharPHyp.τ_notMem_range`.
* `exists_intCast_of_modelDLog_eq`: the eigenvalue lemma (Lemma 2.2) in the form used in
  Lemmas 6.10, 6.11 and (6.7) `eq:lift`.
* **Lemma 6.11** (`lem:theta`): `CharPHyp.exists_θ`, through `CharPHyp.hgt_τ_eq_of_transverse`,
  `CharPHyp.exists_hgt_τ_coeff` (heights `e(x) = e₀` and coefficient `θ` constant) and
  `CharPHyp.hgt_τ_eq_zero` (`e₀ = 0`).
* **Proposition 6.12** (`prop:rational`), case `Γ = ℤ`: `CharPHyp.exists_rat_ψ₀_eq`, broken into
  - `CharPHyp.exists_lift`: (6.7) `eq:lift`;
  - `CharPHyp.exists_padic`: (6.8) `eq:padic`, `ψ - r_j [τ] ∈ p^j W` on `K₀ˣ`;
  - `mem_of_pow_pow_mem`: (6.9) `eq:Epower`, `E ∩ L_A^{p^j} = E^{p^j}`;
  - `exists_pow_eq_mul_pow_pow`: from `p^j • v = [b]` with `v ∈ W`, `b ∈ E` to
    `b^M = c y^{p^j}` with `y ∈ E`;
  - `exists_dvd_sub_of_forall_pow_eq`: the norm argument and unique factorization in `l[s]`
    (the `s`-adic order of `N_{E|l(s)}(a)`);
  - `exists_dvd_sub_of_dvd`: elementary arithmetic (`MN = p^β n'`, `ε = p^β m'`);
  - `CharPHyp.zsmul_ψ₀_eq_of_dvd`: the conclusion via `⋂ p^j W = 0`.

## Remark on the blueprint

In the proof of Proposition 6.12 the integers `r_j` need not be compatible (`r_{j+1} ≡ r_j`): only
(6.8) for each `j` separately is used. We therefore state (6.8) as `∀ j, ∃ r, …`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf IntermediateField KaehlerDifferential

variable {l L : Type*} [Field l] [Field L] [Algebra l L] {ι : Type*}

/-! ### Field-theoretic lemmas -/

section Fields

variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]

include p in
/-- **Blueprint Lemma 2.2** (eigenvalue lemma) in a model, in the form used in Lemmas 6.10, 6.11
and in (6.7) `eq:lift`: let `a ∈ L_B` with `d a ≠ 0` in `Ω_B`, and `b ≠ 0` separable algebraic
over `l(a)`. If `dlog b = κ • dlog a` in `Ω_B` with `κ ∈ l`, then `κ` lies in the prime field
`F_p`, i.e. is the image of an integer. (Apply Lemma 2.2 to the derivation `δ` of the field of
elements separable over `l(a)` with `d f = δ(f) • dlog a`; `Ω_{E|l} → Ω_B` is injective because
`d a ≠ 0`.) -/
theorem exists_intCast_of_modelDLog_eq {B : ι → L} {a b : L} (ha : a ∈ model l B)
    (hda : modelD l B a ≠ 0) (hb : IsSeparable l⟮a⟯ b) (hb0 : b ≠ 0) {κ : l}
    (h : modelDLog l B b = algebraMap l (model l B) κ • modelDLog l B a) :
    ∃ m : ℤ, (m : l) = κ := by
  sorry

/-- Blueprint (6.9) `eq:Epower`: let `s ∈ L_B` with `d s ≠ 0` in `Ω_B`, and let `E ∋ s` be an
intermediate field contained in `L_B` and separable algebraic over `l(s)`. If `z ∈ L_B` and
`z^{p^j} ∈ E`, then `z ∈ E`; i.e. `E ∩ L_B^{p^j} = E^{p^j}`. (Since `Ω_{E|l} → Ω_B` is injective,
`dy = 0` for `y ∈ E ∩ L_B^p`, so `y ∈ E^p` by (S3); induction on `j`.) -/
theorem mem_of_pow_pow_mem {B : ι → L} {s : L} (hs : s ∈ model l B) (hds : modelD l B s ≠ 0)
    {E : IntermediateField l L} (hsE : s ∈ E) (hE : E ≤ model l B)
    (hsep : ∀ y ∈ E, IsSeparable l⟮s⟯ y) {z : L} (hz : z ∈ model l B) {j : ℕ}
    (hzj : z ^ p ^ j ∈ E) : z ∈ E := by
  sorry

/-- Blueprint, proof of Proposition 6.12 (lines 723-725): let `E` be as in `mem_of_pow_pow_mem`.
If `v ∈ W` and `p^j • v = [b]` with `b ∈ E`, then `b^M = c • y^{p^j}` for some `M` prime to `p`,
`c ∈ lˣ` and `y ∈ E`. (If `v ≠ 0`, take a representative `(M, g)` of `v` with `g ∈ L_B`; then
`b^M = c g^{p^j}` and `g ∈ E` by (6.9). If `v = 0`, `b ∈ l`.) -/
theorem exists_pow_eq_mul_pow_pow {B : ι → L} {s : L} (hs : s ∈ model l B)
    (hds : modelD l B s ≠ 0) {E : IntermediateField l L} (hsE : s ∈ E) (hE : E ≤ model l B)
    (hsep : ∀ y ∈ E, IsSeparable l⟮s⟯ y) {v : V l L} (hv : v ∈ W l p B) {j : ℕ} {b : Lˣ}
    (hb : (b : L) ∈ E) (h : p ^ j • v = cls (constUnits l L) (.ofMul b)) :
    ∃ (M : ℕ) (c : l) (y : L), M.Coprime p ∧ c ≠ 0 ∧ y ∈ E ∧
      (b : L) ^ M = algebraMap l L c * y ^ p ^ j := by
  sorry

omit [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L] in
/-- Blueprint, proof of Proposition 6.12 (lines 726-728), the norm argument: let `s` be
transcendental over `l`, `a ≠ 0` algebraic over `l(s)`, `E = l(s, a)`, and `e j` integers such
that for every `j`, `(a s^{-e_j})^{M_j} ∈ lˣ · E^{p^j}` for some `M_j` prime to `p`. Then there
are `M ≥ 1` (namely `[E : l(s)]`) and `ε` (namely the order at `s` of `N_{E|l(s)}(a)`) with
`ε ≡ M e_j (mod p^j)` for all `j`. (Take norms to `l(s)` and compare orders at `s` in `l[s]`.) -/
theorem exists_dvd_sub_of_forall_pow_eq {s a : L} (hs : Transcendental l s) (ha0 : a ≠ 0)
    (ha : IsAlgebraic l⟮s⟯ a) (e : ℕ → ℤ)
    (h : ∀ j : ℕ, ∃ (M : ℕ) (c : l) (y : L), M.Coprime p ∧ c ≠ 0 ∧ y ∈ l⟮s, a⟯ ∧
      (a * s ^ (-e j)) ^ M = algebraMap l L c * y ^ p ^ j) :
    ∃ (M : ℕ) (ε : ℤ), 0 < M ∧ ∀ j : ℕ, (p : ℤ) ^ j ∣ ε - M * e j := by
  sorry

omit [CharP L p] [PerfectField L] [IsRelAlgClosed l L] in
/-- Blueprint, proof of Proposition 6.12 (lines 729-731), arithmetic: if `ε ≡ M r_j (mod p^j)`
for all `j`, with `M ≥ 1`, write `M = p^β n'` with `p ∤ n'`; then `p^β ∣ ε`, say `ε = p^β m'`, and
`n' r_j ≡ m' (mod p^{j-β})` for all `j ≥ β`. -/
theorem exists_dvd_sub_of_dvd {M : ℕ} (hM : 0 < M) {ε : ℤ} {r : ℕ → ℤ}
    (h : ∀ j : ℕ, (p : ℤ) ^ j ∣ ε - M * r j) :
    ∃ (n' : ℕ) (m' : ℤ) (β : ℕ), 0 < n' ∧ ∀ j : ℕ, β ≤ j → (p : ℤ) ^ (j - β) ∣ n' * r j - m' := by
  sorry

end Fields

namespace CharPHyp

variable {K : Type*} [Field K] [PerfectField K] (H : CharPHyp K l L)
variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]

/-! ### Primitive roots, (6.6) `eq:roots` -/

/-- Blueprint (6.6) `eq:roots`: `Frob(K₀) ⊆ K₀` (`ψ(x^p) = p ψ(x)` has height `ht ψ(x) + 1`). -/
theorem pow_mem_K₀ {x : K} (hx : x ∈ H.K₀ p) : x ^ p ∈ H.K₀ p := by
  sorry

/-- Blueprint (6.6) `eq:roots`: `K = ⋃_j Frob^{-j}(K₀)`, i.e. some `x^{p^j}` lies in `K₀`. -/
theorem exists_pow_pow_mem_K₀ (x : K) : ∃ j : ℕ, x ^ p ^ j ∈ H.K₀ p := by
  sorry

theorem hgtV_nonneg {x : K} (hx : x ∈ H.K₀ p) (hxk : x ∉ H.k) :
    0 ≤ hgtV p (H.B p) (H.ψK x) :=
  (H.mem_K₀_iff_hgtV p hxk).1 hx

/-- Blueprint (6.6) `eq:roots`: for a primitive `x₀`, `ht ψ(x₀^{p^j}) = j`. In particular the
decomposition `x = Frob^j(x₀)` of `exists_primitive_root` is unique. -/
theorem hgtV_pow_pow_of_primitive {x₀ : H.K₀ p} (hx₀ : (H.data p).Δ x₀ ≠ 0) (j : ℕ) :
    hgtV p (H.B p) (H.ψK ((x₀ : K) ^ p ^ j)) = j := by
  sorry

/-- Blueprint (6.6) `eq:roots`: every `x ∈ K₀ \ k` is `Frob^j(x₀)` with `x₀` primitive and
`j = ht ψ(x) ≥ 0` (the *primitive root* of `x`; `K` is perfect of characteristic `p`). -/
theorem exists_primitive_root (x : H.K₀ p) (hx : (x : K) ∉ H.k) :
    ∃ x₀ : H.K₀ p, (H.data p).Δ x₀ ≠ 0 ∧ x₀ ^ p ^ (hgtV p (H.B p) (H.ψK x)).toNat = x := by
  sorry

/-! ### Lemma 6.10 -/

/-- **Blueprint Lemma 6.10** (`lem:tauinQ`), first part: `τ(x) ∈ Q_x` for `x ∈ K₀ \ k` (from
`μ(x) ∈ Q_x`, Lemma 6.5(b), for primitive `x`, and (6.6) in general). -/
theorem τ_mem_pointV {x : H.K₀ p} (hx : (x : K) ∉ H.k) : H.τ p x ∈ pointV l (H.ψK x) := by
  sorry

/-- **Blueprint Lemma 6.10** (`lem:tauinQ`), second part: `τ(k) ⊆ l` (for `c ∈ kˣ` and primitive
`x`, `τ(c) = t(c x)/t(x) ∈ Q_x`; take two transverse `x`). -/
theorem τ_mem_range_of_mem {x : H.K₀ p} (hx : (x : K) ∈ H.k) :
    H.τ p x ∈ (algebraMap l L).range := by
  sorry

/-- **Blueprint Lemma 6.10** (`lem:tauinQ`), third part: `τ(x) ∉ l` for `x ∈ K₀ \ k` (otherwise
`μ(x) ∈ l`, hence `μ(x) ∈ F_p` by the eigenvalue lemma, so `τ(x) ∈ F_p` and `x` lies in the prime
field of `K`, which is contained in `k`). -/
theorem τ_notMem_range {x : H.K₀ p} (hx : (x : K) ∉ H.k) :
    H.τ p x ∉ (algebraMap l L).range := by
  sorry

theorem transcendental_τ {x : H.K₀ p} (hx : (x : K) ∉ H.k) : Transcendental l (H.τ p x) :=
  IsRelAlgClosed.transcendental (H.τ_notMem_range p hx)

/-! ### Lemma 6.11 -/

/-- Blueprint, proof of Lemma 6.11: for transverse `x, y`, the heights of `τ(x)` and `τ(y)`
agree (`(a, b, a b)` and `(τ x, τ y, τ x τ y)` are normalized triples of
`(Q_x, Q_y, Q_{xy})`; Lemma 3.5(b)). -/
theorem hgt_τ_eq_of_transverse {x y : H.K₀ p} (h : (H.data p).Transverse x y) :
    hgt l p (H.B p) (H.τ p x) = hgt l p (H.B p) (H.τ p y) := by
  sorry

/-- Blueprint, proof of Lemma 6.11: the height `e(x)` of `τ(x)` is a constant `e₀` on primitive
elements, and with `σ_x = Frob^{-e₀}(τ x)` (a model generator of `Q_x`) there is a constant
`θ ∈ Fˣ` with `Δ(x) = θ • dlog σ_x` for all primitive `x`. -/
theorem exists_hgt_τ_coeff : ∃ (e₀ : ℤ) (θ : H.F p), θ ≠ 0 ∧ ∀ x : H.K₀ p,
    (H.data p).Δ x ≠ 0 → hgt l p (H.B p) (H.τ p x) = e₀ ∧
      (H.data p).Δ x = θ • modelDLog l (H.B p) (frobZ L p (-e₀) (H.τ p x)) := by
  sorry

/-- Blueprint, end of the proof of Lemma 6.11: `e₀ = 0`, i.e. `τ(x)` is a model generator of
`Q_x` for primitive `x` (`σ_{1-x} = 1 - σ_x` gives `μ(x) = σ_x/(σ_x - 1)`, so `τ(x) = σ_x`). -/
theorem hgt_τ_eq_zero {x : H.K₀ p} (hx : (H.data p).Δ x ≠ 0) :
    hgt l p (H.B p) (H.τ p x) = 0 := by
  sorry

/-- **Blueprint Lemma 6.11** (`lem:theta`): there is `θ ∈ F_pˣ` (an integer prime to `p`) such
that for every primitive `x`, `d τ(x) ≠ 0` and `Δ(x) = θ • dlog τ(x)`. -/
theorem exists_θ : ∃ θ : ℤ, (θ : L) ≠ 0 ∧ ∀ x : H.K₀ p, (H.data p).Δ x ≠ 0 →
    modelD l (H.B p) (H.τ p x) ≠ 0 ∧
      (H.data p).Δ x = (θ : H.F p) • modelDLog l (H.B p) (H.τ p x) := by
  sorry

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

/-- Blueprint (6.7) `eq:lift`: if `ψ' : K₀ˣ → W` vanishes on `kˣ` and `ψ'(x) ∈ G_{Q_x}` for
`x ∈ K₀ \ k`, then there is an integer `m` with `ψ' - m [τ] ∈ p W` on `K₀ˣ`. -/
theorem exists_lift (ψ' : Additive (H.K₀ p)ˣ →+ V l L) (hW : ∀ x, ψ' x ∈ W l p (H.B p))
    (hk : ∀ x : (H.K₀ p)ˣ, ((x : H.K₀ p) : K) ∈ H.k → ψ' (.ofMul x) = 0)
    (hG : ∀ x : (H.K₀ p)ˣ, ((x : H.K₀ p) : K) ∉ H.k →
      ψ' (.ofMul x) ∈ pointGroup (pointV l (H.ψK ((x : H.K₀ p) : K)))) :
    ∃ m : ℤ, ∀ x : (H.K₀ p)ˣ, ∃ w ∈ W l p (H.B p),
      ψ' (.ofMul x) - m • H.τV p (.ofMul x) = p • w := by
  sorry

/-- Blueprint (6.8) `eq:padic`: for every `j` there is an integer `r_j` with
`ψ - r_j [τ] ∈ p^j W` on `K₀ˣ` (by induction on `j`, applying (6.7) to
`ψ_j = p^{-j}(ψ - r_j [τ])`). -/
theorem exists_padic (j : ℕ) : ∃ r : ℤ, ∀ x : (H.K₀ p)ˣ, ∃ w ∈ W l p (H.B p),
    H.ψ₀ p (.ofMul x) - r • H.τV p (.ofMul x) = p ^ j • w := by
  sorry

/-- Blueprint, end of the proof of Proposition 6.12: if `ψ - r_j [τ] ∈ p^j W` for all `j` and
`n' r_j ≡ m' (mod p^{j-β})` for `j ≥ β`, then `n' ψ = m' [τ]` on `K₀ˣ` (as
`n' ψ - m' [τ] ∈ ⋂_j p^j W = 0`). -/
theorem zsmul_ψ₀_eq_of_dvd {r : ℕ → ℤ}
    (hr : ∀ (j : ℕ) (x : (H.K₀ p)ˣ), ∃ w ∈ W l p (H.B p),
      H.ψ₀ p (.ofMul x) - r j • H.τV p (.ofMul x) = p ^ j • w)
    {n' : ℕ} {m' : ℤ} {β : ℕ} (h : ∀ j : ℕ, β ≤ j → (p : ℤ) ^ (j - β) ∣ n' * r j - m')
    (x : (H.K₀ p)ˣ) : (n' : ℤ) • H.ψ₀ p (.ofMul x) = m' • H.τV p (.ofMul x) := by
  sorry

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
  sorry

end CharPHyp

end MilnorAlgDep
