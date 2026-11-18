module

public import MilnorAlgDep.CharP.LevelV
public import MilnorAlgDep.CharP.Quadrangle

/-!
# Step A: the levels of `ψ(x)` and `ψ(1 - x)`

Blueprint Section 6.2 (`sec:stepA`) with `Γ = ℤ`: Proposition 6.1 (`prop:levels`),
equation (6.2) `eq:nohom`, Lemma 6.2 (`lem:gauge`), Lemma 6.3 (`lem:cocycle`), equation (6.4)
`eq:nu`.

We work with `H : CharPHyp K l L`, `L` perfect of characteristic `p`, `l` relatively algebraically
closed, and (for Proposition 6.1) `K` perfect.

## Main definitions

* `CharPHyp.n p s = lev ψ(1 - s) - lev ψ(s)` for `s ∉ k`.
* `CharPHyp.c p u w`: for `ψ`-independent `u, w`, the integer `c(u, w)` of (6.3) `eq:defc`, i.e.
  `(lev ψ(u), lev ψ(w) + c(u, w), *)` is the level triple of `(Q_u, Q_w, Q_{u+w})`. In terms of
  the chosen representatives `ρ`, it is the first entry of `levelTriple l p (ρ u) (ρ w) (ρ (u+w))`.
* `CharPHyp.ν p s`: the right hand side of Lemma 6.2, as a function of `s`.

## Main statements

* `CharPHyp.c_eq_ν`: Lemma 6.2 (gauge), `c(u, w) = ν(-u/w)`; its cases are
  `c_eq_neg_n_of_pos`, `c_eq_zero_of_n_neg`, `c_eq_zero_of_n_eq_zero` and (via `c_swap`) the
  case `n(s) = 0 < n(1/s)`; exhaustiveness is `n_inv_nonneg_of_n_eq_zero`.
* `CharPHyp.c_add_c`: Lemma 6.3 (cocycle), from the quadrangle lemma
  (`levelTriple_fst_add_levelTriple_fst`).
* `CharPHyp.ν_neg_mul`: equation (6.4) `eq:nu`.
* `nohom`: equation (6.2) `eq:nohom`.
* `CharPHyp.n_eq_zero`, `CharPHyp.levDiffV_one_sub`, `CharPHyp.hgtV_one_sub`:
  Proposition 6.1, `lev ψ(1 - x) = lev ψ(x)` for `x ∉ k`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf IntermediateField

variable {l L : Type*} [Field l] [Field L] [Algebra l L]

/-! ### Auxiliary lemmas -/

section Aux

-- TODO(move): `Foundations/AlgIndep.lean`.
theorem VAlgIndep.pair_swap {v w : V l L} (h : VAlgIndep l ![v, w]) : VAlgIndep l ![w, v] := by
  have := h.comp ![1, 0] (by decide)
  convert this using 1
  ext i
  fin_cases i <;> rfl

theorem VAlgIndep.triple_01 {u v w : V l L} (h : VAlgIndep l ![u, v, w]) :
    VAlgIndep l ![u, v] := by
  have := h.comp ![0, 1] (by decide)
  convert this using 1
  ext i
  fin_cases i <;> rfl

theorem VAlgIndep.triple_02 {u v w : V l L} (h : VAlgIndep l ![u, v, w]) :
    VAlgIndep l ![u, w] := by
  have := h.comp ![0, 2] (by decide)
  convert this using 1
  ext i
  fin_cases i <;> rfl

theorem VAlgIndep.triple_12 {u v w : V l L} (h : VAlgIndep l ![u, v, w]) :
    VAlgIndep l ![v, w] := by
  have := h.comp ![1, 2] (by decide)
  convert this using 1
  ext i
  fin_cases i <;> rfl

-- TODO(move): `CharP/Normalized.lean`.
/-- Swapping the first two points of a collinear triple negates the first entry of the level
triple relative to the given elements: if `(a, Frob^j b, *)` is normalized, then so is
`(b, Frob^{-j} a, *)`. (This is "`c(w, u) = -c(u, w)`", blueprint line 438.) -/
theorem levelTriple_swap_fst (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L]
    [IsRelAlgClosed l L] {a b d : L} (h : IsCollinearTriple l a b d) :
    (levelTriple l p b a d).1 = -(levelTriple l p a b d).1 := by
  sorry

end Aux

/-- Blueprint equation (6.2) `eq:nohom`: if `K` is perfect of positive characteristic, every
homomorphism `Kˣ → ℤ` is trivial (`Kˣ` is divisible by the characteristic). -/
theorem nohom {K : Type*} [Field K] [PerfectField K] (hK : ringChar K ≠ 0)
    (χ : Additive Kˣ →+ ℤ) : χ = 0 := by
  sorry

namespace CharPHyp

variable {K : Type*} [Field K] (H : CharPHyp K l L)
variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L]

/-! ### The functions `n`, `c` and `ν` -/

/-- Blueprint Section 6.2: `n(s) = lev ψ(1 - s) - lev ψ(s) ∈ ℤ`, for `s ∈ K \ k` (for `s ∈ k` the
value is meaningless). -/
noncomputable def n (s : K) : ℤ :=
  levDiffV p (H.ψK (1 - s)) (H.ψK s)

/-- Blueprint (6.3) `eq:defc`: for `ψ`-independent `u, w`, the integer `c(u, w)` such that
`(lev ψ(u), lev ψ(w) + c(u, w), *)` is the level triple of `(Q_u, Q_w, Q_{u+w})`, i.e. the first
entry of the level triple of `(Q_u, Q_w, Q_{u+w})` relative to the chosen representatives
`ρ u, ρ w, ρ (u + w)` (`isNormalized_levelTriple`). Meaningless if `u, w` are not
`ψ`-independent. -/
noncomputable def c (u w : K) : ℤ :=
  (levelTriple l p (H.ρ p u : L) (H.ρ p w : L) (H.ρ p (u + w) : L)).1

/-- Blueprint Lemma 6.2: the function `ν(s)`, defined by the case distinction of the lemma:
`-n(s)` if `n(s) > 0`; `n(1/s)` if `n(s) = 0` and `n(1/s) > 0`; `0` otherwise. By Lemma 6.2
(`c_eq_ν`), `c(u, w) = ν(-u/w)` for all `ψ`-independent `u, w`. -/
noncomputable def ν (s : K) : ℤ :=
  if 0 < H.n p s then -H.n p s else if H.n p s = 0 ∧ 0 < H.n p s⁻¹ then H.n p s⁻¹ else 0

variable [IsRelAlgClosed l L]

omit [PerfectField L] in
theorem samePointV_one_sub {s : K} (hs : s ∉ H.k) :
    SamePointV l (H.ψK (1 - s)) (H.ψK s) :=
  ⟨H.ψK_ne_zero (H.one_sub_notMem hs), H.ψK_ne_zero hs, H.pointV_ψK_one_sub hs⟩

/-- Blueprint Section 6.2: `n(1 - s) = -n(s)`. -/
theorem n_one_sub {s : K} (hs : s ∉ H.k) : H.n p (1 - s) = -H.n p s := by
  rw [n, n, sub_sub_cancel, levDiffV_swap p (H.samePointV_one_sub hs)]

/-- Blueprint Section 6.2: `n(1/s) = lev(ψ(1 - s) - ψ(s)) - lev ψ(s)`. -/
theorem n_inv {s : K} (hs : s ∉ H.k) :
    H.n p s⁻¹ = levDiffV p (H.ψK (1 - s) - H.ψK s) (H.ψK s) := by
  sorry

/-- `c(w, u) = -c(u, w)` (blueprint line 438). -/
theorem c_swap {u w : K} (h : VAlgIndep l ![H.ψK u, H.ψK w]) : H.c p w u = -H.c p u w := by
  rw [c, c, add_comm w u]
  exact levelTriple_swap_fst p (H.isCollinearTriple_add p h)

/-! ### Lemma 6.2 (gauge) -/

/-- **Blueprint Lemma 6.2** (gauge), first case: if `n(s) > 0` for `s = -u/w`, then
`c(u, w) = -n(s)`. -/
theorem c_eq_neg_n_of_pos {u w : K} (h : VAlgIndep l ![H.ψK u, H.ψK w])
    (hn : 0 < H.n p (-u / w)) : H.c p u w = -H.n p (-u / w) := by
  sorry

/-- **Blueprint Lemma 6.2** (gauge), second case: if `n(s) < 0` for `s = -u/w`, then
`c(u, w) = 0`. -/
theorem c_eq_zero_of_n_neg {u w : K} (h : VAlgIndep l ![H.ψK u, H.ψK w])
    (hn : H.n p (-u / w) < 0) : H.c p u w = 0 := by
  sorry

/-- **Blueprint Lemma 6.2** (gauge), exhaustiveness: if `n(s) = 0` then `n(1/s) ≥ 0` (because
`e / a` is separable over `l(a)`, blueprint line 459). -/
theorem n_inv_nonneg_of_n_eq_zero {s : K} (hs : s ∉ H.k) (hn : H.n p s = 0) :
    0 ≤ H.n p s⁻¹ := by
  sorry

/-- **Blueprint Lemma 6.2** (gauge), third case: if `n(s) = n(1/s) = 0` for `s = -u/w`, then
`c(u, w) = 0`. -/
theorem c_eq_zero_of_n_eq_zero {u w : K} (h : VAlgIndep l ![H.ψK u, H.ψK w])
    (hn : H.n p (-u / w) = 0) (hn' : H.n p (-u / w)⁻¹ = 0) : H.c p u w = 0 := by
  sorry

omit [PerfectField L] [IsRelAlgClosed l L] in
/-- For `ψ`-independent `u, w`, `s = -u/w ∉ k` (otherwise `ψ(u) = ψ(w)`). -/
theorem notMem_neg_div {u w : K} (h : VAlgIndep l ![H.ψK u, H.ψK w]) : -u / w ∉ H.k := by
  sorry

/-- **Blueprint Lemma 6.2 (The gauge of a sum)**: for `ψ`-independent `u, w`,
`c(u, w) = ν(-u/w)`; in particular `c(u, w)` only depends on `-u/w`. -/
theorem c_eq_ν {u w : K} (h : VAlgIndep l ![H.ψK u, H.ψK w]) : H.c p u w = H.ν p (-u / w) := by
  have hs := H.notMem_neg_div h
  have e : -w / u = (-u / w)⁻¹ := by rw [inv_div, neg_div, div_neg]
  rcases lt_trichotomy 0 (H.n p (-u / w)) with hn | hn | hn
  · rw [ν, ite_eq_left hn, H.c_eq_neg_n_of_pos p h hn]
  · have hn' := H.n_inv_nonneg_of_n_eq_zero p hs hn.symm
    rcases hn'.lt_or_eq with hn' | hn'
    · -- the case `n(s) = 0 < n(1/s)`: apply the first case to `(w, u)`
      rw [ν, ite_eq_right hn.ge.not_gt, ite_eq_left ⟨hn.symm, hn'⟩, H.c_swap p h.pair_swap,
        H.c_eq_neg_n_of_pos p h.pair_swap (by rwa [e]), e, neg_neg]
    · rw [ν, ite_eq_right hn.ge.not_gt, ite_eq_right (fun h' ↦ h'.2.ne hn'),
        H.c_eq_zero_of_n_eq_zero p h hn.symm hn'.symm]
  · rw [ν, ite_eq_right hn.not_gt, ite_eq_right (fun h' ↦ hn.ne h'.1),
      H.c_eq_zero_of_n_neg p h hn]

/-! ### Lemma 6.3 (cocycle) -/

/-- **Blueprint Lemma 6.3 (Cocycle)**: if `u, w, z` are `ψ`-independent, then
`c(u, z) = c(u, w) + c(w, z)`. Proof: the quadrangle lemma for the seven points
`Q_u, Q_w, Q_z, Q_{u+w}, Q_{w+z}, Q_{u+w+z}, Q_{u+z}` (`levelTriple_fst_add_levelTriple_fst`). -/
theorem c_add_c {u w z : K} (h : VAlgIndep l ![H.ψK u, H.ψK w, H.ψK z]) :
    H.c p u w + H.c p w z = H.c p u z := by
  sorry

/-! ### Proposition 6.1 -/

/-- Blueprint equation (6.4) `eq:nu`: `ν(-s s') = ν(s) + ν(s')` for `ψ`-independent `s, s'`. -/
theorem ν_neg_mul {s s' : K} (h : VAlgIndep l ![H.ψK s, H.ψK s']) :
    H.ν p (-(s * s')) = H.ν p s + H.ν p s' := by
  sorry

/-- Blueprint, proof of Proposition 6.1: `ν(s s') = ν(s) + ν(s')` for `ψ`-independent `s, s'`
(the constant `δ₀ = ν(-s) - ν(s)` vanishes). -/
theorem ν_mul {s s' : K} (h : VAlgIndep l ![H.ψK s, H.ψK s']) :
    H.ν p (s * s') = H.ν p s + H.ν p s' := by
  sorry

/-- Blueprint, proof of Proposition 6.1: `ν` extends to a homomorphism `χ : Kˣ → ℤ` (with
`χ = ϱ` on `kˣ`, `ϱ(c) = ν(c w) - ν(w)`). -/
theorem exists_addMonoidHom_eq_ν :
    ∃ χ : Additive Kˣ →+ ℤ, ∀ x : Kˣ, (x : K) ∉ H.k → χ (.ofMul x) = H.ν p x := by
  sorry

/-- Blueprint, proof of Proposition 6.1: `ν = 0` on `K \ k`, by `eq:nohom`. -/
theorem ν_eq_zero [PerfectField K] {s : K} (hs : s ∉ H.k) : H.ν p s = 0 := by
  obtain ⟨χ, hχ⟩ := H.exists_addMonoidHom_eq_ν p
  have h0 := nohom H.A4 χ
  have := hχ (Units.mk0 s (H.ne_zero_of_notMem hs)) hs
  rw [h0, Units.val_mk0] at this
  exact this.symm

/-- **Blueprint Proposition 6.1**: `n(s) = 0`, i.e. `lev ψ(1 - s) = lev ψ(s)`, for every
`s ∈ K \ k`. -/
theorem n_eq_zero [PerfectField K] {s : K} (hs : s ∉ H.k) : H.n p s = 0 := by
  have hle : ∀ t : K, t ∉ H.k → H.n p t ≤ 0 := by
    intro t ht
    by_contra hpos
    have := H.ν_eq_zero p ht
    rw [ν, ite_eq_left (not_le.1 hpos)] at this
    omega
  have h1 := hle _ (H.one_sub_notMem hs)
  rw [H.n_one_sub p hs] at h1
  exact le_antisymm (hle s hs) (by omega)

/-- **Blueprint Proposition 6.1** (`prop:levels`): for every `x ∈ K \ k`,
`lev ψ(1 - x) = lev ψ(x)`. -/
theorem levDiffV_one_sub [PerfectField K] {x : K} (hx : x ∉ H.k) :
    levDiffV p (H.ψK (1 - x)) (H.ψK x) = 0 :=
  H.n_eq_zero p hx

/-- **Blueprint Proposition 6.1**, in terms of heights: `ψ(1 - x)` and `ψ(x)` have the same
height with respect to any transcendence basis. -/
theorem hgtV_one_sub [PerfectField K] {ι : Type*} {B : ι → L} (hB : IsTranscendenceBasis l B)
    {x : K} (hx : x ∉ H.k) : hgtV p B (H.ψK (1 - x)) = hgtV p B (H.ψK x) := by
  have := hgtV_sub_hgtV p hB (H.samePointV_one_sub hx)
  rw [H.levDiffV_one_sub p hx] at this
  omega

end CharPHyp

end MilnorAlgDep
