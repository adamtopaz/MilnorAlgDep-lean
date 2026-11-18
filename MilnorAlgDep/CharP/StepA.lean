module

public import MilnorAlgDep.CharP.LevelV
public import MilnorAlgDep.CharP.Quadrangle

/-!
# Step A: the levels of `ψ(x)` and `ψ(1 - x)`

Blueprint Section 6.2 (`sec:stepA`) with `Γ = ℤ`: Proposition 6.1 (`prop:levels`),
equation `eq:nohom`, Lemma 6.2 (`lem:gauge`), Lemma 6.3 (`lem:cocycle`), equation
`eq:nu`.

We work with `H : CharPHyp K l L`, `L` perfect of characteristic `p`, `l` relatively algebraically
closed, and (for Proposition 6.1) `K` perfect.

## Main definitions

* `CharPHyp.n p s = lev ψ(1 - s) - lev ψ(s)` for `s ∉ k`.
* `CharPHyp.c p u w`: for `ψ`-independent `u, w`, the integer `c(u, w)` of `eq:defc`, i.e.
  `(lev ψ(u), lev ψ(w) + c(u, w), *)` is the level triple of `(Q_u, Q_w, Q_{u+w})`. In terms of
  the chosen representatives `ρ`, it is the first entry of `levelTriple l p (ρ u) (ρ w) (ρ (u+w))`.
* `CharPHyp.ν p s`: the right hand side of Lemma 6.2, as a function of `s`.

## Main statements

* `CharPHyp.c_eq_ν`: Lemma 6.2 (gauge), `c(u, w) = ν(-u/w)`; its cases are
  `c_eq_neg_n_of_pos`, `c_eq_zero_of_n_neg`, `c_eq_zero_of_n_eq_zero` and (via `c_swap`) the
  case `n(s) = 0 < n(1/s)`; exhaustiveness is `n_inv_nonneg_of_n_eq_zero`.
* `CharPHyp.c_add_c`: Lemma 6.3 (cocycle), from the quadrangle lemma
  (`levelTriple_fst_add_levelTriple_fst`).
* `CharPHyp.ν_neg_mul`: equation `eq:nu`.
* `nohom`: equation `eq:nohom`.
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
  set j := (levelTriple l p a b d).1
  set k := (levelTriple l p a b d).2
  have hn : IsNormalized l (frobZ L p j b) a (frobZ L p k d) :=
    (isNormalized_levelTriple p h).swap₁₂
  have hn' : IsNormalized l b (frobZ L p (-j) a) (frobZ L p (-j + k) d) := by
    have := (IsNormalized.frobZ_iff p (-j)).2 hn
    rwa [frobZ_neg_apply_frobZ, ← frobZ_add_apply] at this
  have ha : SamePoint l (frobZ L p (-j) a) a :=
    (samePoint_frobZ_left_iff p (-j)).2 (samePoint_refl h.transcendental₁)
  have hd : SamePoint l (frobZ L p (-j + k) d) d :=
    (samePoint_frobZ_left_iff p (-j + k)).2 (samePoint_refl h.transcendental₃)
  rw [levelTriple_eq_of_isNormalized p hn' (samePoint_refl h.transcendental₂) ha hd,
    levDiff_frobZ_left p (samePoint_refl h.transcendental₁), levDiff_self p h.transcendental₁,
    levDiff_self p h.transcendental₂]
  ring

end Aux

/-- Blueprint equation `eq:nohom`: if `K` is perfect of positive characteristic, every
homomorphism `Kˣ → ℤ` is trivial (`Kˣ` is divisible by the characteristic). -/
theorem nohom {K : Type*} [Field K] [PerfectField K] (hK : ringChar K ≠ 0)
    (χ : Additive Kˣ →+ ℤ) : χ = 0 := by
  set q := ringChar K
  have hq : q.Prime := (CharP.char_is_prime_or_zero K q).resolve_right hK
  have : Fact q.Prime := ⟨hq⟩
  have : CharP K q := ringChar.charP K
  ext x
  have hdvd : ∀ n : ℕ, ((q ^ n : ℕ) : ℤ) ∣ χ (.ofMul x) := by
    intro n
    set y : Kˣ := Units.map ((iterateFrobeniusEquiv K q n).symm : K →* K) x
    have hy : y ^ (q ^ n) = x := by
      ext
      rw [Units.val_pow_eq_pow_val]
      change ((iterateFrobeniusEquiv K q n).symm (x : K)) ^ q ^ n = _
      rw [← iterateFrobenius_def, ← coe_iterateFrobeniusEquiv, RingEquiv.apply_symm_apply]
    have hx : Additive.ofMul x = (q ^ n) • Additive.ofMul y := by
      rw [← ofMul_pow, hy]
    exact ⟨χ (.ofMul y), by rw [hx, map_nsmul, nsmul_eq_mul]⟩
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (hdvd (χ (.ofMul x)).natAbs) ?_
  rw [Int.natAbs_natCast]
  exact Nat.lt_pow_self hq.one_lt

namespace CharPHyp

variable {K : Type*} [Field K] (H : CharPHyp K l L)
variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L]

/-! ### The functions `n`, `c` and `ν` -/

/-- Blueprint Section 6.2: `n(s) = lev ψ(1 - s) - lev ψ(s) ∈ ℤ`, for `s ∈ K \ k` (for `s ∈ k` the
value is meaningless). -/
noncomputable def n (s : K) : ℤ :=
  levDiffV p (H.ψK (1 - s)) (H.ψK s)

/-- Blueprint `eq:defc`: for `ψ`-independent `u, w`, the integer `c(u, w)` such that
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
  intro hk
  have hu : u ≠ 0 := fun h0 ↦ h.ne_zero 0 (by simp [h0])
  have hw : w ≠ 0 := fun h0 ↦ h.ne_zero 1 (by simp [h0])
  have hs0 : -u / w ≠ 0 := div_ne_zero (neg_ne_zero.2 hu) hw
  have e : H.ψK u = H.ψK w := by
    have : u = -((-u / w) * w) := by field_simp
    rw [this, ψK_neg, H.ψK_mul_of_mem hk hs0]
  exact absurd (h.injective (a₁ := 0) (a₂ := 1) (by simpa using e)) (by decide)

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
  have huw := h.triple_01
  have hwz := h.triple_12
  have huz := h.triple_02
  have hu : u ≠ 0 := fun h0 ↦ huw.ne_zero 0 (by simp [h0])
  have hw : w ≠ 0 := fun h0 ↦ huw.ne_zero 1 (by simp [h0])
  have hz : z ≠ 0 := fun h0 ↦ hwz.ne_zero 1 (by simp [h0])
  have huw0 := H.ne_zero_of_notMem (H.add_notMem_of_vAlgIndep p huw)
  have hwz0 := H.ne_zero_of_notMem (H.add_notMem_of_vAlgIndep p hwz)
  have huz0k := H.add_notMem_of_vAlgIndep p huz
  have huz0 := H.ne_zero_of_notMem huz0k
  -- `u + w` and `z` are `ψ`-independent, hence `u + w + z ∉ k`
  have hg := H.add_notMem_of_vAlgIndep p (H.vAlgIndep_add_of_vAlgIndep₃ p h)
  have hg0 := H.ne_zero_of_notMem hg
  have hAE : IsAlgebraic l⟮(H.ρ p u : L), (H.ρ p (w + z) : L)⟯ (H.ρ p (u + w + z) : L) := by
    have := H.isAlgebraic_ρ_add p hu hwz0 (by rw [← add_assoc]; exact hg0)
    rwa [← add_assoc] at this
  have hBG : IsAlgebraic l⟮(H.ρ p w : L), (H.ρ p (u + w + z) : L)⟯ (H.ρ p (u + z) : L) := by
    have := H.isAlgebraic_ρ_add p hg0 (neg_ne_zero.2 hw)
      (by rw [show u + w + z + -w = u + z by ring]; exact huz0)
    rwa [ρ_neg, show u + w + z + -w = u + z by ring, Set.pair_comm] at this
  exact levelTriple_fst_add_levelTriple_fst p ((vAlgIndep_triple_iff_vRep p).1 h)
    (H.isCollinearTriple_add p huw) (H.isCollinearTriple_add p hwz) (H.transcendental_ρ p hg)
    (H.isAlgebraic_ρ_add p huw0 hz hg0) hAE (H.transcendental_ρ p huz0k)
    (H.isAlgebraic_ρ_add p hu hz huz0) hBG

/-! ### Proposition 6.1 -/

/-- Blueprint equation `eq:nu`: `ν(-s s') = ν(s) + ν(s')` for `ψ`-independent `s, s'`. -/
theorem ν_neg_mul {s s' : K} (h : VAlgIndep l ![H.ψK s, H.ψK s']) :
    H.ν p (-(s * s')) = H.ν p s + H.ν p s' := by
  obtain ⟨i, h3⟩ := H.exists_vAlgIndep₃ p h
  set z := (H.x i : K)
  have hs : s ≠ 0 := fun h0 ↦ h.ne_zero 0 (by simp [h0])
  have hs' : s' ≠ 0 := fun h0 ↦ h.ne_zero 1 (by simp [h0])
  have hz : z ≠ 0 := (H.x i).ne_zero
  have hψw : H.ψK (-(s' * z)) = H.ψK s' + H.ψK z := by rw [ψK_neg, H.ψK_mul hs' hz]
  have hψu : H.ψK (s * s' * z) = H.ψK s + H.ψK s' + H.ψK z := by
    rw [H.ψK_mul (mul_ne_zero hs hs') hz, H.ψK_mul hs hs']
  have h3' : VAlgIndep l ![H.ψK (s * s' * z), H.ψK (-(s' * z)), H.ψK z] := by
    rw [hψu, hψw]
    exact h3.add_add₃
  have hc := H.c_add_c p h3'
  rw [H.c_eq_ν p h3'.triple_01, H.c_eq_ν p h3'.triple_12, H.c_eq_ν p h3'.triple_02] at hc
  have e1 : -(s * s' * z) / -(s' * z) = s := by field_simp
  have e2 : -(-(s' * z)) / z = s' := by field_simp
  have e3 : -(s * s' * z) / z = -(s * s') := by field_simp
  rw [e1, e2, e3] at hc
  exact hc.symm

/-- `δ(a) = ν(-a) - ν(a)` takes the same value at `ψ`-independent `a, b` (blueprint, proof of
Proposition 6.1). -/
theorem ν_neg_sub_ν_eq {a b : K} (h : VAlgIndep l ![H.ψK a, H.ψK b]) :
    H.ν p (-a) - H.ν p a = H.ν p (-b) - H.ν p b := by
  have h₁ : VAlgIndep l ![H.ψK (-a), H.ψK b] := by rwa [ψK_neg]
  have h₂ : VAlgIndep l ![H.ψK a, H.ψK (-b)] := by rwa [ψK_neg]
  have e₁ := H.ν_neg_mul p h₁
  have e₂ := H.ν_neg_mul p h₂
  rw [neg_mul, neg_neg] at e₁
  rw [mul_neg, neg_neg] at e₂
  linarith

/-- Blueprint, proof of Proposition 6.1: `ν(s s') = ν(s) + ν(s')` for `ψ`-independent `s, s'`
(the constant `δ₀ = ν(-s) - ν(s)` vanishes). -/
theorem ν_mul {s s' : K} (h : VAlgIndep l ![H.ψK s, H.ψK s']) :
    H.ν p (s * s') = H.ν p s + H.ν p s' := by
  have h₁ : VAlgIndep l ![H.ψK (-s), H.ψK s'] := by rwa [ψK_neg]
  -- `δ(s) = δ(s') = δ(-s) = -δ(s)`
  have d₁ := H.ν_neg_sub_ν_eq p h
  have d₂ := H.ν_neg_sub_ν_eq p h₁
  rw [neg_neg] at d₂
  have e := H.ν_neg_mul p h₁
  rw [neg_mul, neg_neg] at e
  linarith

/-- Blueprint, proof of Proposition 6.1: for `c ∈ kˣ`, `ϱ(c) = ν(c w) - ν(w)` does not depend on
`w ∉ k`. -/
theorem ν_mul_sub_ν_eq {c w w' : K} (hc : c ∈ H.k) (hc0 : c ≠ 0) (hw : w ∉ H.k)
    (hw' : w' ∉ H.k) : H.ν p (c * w) - H.ν p w = H.ν p (c * w') - H.ν p w' := by
  have key : ∀ {a b : K}, VAlgIndep l ![H.ψK a, H.ψK b] →
      H.ν p (c * a) - H.ν p a = H.ν p (c * b) - H.ν p b := by
    intro a b hab
    have h₁ : VAlgIndep l ![H.ψK (c * a), H.ψK b] := by rwa [H.ψK_mul_of_mem hc hc0]
    have h₂ : VAlgIndep l ![H.ψK a, H.ψK (c * b)] := by rwa [H.ψK_mul_of_mem hc hc0]
    have e₁ := H.ν_mul p h₁
    have e₂ := H.ν_mul p h₂
    rw [show c * a * b = a * (c * b) by ring] at e₁
    linarith
  obtain ⟨r, hr, hr'⟩ := H.exists_vAlgIndep_pair hw hw'
  rw [key hr, key hr']

/-- `ν(x y) = ν(x) + ν(y)` for `x, y, x y ∉ k` (blueprint, proof of Proposition 6.1). -/
theorem ν_mul_of_notMem {x y : K} (hx : x ∉ H.k) (hy : y ∉ H.k) (hxy : x * y ∉ H.k) :
    H.ν p (x * y) = H.ν p x + H.ν p y := by
  have hx0 := H.ne_zero_of_notMem hx
  have hy0 := H.ne_zero_of_notMem hy
  by_cases hind : VAlgIndep l ![H.ψK x, H.ψK y]
  · exact H.ν_mul p hind
  -- `Q_x = Q_y`: compare with a third element `w`
  obtain ⟨w, hxw, hyw⟩ := H.exists_vAlgIndep_pair hx hy
  have hw0 : H.ψK w ≠ 0 := hxw.ne_zero 1
  have hψx := H.ψK_ne_zero hx
  have hψy := H.ψK_ne_zero hy
  have hpt : pointV l (H.ψK y) = pointV l (H.ψK x) := by
    rw [vAlgIndep_pair_iff hψx hψy, not_not] at hind
    exact hind.symm
  have hymem : H.ψK y ∈ pointGroup (pointV l (H.ψK x)) :=
    (mem_pointGroup_pointV_iff hψx).2 (Or.inr hpt)
  -- `x y, w` are independent
  have hxyw : VAlgIndep l ![H.ψK (x * y), H.ψK w] := by
    have hxy0 := H.ψK_ne_zero hxy
    have hxypt : pointV l (H.ψK (x * y)) = pointV l (H.ψK x) := by
      have hm : H.ψK (x * y) ∈ pointGroup (pointV l (H.ψK x)) := by
        rw [H.ψK_mul hx0 hy0]
        exact add_mem (mem_pointGroup_pointV _) hymem
      rcases (mem_pointGroup_pointV_iff hψx).1 hm with h0 | h0
      · exact absurd h0 hxy0
      · exact h0
    rw [vAlgIndep_pair_iff hxy0 hw0, hxypt]
    exact (vAlgIndep_pair_iff hψx hw0).1 hxw
  -- `x, y w` are independent
  have hxyw' : VAlgIndep l ![H.ψK x, H.ψK (y * w)] := by
    have := hxw.add_of_mem_pointGroup hymem
    have hw0' : w ≠ 0 := fun h0 ↦ hw0 (by rw [h0, ψK_zero])
    rwa [H.ψK_mul hy0 hw0', add_comm]
  have e₁ := H.ν_mul p hxyw
  have e₂ := H.ν_mul p hxyw'
  have e₃ := H.ν_mul p hyw
  rw [show x * y * w = x * (y * w) by ring] at e₁
  linarith

/-- Blueprint, proof of Proposition 6.1: `ν` extends to a homomorphism `χ : Kˣ → ℤ` (with
`χ = ϱ` on `kˣ`, `ϱ(c) = ν(c w) - ν(w)`). -/
theorem exists_addMonoidHom_eq_ν :
    ∃ χ : Additive Kˣ →+ ℤ, ∀ x : Kˣ, (x : K) ∉ H.k → χ (.ofMul x) = H.ν p x := by
  classical
  set r₀ : K := ((H.x 0 : Kˣ) : K)
  have hr₀ : r₀ ∉ H.k := H.x_notMem 0
  let f : K → ℤ := fun x ↦ if x ∈ H.k then H.ν p (x * r₀) - H.ν p r₀ else H.ν p x
  have hf_mem : ∀ {x : K}, x ∈ H.k → f x = H.ν p (x * r₀) - H.ν p r₀ := fun hx ↦ ite_eq_left hx
  have hf_notMem : ∀ {x : K}, x ∉ H.k → f x = H.ν p x := fun hx ↦ ite_eq_right hx
  have hmul_mem : ∀ {c y : K}, c ∈ H.k → c ≠ 0 → y ∉ H.k → c * y ∉ H.k := fun hc hc0 hy h ↦
    hy (by simpa [hc0] using mul_mem (inv_mem hc) h)
  have hadd : ∀ x y : K, x ≠ 0 → y ≠ 0 → f (x * y) = f x + f y := by
    intro x y hx0 hy0
    by_cases hx : x ∈ H.k <;> by_cases hy : y ∈ H.k
    · rw [hf_mem (mul_mem hx hy), hf_mem hx, hf_mem hy]
      have := H.ν_mul_sub_ν_eq p hx hx0 (hmul_mem hy hy0 hr₀) hr₀
      rw [← mul_assoc] at this
      linarith
    · rw [hf_notMem (hmul_mem hx hx0 hy), hf_mem hx, hf_notMem hy]
      have := H.ν_mul_sub_ν_eq p hx hx0 hy hr₀
      linarith
    · rw [mul_comm, hf_notMem (hmul_mem hy hy0 hx), hf_mem hy, hf_notMem hx]
      have := H.ν_mul_sub_ν_eq p hy hy0 hx hr₀
      linarith
    · by_cases hxy : x * y ∈ H.k
      · rw [hf_mem hxy, hf_notMem hx, hf_notMem hy]
        -- compare with `w` independent of `x` and `y`
        obtain ⟨w, hxw, hyw⟩ := H.exists_vAlgIndep_pair hx hy
        have hwk : w ∉ H.k := fun hk ↦ hxw.ne_zero 1 (H.ψK_eq_zero_iff.2 hk)
        have hw0 := H.ne_zero_of_notMem hwk
        have e₀ := H.ν_mul_sub_ν_eq p hxy (mul_ne_zero hx0 hy0) hr₀ hwk
        have hyw' : y * w ∉ H.k := fun hk ↦ by
          have hψy := H.ψK_ne_zero hy
          have hψw := H.ψK_ne_zero hwk
          have h0 := (pointV_add_ne hψy hψw ((vAlgIndep_pair_iff hψy hψw).1 hyw)).1
          rw [← H.ψK_mul hy0 hw0] at h0
          exact h0 (H.ψK_eq_zero_iff.2 hk)
        have hxyw : x * (y * w) ∉ H.k := by
          rw [← mul_assoc]
          exact hmul_mem hxy (mul_ne_zero hx0 hy0) hwk
        have e₁ := H.ν_mul_of_notMem p hx hyw' hxyw
        have e₂ := H.ν_mul p hyw
        rw [← mul_assoc] at e₁
        linarith
      · rw [hf_notMem hxy, hf_notMem hx, hf_notMem hy]
        exact H.ν_mul_of_notMem p hx hy hxy
  refine ⟨AddMonoidHom.mk' (fun x ↦ f (Additive.toMul x : Kˣ)) fun x y ↦ ?_, fun x hx ↦ ?_⟩
  · change f ((Additive.toMul x * Additive.toMul y : Kˣ) : K) = _
    rw [Units.val_mul]
    exact hadd _ _ (Additive.toMul x).ne_zero (Additive.toMul y).ne_zero
  · exact hf_notMem hx

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
