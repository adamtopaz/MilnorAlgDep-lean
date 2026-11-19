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

/-- Normality criterion in coordinates (blueprint, proof of Lemma 6.2): in the model `L_B` of an
algebraically independent pair `B = (b₁, b₂)`, if the differentials of `X, Y, Z ∈ L_B` have
pairwise non-proportional coordinates and `Z` is algebraic over `l(X, Y)`, then `(X, Y, Z)` is
normalized. -/
theorem isNormalized_of_coords [PerfectField l] {b₁ b₂ X Y Z : L}
    (hB : AlgebraicIndependent l ![b₁, b₂]) (hX : X ∈ model l ![b₁, b₂])
    (hY : Y ∈ model l ![b₁, b₂]) (hZ : Z ∈ model l ![b₁, b₂])
    {α₁ α₂ β₁ β₂ γ₁ γ₂ : model l ![b₁, b₂]}
    (hdX : modelD l ![b₁, b₂] X = α₁ • modelD l ![b₁, b₂] b₁ + α₂ • modelD l ![b₁, b₂] b₂)
    (hdY : modelD l ![b₁, b₂] Y = β₁ • modelD l ![b₁, b₂] b₁ + β₂ • modelD l ![b₁, b₂] b₂)
    (hdZ : modelD l ![b₁, b₂] Z = γ₁ • modelD l ![b₁, b₂] b₁ + γ₂ • modelD l ![b₁, b₂] b₂)
    (hXY : α₁ * β₂ - α₂ * β₁ ≠ 0) (hXZ : α₁ * γ₂ - α₂ * γ₁ ≠ 0) (hYZ : β₁ * γ₂ - β₂ * γ₁ ≠ 0)
    (halg : IsAlgebraic l⟮X, Y⟯ Z) : IsNormalized l X Y Z := by
  have hli : LinearIndependent (model l ![b₁, b₂])
      ![modelD l ![b₁, b₂] b₁, modelD l ![b₁, b₂] b₂] := by
    have := linearIndependent_modelD hB
    convert this using 1
    ext i
    fin_cases i <;> rfl
  refine isNormalized_of_linearIndependent_modelD hX hY hZ ?_ ?_ ?_ halg
  · rw [hdX, hdY]
    exact linearIndependent_pair_smul_add hli hXY
  · rw [hdX, hdZ]
    exact linearIndependent_pair_smul_add hli hXZ
  · rw [hdY, hdZ]
    exact linearIndependent_pair_smul_add hli hYZ

/-- `d b₁ ≠ 0` in the model of an algebraically independent pair `(b₁, b₂)`. -/
theorem modelD_ne_zero_left {b₁ b₂ : L} (hB : AlgebraicIndependent l ![b₁, b₂]) :
    modelD l ![b₁, b₂] b₁ ≠ 0 :=
  (linearIndependent_modelD hB).ne_zero 0

theorem modelD_ne_zero_right {b₁ b₂ : L} (hB : AlgebraicIndependent l ![b₁, b₂]) :
    modelD l ![b₁, b₂] b₂ ≠ 0 :=
  (linearIndependent_modelD hB).ne_zero 1

/-- Frobenius twists of an algebraically independent pair are algebraically independent. -/
theorem algebraicIndependent_frobZ_pair (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L]
    [IsRelAlgClosed l L] {a y : L} (h : AlgebraicIndependent l ![a, y]) (i j : ℤ) :
    AlgebraicIndependent l ![frobZ L p i a, frobZ L p j y] := by
  have ha : Transcendental l a := h.transcendental 0
  have hy : Transcendental l y := h.transcendental 1
  by_contra hcon
  have hsp : SamePoint l (frobZ L p i a) (frobZ L p j y) :=
    samePoint_iff_not_algebraicIndependent.2 ⟨(transcendental_frobZ_iff p i).2 ha,
      (transcendental_frobZ_iff p j).2 hy, hcon⟩
  rw [samePoint_frobZ_left_iff, samePoint_frobZ_right_iff] at hsp
  exact (samePoint_iff_not_algebraicIndependent.1 hsp).2.2 h

section RepAux

variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L]

/-- Three elements of `V` have representatives with a common denominator. -/
theorem exists_isVRep₃ (v₁ v₂ v₃ : V l L) : ∃ (N : ℕ) (a₁ a₂ a₃ : Lˣ),
    IsVRep p v₁ N a₁ ∧ IsVRep p v₂ N a₂ ∧ IsVRep p v₃ N a₃ := by
  have h₁ := isVRep_vRep p v₁
  have h₂ := isVRep_vRep p v₂
  have h₃ := isVRep_vRep p v₃
  refine ⟨vRepNat p v₁ * vRepNat p v₂ * vRepNat p v₃, _, _, _,
    h₁.pow p (Nat.mul_pos h₂.pos h₃.pos) (Nat.coprime_mul_iff_left.2 ⟨h₂.coprime, h₃.coprime⟩)
      (by ring),
    h₂.pow p (Nat.mul_pos h₁.pos h₃.pos) (Nat.coprime_mul_iff_left.2 ⟨h₁.coprime, h₃.coprime⟩)
      (by ring),
    h₃.pow p (Nat.mul_pos h₁.pos h₂.pos) (Nat.coprime_mul_iff_left.2 ⟨h₁.coprime, h₂.coprime⟩)
      (by ring)⟩

variable [IsRelAlgClosed l L]

omit [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L] in
theorem IsVRep.algebraicIndependent_pair {v w : V l L} {N M : ℕ} {a b : Lˣ}
    (hv : IsVRep p v N a) (hw : IsVRep p w M b) (h : VAlgIndep l ![v, w]) :
    AlgebraicIndependent l ![(a : L), (b : L)] := by
  have := (VAlgIndep.iff_of_nsmul_eq_cls (N := ![N, M]) (a := ![a, b])
    (fun i ↦ by fin_cases i <;> simp [hv.pos, hw.pos])
    (fun i ↦ by fin_cases i <;> simp [hv.nsmul_eq, hw.nsmul_eq])).1 h
  convert this using 1
  ext i
  fin_cases i <;> rfl

end RepAux

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

omit [PerfectField L] in
theorem samePointV_one_sub_sub {s : K} (hs : s ∉ H.k) :
    SamePointV l (H.ψK (1 - s) - H.ψK s) (H.ψK s) := by
  have hs0 := H.ne_zero_of_notMem hs
  have h1s := H.ne_zero_of_notMem (H.one_sub_notMem hs)
  have e₁ : H.ψK (1 - s⁻¹) = H.ψK (1 - s) - H.ψK s := by
    rw [show 1 - s⁻¹ = -((1 - s) / s) by field_simp; ring, ψK_neg, H.ψK_div h1s hs0]
  rw [← e₁]
  have hi := H.samePointV_one_sub (H.inv_notMem hs)
  rw [ψK_inv] at hi
  exact ⟨hi.1, H.ψK_ne_zero hs, hi.2.2.trans (pointV_neg _)⟩

/-- Blueprint Section 6.2: `n(1/s) = lev(ψ(1 - s) - ψ(s)) - lev ψ(s)`. -/
theorem n_inv {s : K} (hs : s ∉ H.k) :
    H.n p s⁻¹ = levDiffV p (H.ψK (1 - s) - H.ψK s) (H.ψK s) := by
  have hs0 := H.ne_zero_of_notMem hs
  have h1s := H.ne_zero_of_notMem (H.one_sub_notMem hs)
  have e₁ : H.ψK (1 - s⁻¹) = H.ψK (1 - s) - H.ψK s := by
    rw [show 1 - s⁻¹ = -((1 - s) / s) by field_simp; ring, ψK_neg, H.ψK_div h1s hs0]
  rw [n, e₁, ψK_inv, ← neg_one_smul ℚ (H.ψK s),
    levDiffV_smul_right p (by norm_num) (H.samePointV_one_sub_sub hs), padicValRat.neg,
    padicValRat.one, sub_zero]

/-- `c(w, u) = -c(u, w)` (blueprint line 438). -/
theorem c_swap {u w : K} (h : VAlgIndep l ![H.ψK u, H.ψK w]) : H.c p w u = -H.c p u w := by
  rw [c, c, add_comm w u]
  exact levelTriple_swap_fst p (H.isCollinearTriple_add p h)

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

/-! ### Lemma 6.2 (gauge) -/

/-- The common setting of the proof of Lemma 6.2 (blueprint lines 443-445): for `ψ`-independent
`u, w` and `s = -u/w`, representatives with a common `N`: `N ψ(s) = [a]`, `N ψ(w) = [y]`,
`N ψ(1 - s) = [e]`, so that `N ψ(u) = [a y]` and `N ψ(u + w) = [y e]`; `a, y` are algebraically
independent, `e` lies in the point of `a`, `n(s) = lev(e) - lev(a)`, and `c(u, w)` can be computed
from any normalized triple in the points `Q_u, Q_w, Q_{u+w}`. -/
theorem gauge_setup {u w : K} (h : VAlgIndep l ![H.ψK u, H.ψK w]) :
    ∃ (N : ℕ) (a y e : Lˣ), IsVRep p (H.ψK (-u / w)) N a ∧ IsVRep p (H.ψK (1 - -u / w)) N e ∧
      AlgebraicIndependent l ![(a : L), (y : L)] ∧ SamePoint l (e : L) (a : L) ∧
      Transcendental l ((a * y : Lˣ) : L) ∧ Transcendental l ((y * e : Lˣ) : L) ∧
      H.n p (-u / w) = levDiff l p (e : L) (a : L) ∧
      (∀ X Y Z : L, SamePoint l X ((a * y : Lˣ) : L) → SamePoint l Y (y : L) →
        SamePoint l Z ((y * e : Lˣ) : L) → IsAlgebraic l⟮X, Y⟯ Z) ∧
      (∀ X Y Z : L, IsNormalized l X Y Z → SamePoint l X ((a * y : Lˣ) : L) →
        SamePoint l Y (y : L) → SamePoint l Z ((y * e : Lˣ) : L) →
        H.c p u w = levDiff l p Y (y : L) - levDiff l p X ((a * y : Lˣ) : L)) := by
  have hs : -u / w ∉ H.k := H.notMem_neg_div h
  have hu0 : H.ψK u ≠ 0 := h.ne_zero 0
  have hw0 : H.ψK w ≠ 0 := h.ne_zero 1
  have hu : u ≠ 0 := fun h0 ↦ hu0 (by rw [h0, ψK_zero])
  have hw : w ≠ 0 := fun h0 ↦ hw0 (by rw [h0, ψK_zero])
  have hs0 : -u / w ≠ 0 := H.ne_zero_of_notMem hs
  have h1s : 1 - -u / w ∉ H.k := H.one_sub_notMem hs
  obtain ⟨N, a, y, e, ha, hy, he⟩ := exists_isVRep₃ p (H.ψK (-u / w)) (H.ψK w) (H.ψK (1 - -u / w))
  have hψu : H.ψK u = H.ψK (-u / w) + H.ψK w := by
    have : u = -((-u / w) * w) := by field_simp
    conv_lhs => rw [this]
    rw [ψK_neg, H.ψK_mul hs0 hw]
  have hψuw : H.ψK (u + w) = H.ψK w + H.ψK (1 - -u / w) := by
    have e' : u + w = w * (1 - -u / w) := by field_simp; ring
    rw [e', H.ψK_mul hw (H.ne_zero_of_notMem h1s)]
  have hru : IsVRep p (H.ψK u) N (a * y) :=
    ⟨ha.pos, ha.coprime, by rw [hψu, smul_add, ha.nsmul_eq, hy.nsmul_eq, cls_mul]⟩
  have hruw : IsVRep p (H.ψK (u + w)) N (y * e) :=
    ⟨ha.pos, ha.coprime, by rw [hψuw, smul_add, hy.nsmul_eq, he.nsmul_eq, cls_mul]⟩
  -- `s` and `w` are `ψ`-independent
  have hsw : VAlgIndep l ![H.ψK (-u / w), H.ψK w] := by
    have hψs : H.ψK (-u / w) = H.ψK u + -H.ψK w := by rw [hψu]; abel
    obtain ⟨hne, -, hpt'⟩ := pointV_add_ne hu0 (neg_ne_zero.2 hw0)
      (by rw [pointV_neg]; exact (vAlgIndep_pair_iff hu0 hw0).1 h)
    rw [pointV_neg, ← hψs] at hpt'
    rw [← hψs] at hne
    exact (vAlgIndep_pair_iff hne hw0).2 hpt'
  have hay : AlgebraicIndependent l ![(a : L), (y : L)] := ha.algebraicIndependent_pair p hy hsw
  have hea : SamePoint l (e : L) (a : L) := he.samePoint p ha (H.samePointV_one_sub hs)
  have hcol := H.isCollinearTriple_add p h
  have huw0 : H.ψK (u + w) ≠ 0 := H.ψK_ne_zero (H.add_notMem_of_vAlgIndep p h)
  have hsu : SamePoint l ((a * y : Lˣ) : L) (H.ρ p u : L) :=
    hru.samePoint p (H.isVRep_ρ p u) (samePointV_refl hu0)
  have hsw' : SamePoint l (y : L) (H.ρ p w : L) :=
    hy.samePoint p (H.isVRep_ρ p w) (samePointV_refl hw0)
  have hsuw : SamePoint l ((y * e : Lˣ) : L) (H.ρ p (u + w) : L) :=
    hruw.samePoint p (H.isVRep_ρ p (u + w)) (samePointV_refl huw0)
  refine ⟨N, a, y, e, ha, he, hay, hea, hsu.transcendental_left, hsuw.transcendental_left,
    levDiffV_eq p he ha, fun X Y Z hX hY hZ ↦ ?_, fun X Y Z hXYZ hX hY hZ ↦ ?_⟩
  · exact (hcol.of_samePoint (hX.trans hsu) (hY.trans hsw') (hZ.trans hsuw)).isAlgebraic
  · rw [c, levelTriple_eq_of_isNormalized p hXYZ (hX.trans hsu) (hY.trans hsw') (hZ.trans hsuw),
      SepEquiv.levDiff_right p ((H.isVRep_ρ p w).sepEquiv p hy) hY,
      SepEquiv.levDiff_right p ((H.isVRep_ρ p u).sepEquiv p hru) hX]

omit [PerfectField L] [IsRelAlgClosed l L] in
theorem mk_ne_zero {E : IntermediateField l L} {x : L} (hx : x ∈ E) (h0 : x ≠ 0) :
    (⟨x, hx⟩ : E) ≠ 0 :=
  fun h ↦ h0 (congrArg Subtype.val h)

/-- **Blueprint Lemma 6.2** (gauge), first case: if `n(s) > 0` for `s = -u/w`, then
`c(u, w) = -n(s)`. The triple `(A y^{p^i}, y, y e)` with `A = Frob^i(a)`, `i = n(s)`, is
normalized. -/
theorem c_eq_neg_n_of_pos {u w : K} (h : VAlgIndep l ![H.ψK u, H.ψK w])
    (hn : 0 < H.n p (-u / w)) : H.c p u w = -H.n p (-u / w) := by
  have : PerfectField l := IsRelAlgClosed.perfectField l L
  obtain ⟨N, a, y, e, -, -, hay, hea, hay_tr, hye_tr, hn_eq, halg, hc⟩ := H.gauge_setup p h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.n p (-u / w) = m := ⟨_, (Int.toNat_of_nonneg hn.le).symm⟩
  have hm0 : 0 < m := by omega
  rw [hm] at hn_eq ⊢
  have hy_tr : Transcendental l (y : L) := hay.transcendental 1
  obtain ⟨A, hA⟩ : ∃ A, A = frobZ L p m (a : L) := ⟨_, rfl⟩
  have hsep : SepEquiv l (e : L) A := by rw [hA]; exact (levDiff_eq_iff p hea).1 hn_eq.symm
  have hB : AlgebraicIndependent l ![A, (y : L)] := by
    have := algebraicIndependent_frobZ_pair p hay m 0
    rwa [frobZ_zero_apply, ← hA] at this
  have hAm : A ∈ model l ![A, (y : L)] := self_mem_model _ 0
  have hym : (y : L) ∈ model l ![A, (y : L)] := self_mem_model _ 1
  have hem : (e : L) ∈ model l ![A, (y : L)] := hsep.symm.mem_model hAm
  obtain ⟨c, hc0, hdc⟩ := hsep.symm.exists_modelD_eq_smul hAm (modelD_ne_zero_left hB)
  have hX : A * (y : L) ^ p ^ m = frobZ L p m ((a * y : Lˣ) : L) := by
    rw [Units.val_mul, map_mul, ← hA, frobZ_natCast_apply p m (y : L)]
  have hsX : SamePoint l (A * (y : L) ^ p ^ m) ((a * y : Lˣ) : L) := by
    rw [hX, samePoint_frobZ_left_iff]
    exact samePoint_refl hay_tr
  have hyp0 : (y : L) ^ p ^ m ≠ 0 := pow_ne_zero _ y.ne_zero
  have hnorm : IsNormalized l (A * (y : L) ^ p ^ m) (y : L) ((y * e : Lˣ) : L) := by
    refine isNormalized_of_coords hB (mul_mem hAm (pow_mem hym _)) hym
      (by rw [Units.val_mul]; exact mul_mem hym hem) (α₁ := ⟨_, pow_mem hym (p ^ m)⟩) (α₂ := 0)
      (β₁ := 0) (β₂ := 1) (γ₁ := ⟨y, hym⟩ * c) (γ₂ := ⟨e, hem⟩) ?_ ?_ ?_ ?_ ?_ ?_
      (halg _ _ _ hsX (samePoint_refl hy_tr) (samePoint_refl hye_tr))
    · rw [modelD_mul hAm (pow_mem hym _), modelD_pow_pow_of_pos p hym hm0, smul_zero, zero_add,
        zero_smul, add_zero]
    · rw [zero_smul, one_smul, zero_add]
    · rw [Units.val_mul, modelD_mul hym hem, hdc, smul_smul]
    · rw [mul_one, mul_zero, sub_zero]
      exact mk_ne_zero _ hyp0
    · rw [zero_mul, sub_zero]
      exact mul_ne_zero (mk_ne_zero _ hyp0) (mk_ne_zero _ e.ne_zero)
    · rw [zero_mul, one_mul, zero_sub, neg_ne_zero]
      exact mul_ne_zero (mk_ne_zero _ y.ne_zero) hc0
  rw [hc _ _ _ hnorm hsX (samePoint_refl hy_tr) (samePoint_refl hye_tr), levDiff_self p hy_tr, hX,
    levDiff_frobZ_left p (samePoint_refl hay_tr), levDiff_self p hay_tr]
  ring

/-- **Blueprint Lemma 6.2** (gauge), second case: if `n(s) < 0` for `s = -u/w`, then
`c(u, w) = 0`. With `j = -n(s)`, `α = Frob^{-j}(a)` and `η = Frob^{-j}(y)`, the triple
`(α η, η, η^{p^j} e)` is normalized. -/
theorem c_eq_zero_of_n_neg {u w : K} (h : VAlgIndep l ![H.ψK u, H.ψK w])
    (hn : H.n p (-u / w) < 0) : H.c p u w = 0 := by
  have : PerfectField l := IsRelAlgClosed.perfectField l L
  obtain ⟨N, a, y, e, -, -, hay, hea, hay_tr, hye_tr, hn_eq, halg, hc⟩ := H.gauge_setup p h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, H.n p (-u / w) = -(m : ℤ) := ⟨(-H.n p (-u / w)).toNat, by omega⟩
  have hm0 : 0 < m := by omega
  rw [hm] at hn_eq
  have hy_tr : Transcendental l (y : L) := hay.transcendental 1
  obtain ⟨α, hα⟩ : ∃ α, α = frobZ L p (-(m : ℤ)) (a : L) := ⟨_, rfl⟩
  obtain ⟨η, hη⟩ : ∃ η, η = frobZ L p (-(m : ℤ)) (y : L) := ⟨_, rfl⟩
  have hsep : SepEquiv l (e : L) α := by rw [hα]; exact (levDiff_eq_iff p hea).1 hn_eq.symm
  have hB : AlgebraicIndependent l ![α, η] := by
    rw [hα, hη]
    exact algebraicIndependent_frobZ_pair p hay _ _
  have hαm : α ∈ model l ![α, η] := self_mem_model _ 0
  have hηm : η ∈ model l ![α, η] := self_mem_model _ 1
  have hem : (e : L) ∈ model l ![α, η] := hsep.symm.mem_model hαm
  obtain ⟨c, hc0, hdc⟩ := hsep.symm.exists_modelD_eq_smul hαm (modelD_ne_zero_left hB)
  have hηy : η ^ p ^ m = (y : L) := by rw [hη]; exact frobZ_neg_natCast_pow p m (y : L)
  have hη0 : η ≠ 0 := fun h0 ↦ y.ne_zero (by
    rw [← hηy, h0, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)])
  have hα0 : α ≠ 0 := fun h0 ↦ a.ne_zero (by
    rw [← frobZ_neg_natCast_pow p m (a : L), ← hα, h0,
      zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)])
  have hX : α * η = frobZ L p (-(m : ℤ)) ((a * y : Lˣ) : L) := by
    rw [Units.val_mul, map_mul, hα, hη]
  have hZ : η ^ p ^ m * (e : L) = ((y * e : Lˣ) : L) := by rw [hηy, Units.val_mul]
  have hsX : SamePoint l (α * η) ((a * y : Lˣ) : L) := by
    rw [hX, samePoint_frobZ_left_iff]
    exact samePoint_refl hay_tr
  have hsY : SamePoint l η (y : L) := by
    rw [hη, samePoint_frobZ_left_iff]
    exact samePoint_refl hy_tr
  have hsZ : SamePoint l (η ^ p ^ m * (e : L)) ((y * e : Lˣ) : L) := by
    rw [hZ]
    exact samePoint_refl hye_tr
  have hηp0 : η ^ p ^ m ≠ 0 := pow_ne_zero _ hη0
  have hnorm : IsNormalized l (α * η) η (η ^ p ^ m * (e : L)) := by
    refine isNormalized_of_coords hB (mul_mem hαm hηm) hηm (mul_mem (pow_mem hηm _) hem)
      (α₁ := ⟨η, hηm⟩) (α₂ := ⟨α, hαm⟩) (β₁ := 0) (β₂ := 1)
      (γ₁ := ⟨η ^ p ^ m, pow_mem hηm _⟩ * c) (γ₂ := 0) ?_ ?_ ?_ ?_ ?_ ?_ (halg _ _ _ hsX hsY hsZ)
    · rw [modelD_mul hαm hηm, add_comm]
    · rw [zero_smul, one_smul, zero_add]
    · rw [modelD_mul (pow_mem hηm _) hem, modelD_pow_pow_of_pos p hηm hm0, smul_zero, add_zero,
        hdc, smul_smul, zero_smul, add_zero]
    · rw [mul_one, mul_zero, sub_zero]
      exact mk_ne_zero _ hη0
    · rw [mul_zero, zero_sub, neg_ne_zero]
      exact mul_ne_zero (mk_ne_zero _ hα0) (mul_ne_zero (mk_ne_zero _ hηp0) hc0)
    · rw [zero_mul, one_mul, zero_sub, neg_ne_zero]
      exact mul_ne_zero (mk_ne_zero _ hηp0) hc0
  rw [hc _ _ _ hnorm hsX hsY hsZ, hX, hη, levDiff_frobZ_left p (samePoint_refl hay_tr),
    levDiff_frobZ_left p (samePoint_refl hy_tr), levDiff_self p hay_tr, levDiff_self p hy_tr]
  ring

/-- **Blueprint Lemma 6.2** (gauge), exhaustiveness: if `n(s) = 0` then `n(1/s) ≥ 0` (because
`e / a` is separable over `l(a)`, blueprint line 459). -/
theorem n_inv_nonneg_of_n_eq_zero {s : K} (hs : s ∉ H.k) (hn : H.n p s = 0) :
    0 ≤ H.n p s⁻¹ := by
  obtain ⟨N, a, e, -, ha, he, -⟩ := exists_isVRep₃ p (H.ψK s) (H.ψK (1 - s)) 0
  have hea : SamePoint l (e : L) (a : L) := he.samePoint p ha (H.samePointV_one_sub hs)
  have hsep : SepEquiv l (e : L) (a : L) := by
    rw [← levDiff_eq_zero_iff p hea, ← levDiffV_eq p he ha]
    exact hn
  have hg : IsVRep p (H.ψK (1 - s) - H.ψK s) N (e * a⁻¹) :=
    ⟨he.pos, he.coprime, by rw [smul_sub, he.nsmul_eq, ha.nsmul_eq, cls_mul, cls_inv,
      sub_eq_add_neg]⟩
  have hga : SamePoint l ((e * a⁻¹ : Lˣ) : L) (a : L) :=
    hg.samePoint p ha (H.samePointV_one_sub_sub hs)
  rw [H.n_inv p hs, levDiffV_eq p hg ha, levDiff_nonneg_iff p hga]
  have h1 : (e : L) ∈ separableClosure l⟮(a : L)⟯ L := mem_separableClosure_iff.2 hsep.1
  have h2 : (a : L)⁻¹ ∈ separableClosure l⟮(a : L)⟯ L :=
    mem_separableClosure_iff.2 (isSeparable_algebraMap
      (⟨(a : L)⁻¹, inv_mem (mem_adjoin_simple_self l (a : L))⟩ : l⟮(a : L)⟯))
  rw [Units.val_mul, Units.val_inv_eq_inv_val, ← mem_separableClosure_iff]
  exact mul_mem h1 h2

/-- **Blueprint Lemma 6.2** (gauge), third case: if `n(s) = n(1/s) = 0` for `s = -u/w`, then
`c(u, w) = 0`: the triple `(a y, y, y e)` is normalized (as `d(e/a) ≠ 0`). -/
theorem c_eq_zero_of_n_eq_zero {u w : K} (h : VAlgIndep l ![H.ψK u, H.ψK w])
    (hn : H.n p (-u / w) = 0) (hn' : H.n p (-u / w)⁻¹ = 0) : H.c p u w = 0 := by
  have : PerfectField l := IsRelAlgClosed.perfectField l L
  obtain ⟨N, a, y, e, ha, he, hay, hea, hay_tr, hye_tr, hn_eq, halg, hc⟩ := H.gauge_setup p h
  have hs := H.notMem_neg_div h
  rw [hn] at hn_eq
  have hy_tr : Transcendental l (y : L) := hay.transcendental 1
  have hsep : SepEquiv l (e : L) (a : L) := (levDiff_eq_zero_iff p hea).1 hn_eq.symm
  -- `g = e / a ≈ a`
  have hg : IsVRep p (H.ψK (1 - -u / w) - H.ψK (-u / w)) N (e * a⁻¹) :=
    ⟨he.pos, he.coprime, by rw [smul_sub, he.nsmul_eq, ha.nsmul_eq, cls_mul, cls_inv,
      sub_eq_add_neg]⟩
  have hga : SamePoint l ((e * a⁻¹ : Lˣ) : L) (a : L) :=
    hg.samePoint p ha (H.samePointV_one_sub_sub hs)
  have hsepg : SepEquiv l ((e * a⁻¹ : Lˣ) : L) (a : L) := by
    rw [← levDiff_eq_zero_iff p hga, ← levDiffV_eq p hg ha, ← H.n_inv p hs]
    exact hn'
  have ham : (a : L) ∈ model l ![(a : L), (y : L)] := self_mem_model _ 0
  have hym : (y : L) ∈ model l ![(a : L), (y : L)] := self_mem_model _ 1
  have hem : (e : L) ∈ model l ![(a : L), (y : L)] := hsep.symm.mem_model ham
  have hgm : ((e * a⁻¹ : Lˣ) : L) ∈ model l ![(a : L), (y : L)] := hsepg.symm.mem_model ham
  obtain ⟨c, hc0, hdc⟩ := hsep.symm.exists_modelD_eq_smul ham (modelD_ne_zero_left hay)
  obtain ⟨c', hc'0, hdc'⟩ := hsepg.symm.exists_modelD_eq_smul ham (modelD_ne_zero_left hay)
  -- `e = g a`, hence `c = g + a c'`
  have hE : (⟨e, hem⟩ : model l ![(a : L), (y : L)]) = ⟨_, hgm⟩ * ⟨a, ham⟩ := by
    apply Subtype.ext
    simp
  have hcc : c = ⟨_, hgm⟩ + ⟨a, ham⟩ * c' := by
    have he_eq : (e : L) = ((e * a⁻¹ : Lˣ) : L) * (a : L) := by simp
    have key := modelD_mul hgm ham
    rw [← he_eq, hdc, hdc', smul_smul, ← add_smul] at key
    exact smul_left_injective _ (modelD_ne_zero_left hay) key
  have hnorm : IsNormalized l ((a * y : Lˣ) : L) (y : L) ((y * e : Lˣ) : L) := by
    refine isNormalized_of_coords hay (by rw [Units.val_mul]; exact mul_mem ham hym) hym
      (by rw [Units.val_mul]; exact mul_mem hym hem) (α₁ := ⟨y, hym⟩) (α₂ := ⟨a, ham⟩)
      (β₁ := 0) (β₂ := 1) (γ₁ := ⟨y, hym⟩ * c) (γ₂ := ⟨e, hem⟩) ?_ ?_ ?_ ?_ ?_ ?_
      (halg _ _ _ (samePoint_refl hay_tr) (samePoint_refl hy_tr) (samePoint_refl hye_tr))
    · rw [Units.val_mul, modelD_mul ham hym, add_comm]
    · rw [zero_smul, one_smul, zero_add]
    · rw [Units.val_mul, modelD_mul hym hem, hdc, smul_smul]
    · rw [mul_one, mul_zero, sub_zero]
      exact mk_ne_zero _ y.ne_zero
    · have : (⟨y, hym⟩ : model l ![(a : L), (y : L)]) * ⟨e, hem⟩ - ⟨a, ham⟩ * (⟨y, hym⟩ * c) =
          -(⟨y, hym⟩ * ⟨a, ham⟩ * ⟨a, ham⟩ * c') := by
        rw [hcc, hE]
        ring
      rw [this, neg_ne_zero]
      exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mk_ne_zero _ y.ne_zero)
        (mk_ne_zero _ a.ne_zero)) (mk_ne_zero _ a.ne_zero)) hc'0
    · rw [zero_mul, one_mul, zero_sub, neg_ne_zero]
      exact mul_ne_zero (mk_ne_zero _ y.ne_zero) hc0
  rw [hc _ _ _ hnorm (samePoint_refl hay_tr) (samePoint_refl hy_tr) (samePoint_refl hye_tr),
    levDiff_self p hay_tr, levDiff_self p hy_tr, sub_zero]

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
