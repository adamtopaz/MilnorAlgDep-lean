module

public import MilnorAlgDep.CharP.Models
public import MilnorAlgDep.CharP.Normalized
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Levels of elements of `V`, and the setting of Section 6 in characteristic `p`

Blueprint Section 6.1 ("Reductions and notation"), lines 406-414, with `Γ = ℤ`.

Throughout, `L` is a perfect field of characteristic `p` (a prime) and `l ⊆ L` is relatively
algebraically closed.

## Levels and heights of elements of `V`

Blueprint (V2): every `v ∈ V_{L|l}` has a representative `(N, a)` with `N` prime to `p`
(`MilnorAlgDep.IsVRep`); we fix one, `(vRepNat p v, vRep p v)` (for `v = 0` it is `(1, 1)`).
As in `MilnorAlgDep.CharP.Levels` we never form the torsor of levels: we only use level
*differences* `lev v - lev w = levDiffV p v w ∈ ℤ` for `v, w` in the same point
(`MilnorAlgDep.SamePointV`), defined through the chosen representatives and independent of the
choice (`levDiffV_eq`, from `levDiff_pow_left` and `levDiff_algebraMap_mul_left`). Likewise the
height `hgt_A(v)` of `v ≠ 0` with respect to a transcendence basis `B` is `hgtV p B v`, the height
of a representative (`hgtV_eq`).

The behaviour under scalars is `levDiffV_smul_left`: `lev (q • v) = lev v + v_p(q)` for
`q ∈ ℚˣ`, which contains `lev (p • v) = lev v + 1`, `lev (-v) = lev v` and `lev (N • v) = lev v`
for `N` prime to `p` (blueprint line 407).

## The hypotheses of Section 6

`MilnorAlgDep.CharPHyp K l L` bundles `k`, `ψ`, (A1)-(A3) with `d = 3` (the three elements of (A3)
made explicit) and (A4) (`ringChar K ≠ 0`), as `MilnorAlgDep.Char0Hyp` does in characteristic
`0`. `CharPHyp.ψK` is `ψ` extended to `K` by `ψK 0 = 0`, and `CharPHyp.ρ p x = vRep p (ψK x)` is
the chosen representative of `ψ(x)`. The blueprint writes `Q_x` for `pointV l (H.ψK x)`.

## Equation `eq:sum` and its consequences (lines 409-414)

* `CharPHyp.ψK_add`, `CharPHyp.pointV_ψK_one_sub_neg_div`: `eq:sum`.
* `CharPHyp.isCollinearTriple_add`: for `ψ`-independent `x, y`, the points `Q_x, Q_y, Q_{x+y}`
  are three distinct collinear points.
* `CharPHyp.isAlgebraic_ρ_add`: in general `Q_{x+y}` lies on the line `⟨Q_x, Q_y⟩`.
* `CharPHyp.pointV_ψK_one_sub`: `Q_{1-x} = Q_x` (A2).

## `ψ`-independence

Bookkeeping lemmas on algebraic independence in `V` used in Step A (Lemma 6.3 and
Proposition 6.1): `VAlgIndep.add_add₃`, `VAlgIndep.add_of_mem_pointGroup`,
`CharPHyp.vAlgIndep_add_of_vAlgIndep₃`, `CharPHyp.exists_vAlgIndep₃`,
`CharPHyp.exists_vAlgIndep_pair`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf IntermediateField

variable {l L : Type*} [Field l] [Field L] [Algebra l L] {ι : Type*}

/-! ### Representatives prime to `p` -/

section Rep

variable (p : ℕ)

/-- Blueprint (V2): `(N, a)` is a *representative* of `v ∈ V_{L|l}` with `N ≥ 1` prime to `p`:
`N • v = [a]`. (For `v ≠ 0` this forces `a ∉ l`, see `IsVRep.transcendental`.) -/
structure IsVRep (v : V l L) (N : ℕ) (a : Lˣ) : Prop where
  pos : 0 < N
  coprime : N.Coprime p
  nsmul_eq : N • v = cls (constUnits l L) (.ofMul a)

/-- `(1, a)` is a representative of `[a]`. -/
theorem isVRep_cls (a : Lˣ) : IsVRep p (cls (constUnits l L) (.ofMul a)) 1 a :=
  ⟨one_pos, Nat.coprime_one_left p, one_nsmul _⟩

variable [Fact p.Prime] [CharP L p] [PerfectField L]

/-- Blueprint (V2), perfect case: every `v` has a representative prime to `p` (for `v = 0`, take
`(1, 1)`). -/
theorem exists_isVRep (v : V l L) : ∃ (N : ℕ) (a : Lˣ), IsVRep p v N a := by
  by_cases hv : v = 0
  · exact ⟨1, 1, one_pos, Nat.coprime_one_left p, by rw [hv, smul_zero, cls_one]⟩
  obtain ⟨N, a, hN, hcop, -, h⟩ := V.exists_rep_coprime hv
  rw [ringExpChar.eq L p] at hcop
  exact ⟨N, a, hN, hcop, h⟩

/-- The chosen denominator of the representative of `v` prime to `p`. -/
noncomputable def vRepNat (v : V l L) : ℕ :=
  (exists_isVRep p v).choose

/-- The chosen representative of `v` prime to `p`: `vRepNat p v • v = [vRep p v]`. -/
noncomputable def vRep (v : V l L) : Lˣ :=
  (exists_isVRep p v).choose_spec.choose

theorem isVRep_vRep (v : V l L) : IsVRep p v (vRepNat p v) (vRep p v) :=
  (exists_isVRep p v).choose_spec.choose_spec

end Rep

section SamePointV

variable (l) in
/-- `v, w ∈ V l L` are non-zero and lie in the same point, `Q_v = Q_w` (blueprint (V3)). -/
def SamePointV (v w : V l L) : Prop :=
  v ≠ 0 ∧ w ≠ 0 ∧ pointV l v = pointV l w

variable {u v w : V l L}

theorem SamePointV.ne_zero_left (h : SamePointV l v w) : v ≠ 0 :=
  h.1

theorem SamePointV.ne_zero_right (h : SamePointV l v w) : w ≠ 0 :=
  h.2.1

theorem SamePointV.pointV_eq (h : SamePointV l v w) : pointV l v = pointV l w :=
  h.2.2

theorem samePointV_refl (hv : v ≠ 0) : SamePointV l v v :=
  ⟨hv, hv, rfl⟩

theorem SamePointV.symm (h : SamePointV l v w) : SamePointV l w v :=
  ⟨h.2.1, h.1, h.2.2.symm⟩

theorem SamePointV.trans (h₁ : SamePointV l u v) (h₂ : SamePointV l v w) : SamePointV l u w :=
  ⟨h₁.1, h₂.2.1, h₁.2.2.trans h₂.2.2⟩

theorem SamePointV.smul_left {q : ℚ} (hq : q ≠ 0) (h : SamePointV l v w) :
    SamePointV l (q • v) w :=
  ⟨smul_ne_zero hq h.1, h.2.1, (pointV_smul hq).trans h.2.2⟩

theorem SamePointV.smul_right {q : ℚ} (hq : q ≠ 0) (h : SamePointV l v w) :
    SamePointV l v (q • w) :=
  (h.symm.smul_left hq).symm

theorem SamePointV.neg_left (h : SamePointV l v w) : SamePointV l (-v) w :=
  ⟨neg_ne_zero.2 h.1, h.2.1, (pointV_neg v).trans h.2.2⟩

/-- Non-zero `v, w` are in the same point iff they are algebraically dependent (V3). -/
theorem samePointV_iff_not_vAlgIndep [IsRelAlgClosed l L] (hv : v ≠ 0) (hw : w ≠ 0) :
    SamePointV l v w ↔ ¬ VAlgIndep l ![v, w] := by
  rw [vAlgIndep_pair_iff hv hw, not_not]
  exact ⟨fun h ↦ h.2.2, fun h ↦ ⟨hv, hw, h⟩⟩

end SamePointV

section RepLemmas

variable (p : ℕ) {v w : V l L} {N M : ℕ} {a b : Lˣ}

theorem IsVRep.pointV_eq (h : IsVRep p v N a) : pointV l v = point l (a : L) :=
  pointV_eq_point h.pos h.nsmul_eq

variable [IsRelAlgClosed l L]

/-- A representative of a non-zero element is transcendental over `l`. -/
theorem IsVRep.transcendental (h : IsVRep p v N a) (hv : v ≠ 0) : Transcendental l (a : L) :=
  IsRelAlgClosed.transcendental (V.not_mem_range_of_nsmul_eq_cls hv h.pos h.nsmul_eq)

/-- A representative of `0` is constant. -/
theorem IsVRep.mem_range_of_eq_zero (h : IsVRep p v N a) (hv : v = 0) :
    (a : L) ∈ (algebraMap l L).range := by
  rw [← V.cls_eq_zero_iff', ← h.nsmul_eq, hv, smul_zero]

/-- Representatives of elements in the same point lie in the same point. -/
theorem IsVRep.samePoint (hv : IsVRep p v N a) (hw : IsVRep p w M b) (h : SamePointV l v w) :
    SamePoint l (a : L) (b : L) :=
  ⟨hv.transcendental p h.1, hw.transcendental p h.2.1,
    hv.pointV_eq.symm.trans (h.2.2.trans hw.pointV_eq)⟩

variable [CharP L p]

/-- Two representatives (prime to `p`) of the same element are `≈`-equivalent; in particular
they have the same level (blueprint line 406). -/
theorem IsVRep.sepEquiv {a' : Lˣ} {N' : ℕ} (h : IsVRep p v N a) (h' : IsVRep p v N' a') :
    SepEquiv l (a : L) (a' : L) := by
  sorry

variable [Fact p.Prime] [PerfectField L]

theorem SamePointV.samePoint_vRep (h : SamePointV l v w) :
    SamePoint l (vRep p v : L) (vRep p w : L) :=
  (isVRep_vRep p v).samePoint p (isVRep_vRep p w) h

omit [IsRelAlgClosed l L] in
/-- `v` is algebraically independent iff its chosen representatives are. -/
theorem vAlgIndep_iff_algebraicIndependent_vRep {v : ι → V l L} :
    VAlgIndep l v ↔ AlgebraicIndependent l fun i ↦ (vRep p (v i) : L) :=
  VAlgIndep.iff_of_nsmul_eq_cls (fun i ↦ (isVRep_vRep p (v i)).pos)
    (fun i ↦ (isVRep_vRep p (v i)).nsmul_eq)

end RepLemmas

/-! ### Level differences -/

section LevDiffV

variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L]

/-- Blueprint Section 6.1 (line 406), element-wise: the level difference
`lev(v) - lev(w) ∈ ℤ` of `v, w ∈ V_{L|l}` in the same point, defined as the level difference of
the chosen representatives prime to `p`. It does not depend on the representatives
(`levDiffV_eq`). Meaningful when `SamePointV l v w`; otherwise it is `0`. -/
noncomputable def levDiffV (v w : V l L) : ℤ :=
  levDiff l p (vRep p v : L) (vRep p w : L)

variable [IsRelAlgClosed l L] {u v w : V l L} {N M : ℕ} {a b : Lˣ}

/-- Blueprint line 406: `lev(v) - lev(w) = lev(a) - lev(b)` for any representatives `(N, a)` of
`v` and `(M, b)` of `w` prime to `p` (well-definedness of `lev(v)`). -/
theorem levDiffV_eq (hv : IsVRep p v N a) (hw : IsVRep p w M b) :
    levDiffV p v w = levDiff l p (a : L) (b : L) := by
  sorry

theorem levDiffV_self (hv : v ≠ 0) : levDiffV p v v = 0 :=
  levDiff_self p ((isVRep_vRep p v).transcendental p hv)

theorem levDiffV_swap (h : SamePointV l v w) : levDiffV p w v = -levDiffV p v w :=
  levDiff_swap p (h.samePoint_vRep p)

theorem levDiffV_add_levDiffV (h₁ : SamePointV l u v) (h₂ : SamePointV l v w) :
    levDiffV p u v + levDiffV p v w = levDiffV p u w :=
  levDiff_add_levDiff p (h₁.samePoint_vRep p) (h₂.samePoint_vRep p)

/-- Blueprint line 407, general form: `lev(q • v) = lev(v) + v_p(q)` for `q ∈ ℚˣ`. This contains
`lev(p • v) = lev(v) + 1`, `lev(-v) = lev(v)` and `lev(N • v) = lev(v)` for `N` prime to `p`. -/
theorem levDiffV_smul_left {q : ℚ} (hq : q ≠ 0) (h : SamePointV l v w) :
    levDiffV p (q • v) w = levDiffV p v w + padicValRat p q := by
  sorry

theorem levDiffV_smul_right {q : ℚ} (hq : q ≠ 0) (h : SamePointV l v w) :
    levDiffV p v (q • w) = levDiffV p v w - padicValRat p q := by
  rw [levDiffV_swap p (h.smul_right hq).symm, levDiffV_smul_left p hq h.symm,
    levDiffV_swap p h]
  ring

/-- Blueprint line 407: `lev(-v) = lev(v)`. -/
theorem levDiffV_neg_left (h : SamePointV l v w) : levDiffV p (-v) w = levDiffV p v w := by
  have := levDiffV_smul_left p (q := -1) (by norm_num) h
  rwa [neg_one_smul, padicValRat.neg, padicValRat.one, add_zero] at this

/-- Blueprint line 406: `lev(N • v) = lev(v)` for `N` prime to `p`. -/
theorem levDiffV_nsmul_left {N : ℕ} (hN : N.Coprime p) (hN0 : 0 < N) (h : SamePointV l v w) :
    levDiffV p (N • v) w = levDiffV p v w := by
  have := levDiffV_smul_left p (q := N) (Nat.cast_ne_zero.2 hN0.ne') h
  rwa [Nat.cast_smul_eq_nsmul, padicValRat.of_nat, multiplicity_eq_zero_of_not_dvd
    ((Nat.Prime.coprime_iff_not_dvd Fact.out).1 hN.symm), Nat.cast_zero, add_zero] at this

/-- Blueprint line 407: `lev(p • v) = lev(v) + 1`. -/
theorem levDiffV_p_nsmul_left (h : SamePointV l v w) :
    levDiffV p (p • v) w = levDiffV p v w + 1 := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have := levDiffV_smul_left p hp h
  rwa [Nat.cast_smul_eq_nsmul, padicValRat.self (Fact.out : p.Prime).one_lt] at this

end LevDiffV

/-! ### Heights -/

section HgtV

variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L]

/-- Blueprint Section 6.3 (line 509): the height `ht(v) = ht_B(lev v) ∈ ℤ` of `v ∈ V_{L|l}` with
respect to a transcendence basis `B` of `L / l`, i.e. the height `hgt l p B a` of the chosen
representative `a` of `v`; it does not depend on the representative (`hgtV_eq`). Meaningful for
`v ≠ 0` and `B` a transcendence basis. -/
noncomputable def hgtV (B : ι → L) (v : V l L) : ℤ :=
  hgt l p B (vRep p v : L)

variable [IsRelAlgClosed l L] {B : ι → L} {v w : V l L} {N : ℕ} {a : Lˣ}

/-- The height of `v ≠ 0` is the height of any representative prime to `p`. -/
theorem hgtV_eq (hB : IsTranscendenceBasis l B) (hv : IsVRep p v N a) (hv0 : v ≠ 0) :
    hgtV p B v = hgt l p B (a : L) := by
  sorry

/-- `ht(v) - ht(w) = lev(v) - lev(w)` for `v, w` in the same point. -/
theorem hgtV_sub_hgtV (hB : IsTranscendenceBasis l B) (h : SamePointV l v w) :
    hgtV p B v - hgtV p B w = levDiffV p v w :=
  hgt_sub_hgt p hB (h.samePoint_vRep p)

/-- `ht(q • v) = ht(v) + v_p(q)`; in particular `ht(p • v) = ht(v) + 1` (blueprint lines 525
and 618). -/
theorem hgtV_smul (hB : IsTranscendenceBasis l B) (hv : v ≠ 0) {q : ℚ} (hq : q ≠ 0) :
    hgtV p B (q • v) = hgtV p B v + padicValRat p q := by
  have h := samePointV_refl (l := l) hv
  have e := hgtV_sub_hgtV p hB (h.smul_left hq)
  rw [levDiffV_smul_left p hq h, levDiffV_self p hv, zero_add] at e
  linarith

theorem hgtV_neg (hB : IsTranscendenceBasis l B) (hv : v ≠ 0) : hgtV p B (-v) = hgtV p B v := by
  have := hgtV_smul p hB hv (q := -1) (by norm_num)
  rwa [neg_one_smul, padicValRat.neg, padicValRat.one, add_zero] at this

theorem hgtV_p_nsmul (hB : IsTranscendenceBasis l B) (hv : v ≠ 0) :
    hgtV p B (p • v) = hgtV p B v + 1 := by
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have := hgtV_smul p hB hv hp
  rwa [Nat.cast_smul_eq_nsmul, padicValRat.self (Fact.out : p.Prime).one_lt] at this

theorem hgtV_pow_nsmul (hB : IsTranscendenceBasis l B) (hv : v ≠ 0) (j : ℕ) :
    hgtV p B (p ^ j • v) = hgtV p B v + j := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hpj : p ^ j • v ≠ 0 := by
      rw [← Nat.cast_smul_eq_nsmul ℚ]
      exact smul_ne_zero (Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)) hv
    rw [pow_succ', mul_smul, hgtV_p_nsmul p hB hpj, ih]
    push_cast
    ring

end HgtV

/-! ### Two lemmas on algebraic independence in `V` -/

section VAlgIndep

variable [IsRelAlgClosed l L]

-- TODO(move): these are Foundations lemmas (`Foundations/AlgIndep.lean`).

/-- A unimodular change of variables preserves algebraic independence of three elements of `V`:
if `u, v, w` are algebraically independent, so are `u + v + w, v + w, w` (used in the proof of
Proposition 6.1, with `ψ(s s' z), ψ(-s' z), ψ(z)`). -/
theorem VAlgIndep.add_add₃ {u v w : V l L} (h : VAlgIndep l ![u, v, w]) :
    VAlgIndep l ![u + v + w, v + w, w] := by
  sorry

/-- If `v, w` are algebraically independent and `v'` lies in `G_{Q_v}`, then `v, w + v'` are
algebraically independent (used in the proof of Proposition 6.1). -/
theorem VAlgIndep.add_of_mem_pointGroup {v w v' : V l L} (h : VAlgIndep l ![v, w])
    (hv' : v' ∈ pointGroup (pointV l v)) : VAlgIndep l ![v, w + v'] := by
  sorry

end VAlgIndep

/-! ### The hypotheses of Section 6 -/

/-- The hypotheses of Theorem A in the case `char L > 0` (so `d = 3`), after the reduction to
perfect fields (blueprint Section 6.1): `k ⊆ K`, `ψ : Kˣ → V_{L|l}` with (A1), (A2), (A3) (the
three elements `x i` made explicit) and (A4) (`K` has positive characteristic). The fields `K`,
`L` are assumed perfect, `L` of characteristic `p` and `l` relatively algebraically closed, as
separate type class arguments. -/
structure CharPHyp (K l L : Type*) [Field K] [Field l] [Field L] [Algebra l L] where
  /-- The subfield `k ⊆ K`. -/
  k : Subfield K
  /-- The homomorphism `ψ : Kˣ → V_{L|l}`. -/
  ψ : Additive Kˣ →+ V l L
  /-- (A1): `ker ψ = kˣ`. -/
  A1 : ∀ x : Kˣ, ψ (.ofMul x) = 0 ↔ (x : K) ∈ k
  /-- (A2): `ψ x`, `ψ (1 - x)` are algebraically dependent for `x ∉ k`. -/
  A2 : ∀ x y : Kˣ, (x : K) + y = 1 → (x : K) ∉ k → ¬ VAlgIndep l ![ψ (.ofMul x), ψ (.ofMul y)]
  /-- The three elements of (A3). -/
  x : Fin 3 → Kˣ
  /-- (A3) with `d = 3`: `ψ (x 0), ψ (x 1), ψ (x 2)` are algebraically independent. -/
  A3 : VAlgIndep l fun i ↦ ψ (.ofMul (x i))
  /-- (A4): `K` has positive characteristic. -/
  A4 : ringChar K ≠ 0

namespace CharPHyp

variable {K l L : Type*} [Field K] [Field l] [Field L] [Algebra l L] (H : CharPHyp K l L)

/-! ### `ψ` on `K` -/

open Classical in
/-- `ψ` extended to `K` by `ψ 0 = 0`. -/
noncomputable def ψK (x : K) : V l L :=
  if hx : x = 0 then 0 else H.ψ (.ofMul (Units.mk0 x hx))

@[simp]
theorem ψK_zero : H.ψK 0 = 0 := by
  simp [ψK]

theorem ψK_of_ne_zero {x : K} (hx : x ≠ 0) : H.ψK x = H.ψ (.ofMul (Units.mk0 x hx)) := by
  simp [ψK, hx]

theorem ψK_units (x : Kˣ) : H.ψK x = H.ψ (.ofMul x) := by
  rw [H.ψK_of_ne_zero x.ne_zero, Units.mk0_val]

theorem ψK_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : H.ψK (x * y) = H.ψK x + H.ψK y := by
  rw [H.ψK_of_ne_zero hx, H.ψK_of_ne_zero hy, H.ψK_of_ne_zero (mul_ne_zero hx hy),
    Units.mk0_mul _ _ (mul_ne_zero hx hy), ofMul_mul, map_add]

@[simp]
theorem ψK_one : H.ψK 1 = 0 := by
  rw [← Units.val_one, ψK_units, ofMul_one, map_zero]

theorem ψK_inv (x : K) : H.ψK x⁻¹ = -H.ψK x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have := H.ψK_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, ψK_one] at this
  exact eq_neg_of_add_eq_zero_right this.symm

theorem ψK_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) : H.ψK (x / y) = H.ψK x - H.ψK y := by
  rw [div_eq_mul_inv, H.ψK_mul hx (inv_ne_zero hy), ψK_inv, sub_eq_add_neg]

theorem ψK_pow (x : K) (n : ℕ) : H.ψK (x ^ n) = n • H.ψK x := by
  induction n with
  | zero => rw [pow_zero, zero_smul, ψK_one]
  | succ n ih =>
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    rw [pow_succ, H.ψK_mul (pow_ne_zero n hx) hx, ih, succ_nsmul]

theorem ψK_eq_zero_iff {x : K} : H.ψK x = 0 ↔ x ∈ H.k := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [zero_mem]
  · rw [H.ψK_of_ne_zero hx, H.A1, Units.val_mk0]

theorem ψK_ne_zero {x : K} (hx : x ∉ H.k) : H.ψK x ≠ 0 :=
  fun h ↦ hx (H.ψK_eq_zero_iff.1 h)

theorem ψK_neg_one : H.ψK (-1) = 0 :=
  H.ψK_eq_zero_iff.2 (neg_mem (one_mem _))

@[simp]
theorem ψK_neg (x : K) : H.ψK (-x) = H.ψK x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [neg_eq_neg_one_mul, H.ψK_mul (neg_ne_zero.2 one_ne_zero) hx, ψK_neg_one, zero_add]

/-- `ψ(c x) = ψ(x)` for `c ∈ kˣ` (blueprint line 403). -/
theorem ψK_mul_of_mem {c x : K} (hc : c ∈ H.k) (hc0 : c ≠ 0) : H.ψK (c * x) = H.ψK x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  rw [H.ψK_mul hc0 hx, H.ψK_eq_zero_iff.2 hc, zero_add]

theorem ne_zero_of_notMem {x : K} (hx : x ∉ H.k) : x ≠ 0 := by
  rintro rfl
  exact hx (zero_mem _)

theorem one_sub_notMem {x : K} (hx : x ∉ H.k) : 1 - x ∉ H.k := fun h ↦
  hx (by simpa using sub_mem (one_mem H.k) h)

theorem inv_notMem {x : K} (hx : x ∉ H.k) : x⁻¹ ∉ H.k := fun h ↦
  hx (by simpa using inv_mem h)

theorem neg_notMem {x : K} (hx : x ∉ H.k) : -x ∉ H.k := fun h ↦
  hx (by simpa using neg_mem h)

/-- (A3) for `ψK`. -/
theorem vAlgIndep_x : VAlgIndep l fun i ↦ H.ψK (H.x i) := by
  simpa only [ψK_units] using H.A3

theorem x_notMem (i : Fin 3) : (H.x i : K) ∉ H.k := fun h ↦
  H.vAlgIndep_x.ne_zero i (H.ψK_eq_zero_iff.2 h)

/-! ### The chosen representatives -/

section Rep

variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L]

/-- The chosen representative (prime to `p`) of `ψ(x)`: `vRepNat p (ψK x) • ψK x = [ρ p x]`. -/
noncomputable def ρ (x : K) : Lˣ :=
  vRep p (H.ψK x)

theorem isVRep_ρ (x : K) : IsVRep p (H.ψK x) (vRepNat p (H.ψK x)) (H.ρ p x) :=
  isVRep_vRep p _

theorem pointV_eq_point_ρ (x : K) : pointV l (H.ψK x) = point l (H.ρ p x : L) :=
  (H.isVRep_ρ p x).pointV_eq p

/-- `ψ(-x) = ψ(x)`, so they have the same representative. -/
theorem ρ_neg (x : K) : H.ρ p (-x) = H.ρ p x := by
  rw [ρ, ρ, ψK_neg]

variable [IsRelAlgClosed l L]

theorem transcendental_ρ {x : K} (hx : x ∉ H.k) : Transcendental l (H.ρ p x : L) :=
  (H.isVRep_ρ p x).transcendental p (H.ψK_ne_zero hx)

end Rep

/-! ### (A2) and equation `eq:sum` -/

section Sum

/-- Blueprint equation `eq:sum`, first part: `ψ(x + y) = ψ(y) + ψ(1 - (-x/y))`. -/
theorem ψK_add {x y : K} (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    H.ψK (x + y) = H.ψK y + H.ψK (1 - -x / y) := by
  have e : x + y = y * (1 - -x / y) := by field_simp; ring
  have h1 : 1 - -x / y ≠ 0 := by
    intro h
    rw [h, mul_zero] at e
    exact hxy e
  rw [e, H.ψK_mul hy h1]

variable [IsRelAlgClosed l L]

/-- (A2) and (V3): for `x ∉ k`, `Q_{1 - x} = Q_x` (blueprint line 414). -/
theorem pointV_ψK_one_sub {x : K} (hx : x ∉ H.k) :
    pointV l (H.ψK (1 - x)) = pointV l (H.ψK x) := by
  have hx0 := H.ne_zero_of_notMem hx
  have h1x0 := H.ne_zero_of_notMem (H.one_sub_notMem hx)
  have hdep := H.A2 (Units.mk0 x hx0) (Units.mk0 (1 - x) h1x0) (by simp) hx
  rw [← H.ψK_of_ne_zero, ← H.ψK_of_ne_zero, vAlgIndep_pair_iff (H.ψK_ne_zero hx)
    (H.ψK_ne_zero (H.one_sub_notMem hx)), not_not] at hdep
  exact hdep.symm

/-- Blueprint equation `eq:sum`, second part: for `x / y ∉ k`, `ψ(1 - (-x/y))` is a non-zero
element of `G_{Q_{x/y}}`. -/
theorem pointV_ψK_one_sub_neg_div {x y : K} (hxy : x / y ∉ H.k) :
    H.ψK (1 - -x / y) ≠ 0 ∧ pointV l (H.ψK (1 - -x / y)) = pointV l (H.ψK (x / y)) := by
  have h : -x / y ∉ H.k := by rw [neg_div]; exact H.neg_notMem hxy
  refine ⟨H.ψK_ne_zero (H.one_sub_notMem h), ?_⟩
  rw [H.pointV_ψK_one_sub h, neg_div, ψK_neg]

variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L]

/-- Consequence of `eq:sum` (blueprint lines 412-413): if `x, y` are `ψ`-independent, then
`Q_x, Q_y, Q_{x+y}` are three distinct collinear points; in terms of the chosen representatives,
`(ρ x, ρ y, ρ (x + y))` is a collinear triple. In particular `ψ(x + y) ≠ 0`
(`add_notMem_of_vAlgIndep`). -/
theorem isCollinearTriple_add {x y : K} (h : VAlgIndep l ![H.ψK x, H.ψK y]) :
    IsCollinearTriple l (H.ρ p x : L) (H.ρ p y : L) (H.ρ p (x + y) : L) := by
  sorry

include p in
theorem add_notMem_of_vAlgIndep {x y : K} (h : VAlgIndep l ![H.ψK x, H.ψK y]) :
    x + y ∉ H.k := by
  intro hk
  have h3 := (H.isCollinearTriple_add p h).transcendental₃
  have h0 : H.ψK (x + y) = 0 := H.ψK_eq_zero_iff.2 hk
  obtain ⟨c, hc⟩ := (H.isVRep_ρ p (x + y)).mem_range_of_eq_zero p h0
  exact h3 (hc ▸ isAlgebraic_algebraMap c)

/-- Consequence of `eq:sum`, in general: `Q_{x+y}` lies on the line `⟨Q_x, Q_y⟩`, i.e. the
representative of `ψ(x + y)` is algebraic over `l(ρ x, ρ y)`. (If `x / y ∈ k`, then
`ψ(x + y) = ψ(y)`.) This is how `eq:sum` is used in the proof of Lemma 6.3. -/
theorem isAlgebraic_ρ_add {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    IsAlgebraic l⟮(H.ρ p x : L), (H.ρ p y : L)⟯ (H.ρ p (x + y) : L) := by
  sorry

end Sum

/-! ### `ψ`-independence -/

section Indep

variable [IsRelAlgClosed l L]

/-- If `u, w, z` are `ψ`-independent, then so are `u + w` and `z` (as `Q_{u+w}` lies on
`⟨Q_u, Q_w⟩`, which does not contain `Q_z`). Used in the proof of Lemma 6.3. -/
theorem vAlgIndep_add_of_vAlgIndep₃ {u w z : K} (h : VAlgIndep l ![H.ψK u, H.ψK w, H.ψK z]) :
    VAlgIndep l ![H.ψK (u + w), H.ψK z] := by
  sorry

/-- Blueprint, proof of Proposition 6.1 (line 470): for `ψ`-independent `s, s'`, one of the
elements `x i` of (A3) is `ψ`-independent of both: `s, s', x i` are `ψ`-independent. -/
theorem exists_vAlgIndep₃ {s s' : K} (h : VAlgIndep l ![H.ψK s, H.ψK s']) :
    ∃ i, VAlgIndep l ![H.ψK s, H.ψK s', H.ψK (H.x i)] := by
  sorry

/-- For any `s, t ∉ k` there is `r` (one of the `x i`) which is `ψ`-independent of `s` and of
`t` ("two elements with the same point are compared with a third one", proof of
Proposition 6.1). -/
theorem exists_vAlgIndep_pair {s t : K} (hs : s ∉ H.k) (ht : t ∉ H.k) :
    ∃ r : K, VAlgIndep l ![H.ψK s, H.ψK r] ∧ VAlgIndep l ![H.ψK t, H.ψK r] := by
  sorry

end Indep

end CharPHyp

end MilnorAlgDep
