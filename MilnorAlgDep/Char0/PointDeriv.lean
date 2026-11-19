module

public import MilnorAlgDep.Char0.DLog
public import MilnorAlgDep.Foundations.Points
public import MilnorAlgDep.Standard.Differentials.Restrict
public import MilnorAlgDep.Standard.Eigenvalue

/-!
# Differentials of a point, and the eigenvalue lemma in `Ω_{L|l}`

Ingredients of blueprint Lemma 6.5(b) (`lem:K0`, "`μ(x) ∈ Q_x`"), Lemma 6.10 (`lem:tauinQ`) and
Lemma 6.11 (`lem:theta`) in characteristic `0`.

Let `l ⊆ L` be fields of characteristic `0` and `a ∈ L` transcendental over `l`. The point
`E = Q_a` (the relative algebraic closure of `l(a)` in `L`) is separable algebraic over `l(a)`, so
`Ω[E⁄l]` is free of rank one over `E`, with basis `d a` (Lemma 2.1 (S2)). Hence:

* `exists_mem_point_D_eq_smul`: for `b ∈ Q_a` we have `d b = c • d a` in `Ω[L⁄l]` with `c ∈ Q_a`
  (this is the blueprint's "`db = b_a da` with `b_a` in the field of elements separable over
  `l(a)`, which is contained in `Q_x`", line 535);
* `pointDeriv`: the derivation `δ` of `E` with `d f = δ(f) • d a / a`, so `δ(a) = a` (the
  blueprint's derivation in the proofs of Lemmas 6.10 and 6.11, line 656). We define it through
  the coordinate function of the basis `d a` of `Ω[E⁄l]`; the identity `d f = δ(f) • d a / a` in
  `Ω[L⁄l]` (`smul_D_eq_pointDeriv_smul`) is obtained by pushing forward along `Ω[E⁄l] → Ω[L⁄l]`,
  and no injectivity statement is needed, only `d a ≠ 0` in `Ω[L⁄l]`;
* `exists_mem_pointV_dlog_eq_smul`: the same for `dlog : V l L → Ω[L⁄l]`: if `v ≠ 0` and
  `Q_w = Q_v`, then `dlog w = c • dlog v` with `c ∈ Q_v`;
* `exists_ratCast_of_dlogL_eq`: Blueprint Lemma 2.2 (eigenvalue lemma) in the form in which it is
  applied: if `b ∈ Q_a`, `b ≠ 0` and `dlog b = κ • dlog a` in `Ω[L⁄l]` with `κ ∈ l`, then `κ` is
  rational.
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential IntermediateField

variable {l L : Type*} [Field l] [Field L] [Algebra l L] [CharZero L]

/-- `a` viewed as an element of its point `Q_a`. -/
def pointGen (a : L) : point l a :=
  ⟨a, self_mem_point a⟩

omit [CharZero L] in
@[simp]
theorem coe_pointGen (a : L) : (pointGen (l := l) a : L) = a :=
  rfl

/-- In characteristic `0`, every element of `Q_a` is separable over `l(a)`. -/
theorem isSeparable_of_mem_point {a y : L} (hy : y ∈ point l a) : IsSeparable l⟮a⟯ y :=
  PerfectField.separable_of_irreducible (minpoly.irreducible (mem_point_iff.1 hy).isIntegral)

/-- In characteristic `0`, `Q_a` is separable algebraic over `l(a) ⊆ Q_a`. -/
theorem isSeparable_point (a : L) :
    Algebra.IsSeparable (adjoin l (Set.range fun _ : Unit ↦ pointGen (l := l) a)) (point l a) :=
  isSeparable_adjoin_restrictFamily (point l a) (a := fun _ : Unit ↦ a)
    (fun _ ↦ self_mem_point a) fun _ hy ↦ by
      rw [Set.range_const]
      exact isSeparable_of_mem_point hy

omit [CharZero L] in
theorem transcendental_pointGen {a : L} (ha : Transcendental l a) :
    Transcendental l (pointGen (l := l) a) :=
  fun h ↦ ha (h.algHom (point l a).val)

omit [CharZero L] in
theorem ne_zero_of_transcendental {a : L} (ha : Transcendental l a) : a ≠ 0 := by
  rintro rfl
  exact ha isAlgebraic_zero

/-- In characteristic `0`, `d a ≠ 0` in `Ω[L⁄l]` for `a` transcendental over `l`. -/
theorem D_ne_zero_of_transcendental {a : L} (ha : Transcendental l a) : D l L a ≠ 0 := by
  have : CharZero l := (algebraMap l L).charZero
  rwa [Ne, kaehler_D_eq_zero_iff_isAlgebraic]

/-- Blueprint Lemma 2.1 (S2) for `E = Q_a`: `d a` is a basis of `Ω[Q_a⁄l]`. -/
noncomputable def pointBasis {a : L} (ha : Transcendental l a) :
    Module.Basis Unit (point l a) Ω[point l a⁄l] :=
  kaehlerBasis (algebraicIndependent_unique_type_iff.2 (transcendental_pointGen ha))
    (isSeparable_point a)

theorem pointBasis_apply {a : L} (ha : Transcendental l a) (i : Unit) :
    pointBasis ha i = D l (point l a) (pointGen a) :=
  kaehlerBasis_apply _ _ i

/-- The coefficient of `d f` with respect to the basis `d a` of `Ω[Q_a⁄l]`. -/
noncomputable def pointCoeff {a : L} (ha : Transcendental l a) (f : point l a) : point l a :=
  (pointBasis ha).coord () (D l (point l a) f)

theorem D_point_eq_pointCoeff_smul {a : L} (ha : Transcendental l a) (f : point l a) :
    D l (point l a) f = pointCoeff ha f • D l (point l a) (pointGen a) := by
  have := (pointBasis ha).sum_repr (D l (point l a) f)
  rw [Fintype.sum_unique, pointBasis_apply] at this
  rw [pointCoeff, Module.Basis.coord_apply]
  exact this.symm

/-- `d f = c • d a` in `Ω[L⁄l]`, with `c = pointCoeff f ∈ Q_a`. -/
theorem D_eq_pointCoeff_smul {a : L} (ha : Transcendental l a) (f : point l a) :
    D l L (f : L) = (pointCoeff ha f : L) • D l L a := by
  have := congrArg (KaehlerDifferential.map l l (point l a) L) (D_point_eq_pointCoeff_smul ha f)
  rw [map_D, LinearMap.map_smul, map_D] at this
  exact this.trans (algebraMap_smul L (pointCoeff ha f) _).symm

/-- Blueprint, proof of Lemma 6.5(b) (line 535), characteristic `0`: if `a` is transcendental
over `l` and `b ∈ Q_a`, then `d b = c • d a` in `Ω[L⁄l]` for some `c ∈ Q_a`. -/
theorem exists_mem_point_D_eq_smul {a b : L} (ha : Transcendental l a) (hb : b ∈ point l a) :
    ∃ c ∈ point l a, D l L b = c • D l L a :=
  ⟨_, (pointCoeff ha ⟨b, hb⟩).2, D_eq_pointCoeff_smul ha ⟨b, hb⟩⟩

/-- The derivation `δ = a • d/da` of `Q_a`: `d f = δ(f) • d a / a` (blueprint, proofs of
Lemmas 6.10 and 6.11). -/
noncomputable def pointDeriv {a : L} (ha : Transcendental l a) :
    Derivation l (point l a) (point l a) :=
  pointGen (l := l) a • ((pointBasis ha).coord ()).compDer (D l (point l a))

theorem pointDeriv_apply {a : L} (ha : Transcendental l a) (f : point l a) :
    pointDeriv ha f = pointGen a * pointCoeff ha f :=
  rfl

theorem pointDeriv_pointGen {a : L} (ha : Transcendental l a) :
    pointDeriv ha (pointGen a) = pointGen a := by
  rw [pointDeriv_apply, pointCoeff, ← pointBasis_apply ha (), Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_eq_same, mul_one]

/-- `a • d f = δ(f) • d a` in `Ω[L⁄l]`. -/
theorem smul_D_eq_pointDeriv_smul {a : L} (ha : Transcendental l a) (f : point l a) :
    a • D l L (f : L) = (pointDeriv ha f : L) • D l L a := by
  rw [D_eq_pointCoeff_smul ha f, smul_smul, pointDeriv_apply, MulMemClass.coe_mul, coe_pointGen]

/-- **Blueprint Lemma 2.2** (eigenvalue lemma), in the form used in Lemmas 6.10 and 6.11 in
characteristic `0`: let `a ∈ L` be transcendental over `l`, `b ∈ Q_a` non-zero and `κ ∈ l` with
`dlog b = κ • dlog a` in `Ω[L⁄l]`. Then `κ` is a rational number. -/
theorem exists_ratCast_of_dlogL_eq {a b : L} (ha : Transcendental l a) (hb : b ∈ point l a)
    (hb0 : b ≠ 0) {κ : l} (h : dlogL l b = algebraMap l L κ • dlogL l a) :
    ∃ q : ℚ, (q : l) = κ := by
  have : CharZero l := (algebraMap l L).charZero
  set b' : point l a := ⟨b, hb⟩
  have ha0 := ne_zero_of_transcendental ha
  have hDa := D_ne_zero_of_transcendental ha
  -- `δ b = κ b`
  have hδ : pointDeriv ha b' = algebraMap l (point l a) κ * b' := by
    apply Subtype.ext
    have e1 := smul_D_eq_pointDeriv_smul ha b'
    have e2 : a • D l L b = (algebraMap l L κ * b) • D l L a := by
      rw [D_eq_smul_dlogL hb0, h, dlogL, smul_smul, smul_smul, smul_smul]
      congr 1
      field_simp
    exact smul_left_injective L hDa (e1.symm.trans e2)
  have hsep : IsSeparable l⟮pointGen (l := l) a⟯ b' := by
    have := isSeparable_point (l := l) a
    rw [Set.range_const] at this
    exact Algebra.IsSeparable.isSeparable _ b'
  have hb'0 : b' ≠ 0 := fun h0 ↦ hb0 (congrArg Subtype.val h0)
  exact exists_ratCast_eq_eigenvalue (pointGen a) (transcendental_pointGen ha) (pointDeriv ha)
    (pointDeriv_pointGen ha) b' hb'0 hsep κ hδ

/-- Blueprint, proof of Lemma 6.5(b) (line 535) and of Lemma 6.11 (`lem:theta`),
characteristic `0`: if `v ≠ 0` and `Q_w = Q_v`, then `dlog w = c • dlog v` for some `c ∈ Q_v`. -/
theorem exists_mem_pointV_dlog_eq_smul [IsRelAlgClosed l L] {v w : V l L} (hv : v ≠ 0)
    (hw : pointV l w = pointV l v) : ∃ c ∈ pointV l v, dlog l L w = c • dlog l L v := by
  obtain ⟨N, a, hN, ha, hva⟩ := V.exists_rep hv
  obtain ⟨M, b, hM, hwb⟩ := VOf.exists_nsmul_eq_cls w
  have hpv : pointV l v = point l (a : L) := pointV_eq_point hN hva
  have hb : (b : L) ∈ point l (a : L) := by
    rw [← hpv, ← hw, pointV_eq_point hM hwb]
    exact self_mem_point _
  obtain ⟨c, hc, hD⟩ := exists_mem_point_D_eq_smul (IsRelAlgClosed.transcendental ha) hb
  refine ⟨(M : L)⁻¹ * (b : L)⁻¹ * c * N * a, ?_, ?_⟩
  · rw [hpv]
    exact mul_mem (mul_mem (mul_mem (mul_mem (inv_mem (_root_.natCast_mem _ M)) (inv_mem hb)) hc)
      (_root_.natCast_mem _ N)) (self_mem_point _)
  · have hN0 : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
    rw [dlog_of_nsmul_eq_cls hM hwb, dlog_of_nsmul_eq_cls hN hva, dlogL, dlogL, hD, smul_smul,
      smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp

end MilnorAlgDep
