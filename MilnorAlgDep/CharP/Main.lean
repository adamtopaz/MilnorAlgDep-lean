module

public import MilnorAlgDep.Foundations.PerfectClosure
public import MilnorAlgDep.CharP.StepC
public import Mathlib.FieldTheory.IsPerfectClosure

/-!
# Theorem A in positive characteristic, for perfect fields

Blueprint Section 6 with `Γ = ℤ`, after the reduction to perfect `K` and `L` (Section 6.1). The
statement below has exactly the hypotheses and conclusion of `MilnorAlgDep.theoremA_perfect`,
plus `[PerfectField K]` and `ringChar L ≠ 0`. Note that `K` and `L` are not assumed to have the
same characteristic: by (A4) `K` has positive characteristic, and equality is part of the
conclusion (Blueprint Proposition 6.9).

The development is in

* `MilnorAlgDep.CharP.LevelV`: levels and heights of elements of `V`, the hypotheses
  `CharPHyp`, equation (6.1) `eq:sum` (Section 6.1);
* `MilnorAlgDep.CharP.StepA`: Step A, Proposition 6.1 (Section 6.2);
* `MilnorAlgDep.CharP.AdaptedModel`: `W`, `dlog_A`, `K₀`, `Δ`, Lemmas 6.4 and 6.5, and
  `τ : K₀ → L` from the abstract Step B (Section 6.3, Proposition 6.9);
* `MilnorAlgDep.CharP.StepC`: (6.6) `eq:roots`, Lemmas 6.10, 6.11, Proposition 6.12
  (Section 6.6).

This file contains the end of the proof (blueprint Section 6.7): `τ` extends uniquely from `K₀`
to `K` (`CharPHyp.τK`, via `PerfectRing.lift`, since `K` is perfect and `p`-radical over `K₀`),
`ψ = r [τ]` on `Kˣ` (`CharPHyp.exists_rat_ψ_eq`), `τ⁻¹(l) = k` (`CharPHyp.τK_mem_range_iff`) and
`k` is relatively algebraically closed in `K` (`CharPHyp.isRelAlgClosed_k`).
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

namespace CharPHyp

variable {K l L : Type*} [Field K] [Field l] [Field L] [Algebra l L] [PerfectField K]
  (H : CharPHyp K l L)
variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]

/-- `K` is `p`-radical over `K₀` (blueprint (6.6) `eq:roots`: `K = ⋃_j Frob^{-j}(K₀)`). -/
theorem isPRadical_K₀ : IsPRadical (H.K₀ p).subtype p where
  pow_mem' x := by
    obtain ⟨j, hj⟩ := H.exists_pow_pow_mem_K₀ p x
    exact ⟨j, ⟨_, hj⟩, rfl⟩
  ker_le' x hx := by
    have hx0 : x = 0 := (H.K₀ p).subtype_injective (by simpa using hx)
    rw [hx0]
    exact Ideal.zero_mem _

theorem charP_K₀ : CharP (H.K₀ p) p :=
  (H.τ p).charP (H.τ p).injective p

/-- Blueprint Section 6.7: the extension `τ : K → L` of `τ : K₀ → L` (`K` is perfect and
`p`-radical over `K₀`, and `L` is perfect). -/
noncomputable def τK : K →+* L :=
  haveI := H.charP_K p
  haveI := H.charP_K₀ p
  haveI := H.isPRadical_K₀ p
  PerfectRing.lift (H.K₀ p).subtype (H.τ p) p

/-- `τK` extends `τ`. -/
theorem τK_coe (x : H.K₀ p) : H.τK p x = H.τ p x := by
  have := H.charP_K p
  have := H.charP_K₀ p
  have := H.isPRadical_K₀ p
  exact PerfectRing.lift_comp_apply (H.K₀ p).subtype (H.τ p) p x

/-- `τ(x)^{p^j} = τ(x^{p^j})` for `x^{p^j} ∈ K₀`. -/
theorem τK_pow_pow {x : K} {j : ℕ} (hj : x ^ p ^ j ∈ H.K₀ p) :
    H.τK p x ^ p ^ j = H.τ p ⟨x ^ p ^ j, hj⟩ := by
  rw [← map_pow, ← τK_coe]

omit [PerfectField K] [CharP L p] [PerfectField L] [IsRelAlgClosed l L] in
theorem pow_pow_notMem {x : K} (hx : x ∉ H.k) (j : ℕ) : x ^ p ^ j ∉ H.k := by
  intro h
  apply H.ψK_ne_zero hx
  have h0 := H.ψK_eq_zero_iff.2 h
  rw [ψK_pow, ← Nat.cast_smul_eq_nsmul ℚ, smul_eq_zero] at h0
  exact h0.resolve_left (Nat.cast_ne_zero.2 (pow_ne_zero _ (Fact.out : p.Prime).ne_zero))

/-- **Blueprint Section 6.7**: `ψ = r [τ]` on `Kˣ` (from Proposition 6.12 on `K₀ˣ`, as `V` is
uniquely divisible). -/
theorem exists_rat_ψ_eq : ∃ r : ℚ, r ≠ 0 ∧
    ∀ x : Kˣ, H.ψ (.ofMul x) = r • 〚Units.map (H.τK p : K →* L) x〛 := by
  obtain ⟨r, hr, h⟩ := H.exists_rat_ψ₀_eq p
  refine ⟨r, hr, fun x ↦ ?_⟩
  obtain ⟨j, hj⟩ := H.exists_pow_pow_mem_K₀ p (x : K)
  have hy0 : (⟨(x : K) ^ p ^ j, hj⟩ : H.K₀ p) ≠ 0 := fun h0 ↦
    pow_ne_zero _ x.ne_zero (congrArg Subtype.val h0)
  set y : (H.K₀ p)ˣ := Units.mk0 _ hy0
  have hψ : H.ψ₀ p (.ofMul y) = p ^ j • H.ψ (.ofMul x) := by
    rw [ψ₀_apply, Units.val_mk0, ψK_pow, ψK_units]
  have hτ : Units.map (H.τ p : H.K₀ p →* L) y = Units.map (H.τK p : K →* L) x ^ p ^ j := by
    ext
    rw [Units.coe_map, Units.val_pow_eq_pow_val, Units.coe_map, Units.val_mk0]
    exact (H.τK_pow_pow p hj).symm
  have e := h y
  rw [hψ, τV_apply, hτ, cls_pow, smul_comm] at e
  exact nsmul_left_cancel (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) e

/-- **Blueprint Section 6.7** and Lemma 6.10: `τ⁻¹(l) = k`. -/
theorem τK_mem_range_iff (x : K) : H.τK p x ∈ (algebraMap l L).range ↔ x ∈ H.k := by
  refine ⟨fun h ↦ ?_, fun hx ↦ ?_⟩
  · by_contra hx
    obtain ⟨j, hj⟩ := H.exists_pow_pow_mem_K₀ p x
    apply H.τ_notMem_range p (x := ⟨_, hj⟩) (H.pow_pow_notMem p hx j)
    rw [← H.τK_pow_pow p hj]
    exact pow_mem h _
  · rw [← Subtype.coe_mk x (H.mem_K₀_of_mem p hx), τK_coe]
    exact H.τ_mem_range_of_mem p hx

include p in
/-- **Blueprint Section 6.7**: `k` is relatively algebraically closed in `K` (if `x` is algebraic
over `k`, then `τ(x)` is algebraic over `l`, so `τ(x) ∈ l` and `x ∈ k`). -/
theorem isRelAlgClosed_k (x : K) (hx : IsAlgebraic H.k x) : x ∈ H.k := by
  have hk : ∀ c : H.k, H.τK p c ∈ (algebraMap l L).range := fun c ↦
    (H.τK_mem_range_iff p c).2 c.2
  let g : H.k →+* (algebraMap l L).range :=
    ((H.τK p).comp H.k.subtype).codRestrict _ hk
  let e : l ≃+* (algebraMap l L).range :=
    RingEquiv.ofBijective (algebraMap l L).rangeRestrict
      ⟨fun a b h ↦ (algebraMap l L).injective (congrArg Subtype.val h),
        (algebraMap l L).rangeRestrict_surjective⟩
  let f : H.k →+* l := e.symm.toRingHom.comp g
  have hcomp : (algebraMap l L).comp f = (H.τK p).comp (algebraMap H.k K) := by
    ext c
    change ((algebraMap l L).rangeRestrict (e.symm (g c)) : L) = H.τK p c
    rw [show (algebraMap l L).rangeRestrict (e.symm (g c)) = e (e.symm (g c)) from rfl,
      RingEquiv.apply_symm_apply]
    rfl
  exact (H.τK_mem_range_iff p x).1
    (IsRelAlgClosed.mem_range (hx.ringHom_of_comp_eq f (H.τK p) f.injective hcomp))

end CharPHyp

variable {K L : Type*} [Field K] [Field L]

/-- **Blueprint Theorem A** for perfect fields `K`, `L` with `L` of positive characteristic
(existence part). -/
theorem theoremA_core_charP [PerfectField K] [PerfectField L] (hL : ringChar L ≠ 0)
    (k : Subfield K) (l : Subfield L)
    (hl : ∀ x : L, IsAlgebraic l x → x ∈ l)
    (ψ : Additive Kˣ →+ V l L)
    (A1 : ∀ x : Kˣ, ψ (.ofMul x) = 0 ↔ (x : K) ∈ k)
    (A2 : ∀ x y : Kˣ, (x : K) + y = 1 → (x : K) ∉ k →
      ¬ VAlgIndep l ![ψ (.ofMul x), ψ (.ofMul y)])
    (A3 : ∃ x : Fin (if ringChar L = 0 then 2 else 3) → Kˣ,
      VAlgIndep l fun i ↦ ψ (.ofMul (x i)))
    (A4 : ringChar L ≠ 0 → ringChar K ≠ 0) :
    ringChar K = ringChar L ∧ (∀ x : K, IsAlgebraic k x → x ∈ k) ∧
      ∃ (τ : K →+* L) (r : ℚ), r ≠ 0 ∧ (∀ x : K, τ x ∈ l ↔ x ∈ k) ∧
        ∀ x : Kˣ, ψ (.ofMul x) = r • 〚Units.map (τ : K →* L) x〛 := by
  have : IsRelAlgClosed l L := IsRelAlgClosed.of_subfield hl
  have : Fact (ringChar L).Prime := ⟨(CharP.char_is_prime_or_zero L _).resolve_right hL⟩
  -- (A3) with `d = 3`
  have hd : (if ringChar L = 0 then 2 else 3) = 3 := ite_eq_right hL
  obtain ⟨x, hx⟩ := A3
  have hA3 : VAlgIndep l fun i : Fin 3 ↦ ψ (.ofMul (x (Fin.cast hd.symm i))) :=
    hx.comp (Fin.cast hd.symm) (Fin.cast_injective _)
  let H : CharPHyp K l L := ⟨k, ψ, A1, A2, fun i ↦ x (Fin.cast hd.symm i), hA3, A4 hL⟩
  obtain ⟨r, hr, hψ⟩ := H.exists_rat_ψ_eq (ringChar L)
  refine ⟨H.ringChar_eq (ringChar L), H.isRelAlgClosed_k (ringChar L), H.τK (ringChar L), r, hr,
    fun y ↦ ?_, hψ⟩
  rw [← H.τK_mem_range_iff (ringChar L) y]
  exact ⟨fun h ↦ ⟨⟨_, h⟩, rfl⟩, fun ⟨c, hc⟩ ↦ hc ▸ c.2⟩

end MilnorAlgDep
