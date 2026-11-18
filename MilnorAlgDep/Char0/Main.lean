module

public import MilnorAlgDep.Foundations.PerfectClosure
public import MilnorAlgDep.Char0.StepC

/-!
# Theorem A when `L` has characteristic zero

Blueprint Section 6 read with `Γ = 0`, `L_A = L`, `K₀ = K`, `Δ = dlog ∘ ψ` (see the blueprint's
"Remark on formalization"). The statement below has exactly the hypotheses and conclusion of
`MilnorAlgDep.theoremA_perfect`, plus `[CharZero L]`. `K` is arbitrary (its characteristic is not
assumed to be zero: that is part of the conclusion).

The development is in

* `MilnorAlgDep.Char0.DLog`: `dlog : V_{L|l} → Ω_{L|l}` (Lemma 6.4 for `Γ = 0`);
* `MilnorAlgDep.Char0.PointDeriv`: differentials of a point and the eigenvalue lemma in
  `Ω_{L|l}`;
* `MilnorAlgDep.Char0.Delta`: `Δ = dlog ∘ ψ`, Lemma 6.5, and `τ` from the abstract Step B
  (Proposition 6.9);
* `MilnorAlgDep.Char0.StepC`: Lemmas 6.10, 6.11 and Proposition 6.12 (case `Γ = 0`).

This file contains the end of the proof (blueprint Section 6.7): `τ⁻¹(l) = k`, `k` is relatively
algebraically closed in `K`, and `char K = char L = 0`. Since `L` has characteristic `0`, no
reduction to perfect fields (Section 6.1) is needed, and (A4) is not used.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

variable {K L : Type*} [Field K] [Field L]

/-- **Blueprint Theorem A** when `L` has characteristic zero (existence part). -/
theorem theoremA_perfect_of_charZero [CharZero L] (k : Subfield K) (l : Subfield L)
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
  -- (A4) is vacuous in characteristic `0` and not needed
  have _ := A4
  have : IsRelAlgClosed l L := IsRelAlgClosed.of_subfield hl
  -- (A3) with `d = 2`
  have hd : (if ringChar L = 0 then 2 else 3) = 2 := ite_eq_left ringChar.eq_zero
  obtain ⟨x, hx⟩ := A3
  have hA3 : VAlgIndep l
      ![ψ (.ofMul (x (Fin.cast hd.symm 0))), ψ (.ofMul (x (Fin.cast hd.symm 1)))] := by
    have h := hx.comp (Fin.cast hd.symm) (Fin.cast_injective _)
    convert h using 1
    ext i
    fin_cases i <;> rfl
  let H : Char0Hyp K l L := ⟨k, ψ, A1, A2, _, _, hA3⟩
  have : CharZero K := H.charZero
  obtain ⟨r, hr, hψ⟩ := H.exists_rat_ψ_eq
  -- `τ⁻¹(l) = k` (Lemma 6.10)
  have hτl : ∀ x : K, H.τ x ∈ l ↔ x ∈ k := by
    intro x
    refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
    · by_contra hx
      exact H.τ_notMem_range hx ⟨⟨_, h⟩, rfl⟩
    · obtain ⟨c, hc⟩ := H.τ_mem_range_of_mem h
      rw [← hc]
      exact c.2
  refine ⟨by rw [ringChar.eq_zero, ringChar.eq_zero], fun x hx ↦ ?_, H.τ, r, hr, hτl, hψ⟩
  -- `k` is relatively algebraically closed in `K`: `τ x` is algebraic over `l`, so lies in `l`
  let f : k →+* l := (H.τ.comp k.subtype).codRestrict l fun c ↦ (hτl c).2 c.2
  have hcomp : (algebraMap l L).comp f = H.τ.comp (algebraMap k K) := by
    ext c
    rfl
  exact (hτl x).1 (hl _ (hx.ringHom_of_comp_eq f H.τ f.injective hcomp))

end MilnorAlgDep
