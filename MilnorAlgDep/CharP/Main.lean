module

public import MilnorAlgDep.Foundations.PerfectClosure

/-!
# Theorem A in positive characteristic, for perfect fields

Blueprint Section 6 with `Γ = ℤ`, after the reduction to perfect `K` and `L` (Section 6.1). The
statement below has exactly the hypotheses and conclusion of `MilnorAlgDep.theoremA_perfect`,
plus `[PerfectField K]` and `ringChar L ≠ 0`. Note that `K` and `L` are not assumed to have the
same characteristic: by (A4) `K` has positive characteristic, and equality is part of the
conclusion (Blueprint Proposition 6.9).
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

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
  sorry

end MilnorAlgDep
