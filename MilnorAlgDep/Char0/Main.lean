module

public import MilnorAlgDep.Foundations.PerfectClosure

/-!
# Theorem A when `L` has characteristic zero

Blueprint Section 6 read with `Γ = 0`, `L_A = L`, `K₀ = K`, `Δ = dlog ∘ ψ` (see the blueprint's
"Remark on formalization"). The statement below has exactly the hypotheses and conclusion of
`MilnorAlgDep.theoremA_perfect`, plus `[CharZero L]`. `K` is arbitrary (its characteristic is not
assumed to be zero: that is part of the conclusion).
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
  sorry

end MilnorAlgDep
