module

public import MilnorAlgDep.Foundations.PerfectClosure

/-!
# Uniqueness in Theorem A

Blueprint Lemma 6.13. The statement is that of `MilnorAlgDep.theoremA_perfect_unique`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

variable {K L : Type*} [Field K] [Field L]

/-- **Blueprint Lemma 6.13** (uniqueness in Theorem A), for a perfect field `L`. See
`MilnorAlgDep.theoremA_perfect_unique` for the discussion of the statement. -/
theorem theoremA_perfect_unique_aux [PerfectField L] (l : Subfield L)
    (hl : ∀ x : L, IsAlgebraic l x → x ∈ l)
    (ψ : Additive Kˣ →+ V l L) (hψ : ψ ≠ 0)
    (τ τ' : K →+* L) (r r' : ℚ)
    (h : ∀ x : Kˣ, ψ (.ofMul x) = r • 〚Units.map (τ : K →* L) x〛)
    (h' : ∀ x : Kˣ, ψ (.ofMul x) = r' • 〚Units.map (τ' : K →* L) x〛) :
    ∃ j : ℤ, τ' = ((frobeniusEquiv L (ringExpChar L) ^ j : L ≃+* L) : L →+* L).comp τ ∧
      r' = (ringExpChar L : ℚ) ^ (-j) * r := by
  sorry

end MilnorAlgDep
