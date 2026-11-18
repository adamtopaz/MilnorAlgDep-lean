module

public import MilnorAlgDep.Foundations.PerfectClosure
public import MilnorAlgDep.Char0.Main
public import MilnorAlgDep.CharP.Main

/-!
# Reductions for Theorem A

Blueprint Section 6.1 ("Reductions") and the first sentence of 6.7.

* `theoremA_perfect_aux`: Theorem A for perfect `L` and arbitrary `K`, from the characteristic
  zero case (`theoremA_perfect_of_charZero`) and the positive characteristic case for perfect `K`
  (`theoremA_core_charP`), by extending `ψ` to the perfect closure of `K`.
* `theoremA_aux`: Theorem A for arbitrary `L`, from `theoremA_perfect_aux` applied to a perfect
  closure `M` of `L`, `l^i` and `V.toPerfectClosure ∘ ψ`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

variable {K L : Type*} [Field K] [Field L]

/-- Theorem A for perfect `L` and arbitrary `K`; this is the statement of
`MilnorAlgDep.theoremA_perfect`. -/
theorem theoremA_perfect_aux [PerfectField L] (k : Subfield K) (l : Subfield L)
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

/-- Theorem A for arbitrary `K` and `L`; this is the statement of `MilnorAlgDep.theoremA`. -/
theorem theoremA_aux (k : Subfield K) (l : Subfield L)
    (hl : ∀ x : L, IsAlgebraic l x → x ∈ l)
    (ψ : Additive Kˣ →+ V l L)
    (A1 : ∀ x : Kˣ, ψ (.ofMul x) = 0 ↔ (x : K) ∈ k)
    (A2 : ∀ x y : Kˣ, (x : K) + y = 1 → (x : K) ∉ k →
      ¬ VAlgIndep l ![ψ (.ofMul x), ψ (.ofMul y)])
    (A3 : ∃ x : Fin (if ringChar L = 0 then 2 else 3) → Kˣ,
      VAlgIndep l fun i ↦ ψ (.ofMul (x i)))
    (A4 : ringChar L ≠ 0 → ringChar K ≠ 0)
    (p : ℕ) [ExpChar L p] (M : Type*) [Field M] [Algebra L M] [ExpChar M p] [PerfectRing M p]
    [IsPerfectClosure (algebraMap L M) p] :
    ringChar K = ringChar L ∧ (∀ x : K, IsAlgebraic k x → x ∈ k) ∧
      ∃ (τ : K →+* M) (r : ℚ), r ≠ 0 ∧ (∀ x : K, τ x ∈ perfectClosureIn l M p ↔ x ∈ k) ∧
        ∀ x : Kˣ, V.toPerfectClosure l M p (ψ (.ofMul x)) = r • 〚Units.map (τ : K →* M) x〛 := by
  sorry

end MilnorAlgDep
