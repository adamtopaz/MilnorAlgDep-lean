module

public import MilnorAlgDep.Milnor.Defs
public import MilnorAlgDep.Foundations.AlgIndep

/-!
# Non-vanishing of symbols

Blueprint Lemma 7.2 (`lem:symbols`).
-/

@[expose] public section

namespace MilnorAlgDep

open VOf MilnorKQ

/-- **Blueprint Lemma 7.2 (a).** If `l` is relatively algebraically closed in `L` and
`a, b ∈ Lˣ` are algebraically independent over `l`, then `{a, b} ≠ 0` in `𝒦_2(L|l)`. -/
theorem symbol_ne_zero_of_algebraicIndependent {l L : Type*} [Field l] [Field L] [Algebra l L]
    [IsRelAlgClosed l L] {a b : Lˣ} (h : AlgebraicIndependent l ![(a : L), (b : L)]) :
    symbol (constUnits l L) a b ≠ 0 := by
  sorry

/-- **Blueprint Lemma 7.2 (b).** If `c ∈ Lˣ` is algebraic over the prime field and not a root of
unity, and `b ∈ Lˣ` is transcendental over the prime field, then `{c, b} ≠ 0` in `𝒦_2(L)`. -/
theorem symbol_ne_zero_of_isAlgebraic_of_transcendental {L : Type*} [Field L] {c b : Lˣ}
    (hc : IsAlgebraic (⊥ : Subfield L) (c : L)) (hc' : ∀ n : ℕ, 0 < n → c ^ n ≠ 1)
    (hb : Transcendental (⊥ : Subfield L) (b : L)) :
    symbol (⊥ : Subgroup Lˣ) c b ≠ 0 := by
  sorry

end MilnorAlgDep
