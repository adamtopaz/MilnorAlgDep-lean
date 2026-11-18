module

public import MilnorAlgDep.Milnor.Defs
public import MilnorAlgDep.Milnor.Tame
public import MilnorAlgDep.Foundations.AlgIndep

/-!
# Non-vanishing of symbols

Blueprint Lemma 7.2 (`lem:symbols`).

Both parts are proved with the tame symbol of `MilnorAlgDep.Milnor.Tame` for a valuation given by
`exists_valuationSubring_of_transcendental`:

* (a) a valuation trivial on `M = l(a)` with `v(b) > 0`; then the relative tame symbol gives
  `T'_v {a, b} = -v(b) ⊗ [ā] ≠ 0`. (The blueprint takes for `M` the relative algebraic closure of
  `l(a)` in `L`; `l(a)` itself suffices, because the residue map is injective on every field on
  which the valuation is trivial. The hypothesis that `l` is relatively algebraically closed is
  not needed.)
* (b) a valuation trivial on the prime field with `v(b) > 0`; then `T_v {c, b} = -v(b) ⊗ [c̄] ≠ 0`
  since `c̄` is not a root of unity.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf MilnorKQ Tame IntermediateField

/-- **Blueprint Lemma 7.2 (a).** If `l` is relatively algebraically closed in `L` and
`a, b ∈ Lˣ` are algebraically independent over `l`, then `{a, b} ≠ 0` in `𝒦_2(L|l)`. -/
theorem symbol_ne_zero_of_algebraicIndependent {l L : Type*} [Field l] [Field L] [Algebra l L]
    [IsRelAlgClosed l L] {a b : Lˣ} (h : AlgebraicIndependent l ![(a : L), (b : L)]) :
    symbol (constUnits l L) a b ≠ 0 := by
  obtain ⟨ha, hb⟩ := algebraicIndependent_pair_iff.1 h
  -- a valuation trivial on `M = l(a)` and positive at `b`
  obtain ⟨A, hA, -, hbA⟩ := exists_valuationSubring_of_transcendental hb
  have hl : ∀ x : l, algebraMap l L x ∈ A := ValuationExt.algebraMap_mem_of_isScalarTower hA
  have haM : IsAlgebraic l⟮(a : L)⟯ (a : L) :=
    isAlgebraic_algebraMap (⟨a, mem_adjoin_simple_self l (a : L)⟩ : l⟮(a : L)⟯)
  have hau : a ∈ A.unitGroup := ValuationExt.mem_unitGroup_of_isAlgebraic hA haM
  -- no positive power of `a` lies in `l`
  have ha' : ∀ n : ℕ, 0 < n → (a : L) ^ n ∉ Set.range (algebraMap l L) := by
    rintro n hn ⟨c, hc⟩
    exact ha (IsAlgebraic.of_pow hn (hc ▸ isAlgebraic_algebraMap c))
  intro h0
  have key := congrArg (tameSymbolRel A hl) h0
  rw [tameSymbolRel_symbol_of_mem A hl hau, map_zero, neg_eq_zero] at key
  refine tmul_ne_zero ?_ ?_ key
  · rw [← val_cls]
    exact val_cls_ne_zero_of_valuation_lt_one A hbA
  · rw [← unitPartRel_cls_of_mem A hl hau]
    exact unitPartRel_cls_ne_zero A hl hA haM ha'

/-- **Blueprint Lemma 7.2 (b).** If `c ∈ Lˣ` is algebraic over the prime field and not a root of
unity, and `b ∈ Lˣ` is transcendental over the prime field, then `{c, b} ≠ 0` in `𝒦_2(L)`. -/
theorem symbol_ne_zero_of_isAlgebraic_of_transcendental {L : Type*} [Field L] {c b : Lˣ}
    (hc : IsAlgebraic (⊥ : Subfield L) (c : L)) (hc' : ∀ n : ℕ, 0 < n → c ^ n ≠ 1)
    (hb : Transcendental (⊥ : Subfield L) (b : L)) :
    symbol (⊥ : Subgroup Lˣ) c b ≠ 0 := by
  -- a valuation trivial on the prime field and positive at `b`
  obtain ⟨A, hA, -, hbA⟩ := exists_valuationSubring_of_transcendental hb
  have hcu : c ∈ A.unitGroup := ValuationExt.mem_unitGroup_of_isAlgebraic hA hc
  intro h0
  have key := congrArg (tameSymbol A) h0
  rw [tameSymbol_symbol_of_mem A hcu, map_zero, neg_eq_zero] at key
  refine tmul_ne_zero (val_cls_ne_zero_of_valuation_lt_one A hbA) ?_ key
  rw [← unitPart_cls_of_mem A hcu]
  intro h
  obtain ⟨n, hn, hn1⟩ := (unitPart_cls_eq_zero_iff_of_isAlgebraic A hA hc).1 h
  exact hc' n hn hn1

end MilnorAlgDep
