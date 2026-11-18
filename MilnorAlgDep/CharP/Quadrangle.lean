module

public import MilnorAlgDep.CharP.Trichotomy

/-!
# The quadrangle lemma

Blueprint, Section 5: Lemma 5.1 (`lem:quadrangle`), element-wise.

Points are given by transcendental elements: `A = Q_{a₀}`, …, `H = Q_{h₀}`. "`X` lies on the line
`⟨P, Q⟩`" is `IsAlgebraic l⟮p, q⟯ x`; "`D` lies on `⟨A, B⟩` and differs from `A, B`" is
`IsCollinearTriple l a₀ b₀ d₀`. "Levels `α_X ∈ Λ(X)` such that each of six collinear triples of
levels is a level triple" becomes: elements `a, …, h` of the points `A, …, H` such that the six
triples are normalized.

## Main statements

* `quadrangle`: Lemma 5.1.
* `levelTriple_fst_add_levelTriple_fst`: the consequence used in the proof of Lemma 6.3
  (cocycle): with `c(a, b) = (levelTriple l p a b d).1`, `c(a₀, b₀) + c(b₀, c₀) = c(a₀, c₀)`.
-/

@[expose] public section

namespace MilnorAlgDep

open IntermediateField

variable {l L : Type*} [Field l] [Field L] [Algebra l L] [PerfectField L] [IsRelAlgClosed l L]
variable {a₀ b₀ c₀ d₀ e₀ g₀ h₀ : L}

/-- **Blueprint Lemma 5.1 (Quadrangle)**: let `A, B, C` be non-collinear points, `D` a point on
`⟨A, B⟩` different from `A, B`, `E` a point on `⟨B, C⟩` different from `B, C`, `G` a point on both
`⟨D, C⟩` and `⟨A, E⟩`, and `H` a point on both `⟨A, C⟩` and `⟨B, G⟩`. Then there are elements
`a ∈ A, …, h ∈ H` such that the six triples `(a, b, d)`, `(b, c, e)`, `(d, c, g)`, `(a, e, g)`,
`(a, c, h)`, `(b, h, g)` are normalized; i.e. their levels `α_X = lev x` form level triples of
`(A, B, D)`, …, `(B, H, G)`. -/
theorem quadrangle (p : ℕ) [Fact p.Prime] [CharP L p]
    (habc : AlgebraicIndependent l ![a₀, b₀, c₀])
    (hd : IsCollinearTriple l a₀ b₀ d₀) (he : IsCollinearTriple l b₀ c₀ e₀)
    (hg : Transcendental l g₀) (hgDC : IsAlgebraic l⟮d₀, c₀⟯ g₀)
    (hgAE : IsAlgebraic l⟮a₀, e₀⟯ g₀)
    (hh : Transcendental l h₀) (hhAC : IsAlgebraic l⟮a₀, c₀⟯ h₀)
    (hhBG : IsAlgebraic l⟮b₀, g₀⟯ h₀) :
    ∃ a b c d e g h : L,
      SamePoint l a a₀ ∧ SamePoint l b b₀ ∧ SamePoint l c c₀ ∧ SamePoint l d d₀ ∧
      SamePoint l e e₀ ∧ SamePoint l g g₀ ∧ SamePoint l h h₀ ∧
      IsNormalized l a b d ∧ IsNormalized l b c e ∧ IsNormalized l d c g ∧
      IsNormalized l a e g ∧ IsNormalized l a c h ∧ IsNormalized l b h g := by
  sorry

/-- The consequence of **blueprint Lemma 5.1** used in the proof of Lemma 6.3 (cocycle): in the
situation of the quadrangle lemma, the first entries of the level triples of `(A, B, D)`,
`(B, C, E)` and `(A, C, H)` relative to `a₀, b₀, c₀, …` satisfy the cocycle relation. -/
theorem levelTriple_fst_add_levelTriple_fst (p : ℕ) [Fact p.Prime] [CharP L p]
    (habc : AlgebraicIndependent l ![a₀, b₀, c₀])
    (hd : IsCollinearTriple l a₀ b₀ d₀) (he : IsCollinearTriple l b₀ c₀ e₀)
    (hg : Transcendental l g₀) (hgDC : IsAlgebraic l⟮d₀, c₀⟯ g₀)
    (hgAE : IsAlgebraic l⟮a₀, e₀⟯ g₀)
    (hh : Transcendental l h₀) (hhAC : IsAlgebraic l⟮a₀, c₀⟯ h₀)
    (hhBG : IsAlgebraic l⟮b₀, g₀⟯ h₀) :
    (levelTriple l p a₀ b₀ d₀).1 + (levelTriple l p b₀ c₀ e₀).1 =
      (levelTriple l p a₀ c₀ h₀).1 := by
  obtain ⟨a, b, c, d, e, g, h, ha, hb, hc, hd', he', -, hh', habd, hbce, -, -, hach, -⟩ :=
    quadrangle p habc hd he hg hgDC hgAE hh hhAC hhBG
  rw [levelTriple_eq_of_isNormalized p habd ha hb hd',
    levelTriple_eq_of_isNormalized p hbce hb hc he',
    levelTriple_eq_of_isNormalized p hach ha hc hh']
  ring

end MilnorAlgDep
