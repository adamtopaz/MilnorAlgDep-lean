module

public import MilnorAlgDep.CharP.Models
public import MilnorAlgDep.CharP.Normalized

/-!
# The trichotomy

Blueprint, Section 4: Lemma 4.6 (`lem:trichotomy`), element-wise.

Let `B` be a transcendence basis of `L / l`, let `(x, y, z)` be a normalized triple of three
distinct collinear points `P = Q_x, Q = Q_y, R = Q_z`, and let `(i, j, k)` be the heights of
`x, y, z`; these are the heights of the level triple `(lev x, lev y, lev z)` of `(P, Q, R)`. The
blueprint's `ω_A(P)` is `omega l p B x`.

## Main statements

* `IsNormalized.trichotomy_lt` (Lemma 4.6(a)): if `i < j`, then `k = i` and `ω(R) = ω(P)`.
* `IsNormalized.trichotomy_eq_of_omega_ne` (Lemma 4.6(b)): if `i = j` and `ω(P) ≠ ω(Q)`, then
  `k = i` and `ω(R)` is contained in `ω(P) + ω(Q)` and differs from `ω(P)` and `ω(Q)`.
* `IsNormalized.trichotomy_eq_of_omega_eq` (Lemma 4.6(c)): if `i = j` and `ω(P) = ω(Q)`, then
  `k ≥ i`.
* `IsNormalized.hgt_eq_of_omega_ne` (Lemma 4.6(d)): if `ω(P), ω(Q), ω(R)` are pairwise distinct
  then `i = j = k`; equivalently (`isNormalized_of_hgt_eq_zero`) model generators of `P, Q, R`
  form a normalized triple, i.e. `(λ_B(P), λ_B(Q), λ_B(R))` is a level triple of `(P, Q, R)`.
-/

@[expose] public section

namespace MilnorAlgDep

open KaehlerDifferential IntermediateField

variable {l L : Type*} [Field l] [Field L] [Algebra l L] {ι : Type*}
variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]
variable {B : ι → L} {x y z : L}

/-- **Blueprint Lemma 4.6(a)**: for a normalized triple `(x, y, z)` with heights `(i, j, k)`, if
`i < j` then `k = i` and `ω(R) = ω(P)`. -/
theorem IsNormalized.trichotomy_lt (hB : IsTranscendenceBasis l B) (h : IsNormalized l x y z)
    (hij : hgt l p B x < hgt l p B y) :
    hgt l p B z = hgt l p B x ∧ omega l p B z = omega l p B x := by
  sorry

/-- **Blueprint Lemma 4.6(b)**: for a normalized triple `(x, y, z)` with heights `(i, j, k)`, if
`i = j` and `ω(P) ≠ ω(Q)`, then `k = i`, and `ω(R)` is contained in `ω(P) + ω(Q)` and different
from `ω(P)` and `ω(Q)`. -/
theorem IsNormalized.trichotomy_eq_of_omega_ne (hB : IsTranscendenceBasis l B)
    (h : IsNormalized l x y z) (hij : hgt l p B x = hgt l p B y)
    (hne : omega l p B x ≠ omega l p B y) :
    hgt l p B z = hgt l p B x ∧ omega l p B z ≤ omega l p B x ⊔ omega l p B y ∧
      omega l p B z ≠ omega l p B x ∧ omega l p B z ≠ omega l p B y := by
  sorry

/-- **Blueprint Lemma 4.6(c)**: for a normalized triple `(x, y, z)` with heights `(i, j, k)`, if
`i = j` and `ω(P) = ω(Q)`, then `k ≥ i`. -/
theorem IsNormalized.trichotomy_eq_of_omega_eq (hB : IsTranscendenceBasis l B)
    (h : IsNormalized l x y z) (hij : hgt l p B x = hgt l p B y)
    (heq : omega l p B x = omega l p B y) : hgt l p B x ≤ hgt l p B z := by
  sorry

/-- **Blueprint Lemma 4.6(d)**: if the lines `ω(P), ω(Q), ω(R)` of three distinct collinear points
are pairwise distinct, then model generators `x, y, z` of `P, Q, R` (elements of height `0`) form
a normalized triple, i.e. `(λ_B(P), λ_B(Q), λ_B(R))` is a level triple of `(P, Q, R)`. -/
theorem isNormalized_of_hgt_eq_zero (hB : IsTranscendenceBasis l B)
    (h : IsCollinearTriple l x y z) (hx : hgt l p B x = 0) (hy : hgt l p B y = 0)
    (hz : hgt l p B z = 0) (hxy : omega l p B x ≠ omega l p B y)
    (hxz : omega l p B x ≠ omega l p B z) (hyz : omega l p B y ≠ omega l p B z) :
    IsNormalized l x y z := by
  sorry

/-- **Blueprint Lemma 4.6(d)**, in terms of heights: if `(x, y, z)` is normalized and the lines
`ω(P), ω(Q), ω(R)` are pairwise distinct, then the heights `i, j, k` are equal. -/
theorem IsNormalized.hgt_eq_of_omega_ne (hB : IsTranscendenceBasis l B)
    (h : IsNormalized l x y z) (hxy : omega l p B x ≠ omega l p B y)
    (hxz : omega l p B x ≠ omega l p B z) (hyz : omega l p B y ≠ omega l p B z) :
    hgt l p B x = hgt l p B y ∧ hgt l p B y = hgt l p B z := by
  sorry

end MilnorAlgDep
