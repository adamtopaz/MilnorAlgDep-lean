module

public import MilnorAlgDep.CharP.AdaptedModel
public import MilnorAlgDep.Standard.Eigenvalue

/-!
# Field-theoretic lemmas for Step C in characteristic `p`

Blueprint Section 6.6 with `Γ = ℤ`: the statements in the proofs of Lemmas 6.10, 6.11 and
Proposition 6.12 that concern only the extension `L / l` and a model, not the homomorphism `ψ`.

* `exists_intCast_of_modelDLog_eq`: the eigenvalue lemma (Lemma 2.2) in the form used in
  Lemmas 6.10, 6.11 and `eq:lift`.
* `mem_of_pow_pow_mem`: `eq:Epower`, `E ∩ L_A^{p^j} = E^{p^j}`.
* `exists_pow_eq_mul_pow_pow`: from `p^j • v = [b]` with `v ∈ W`, `b ∈ E` to
  `b^M = c y^{p^j}` with `y ∈ E`.
* `exists_dvd_sub_of_forall_pow_eq`: the norm argument and unique factorization in `l[s]`
  (the `s`-adic order of `N_{E|l(s)}(a)`).
* `exists_dvd_sub_of_dvd`: elementary arithmetic (`MN = p^β n'`, `ε = p^β m'`).
-/

@[expose] public section

namespace MilnorAlgDep

open VOf IntermediateField KaehlerDifferential

variable {l L : Type*} [Field l] [Field L] [Algebra l L] {ι : Type*}

/-! ### Field-theoretic lemmas -/

section Fields

variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]

include p in
/-- **Blueprint Lemma 2.2** (eigenvalue lemma) in a model, in the form used in Lemmas 6.10, 6.11
and in `eq:lift`: let `a ∈ L_B` with `d a ≠ 0` in `Ω_B`, and `b ≠ 0` separable algebraic
over `l(a)`. If `dlog b = κ • dlog a` in `Ω_B` with `κ ∈ l`, then `κ` lies in the prime field
`F_p`, i.e. is the image of an integer. (Apply Lemma 2.2 to the derivation `δ` of the field of
elements separable over `l(a)` with `d f = δ(f) • dlog a`; `Ω_{E|l} → Ω_B` is injective because
`d a ≠ 0`.) -/
theorem exists_intCast_of_modelDLog_eq {B : ι → L} {a b : L} (ha : a ∈ model l B)
    (hda : modelD l B a ≠ 0) (hb : IsSeparable l⟮a⟯ b) (hb0 : b ≠ 0) {κ : l}
    (h : modelDLog l B b = algebraMap l (model l B) κ • modelDLog l B a) :
    ∃ m : ℤ, (m : l) = κ := by
  sorry

/-- Blueprint `eq:Epower`: let `s ∈ L_B` with `d s ≠ 0` in `Ω_B`, and let `E ∋ s` be an
intermediate field contained in `L_B` and separable algebraic over `l(s)`. If `z ∈ L_B` and
`z^{p^j} ∈ E`, then `z ∈ E`; i.e. `E ∩ L_B^{p^j} = E^{p^j}`. (Since `Ω_{E|l} → Ω_B` is injective,
`dy = 0` for `y ∈ E ∩ L_B^p`, so `y ∈ E^p` by (S3); induction on `j`.) -/
theorem mem_of_pow_pow_mem {B : ι → L} {s : L} (hs : s ∈ model l B) (hds : modelD l B s ≠ 0)
    {E : IntermediateField l L} (hsE : s ∈ E) (hE : E ≤ model l B)
    (hsep : ∀ y ∈ E, IsSeparable l⟮s⟯ y) {z : L} (hz : z ∈ model l B) {j : ℕ}
    (hzj : z ^ p ^ j ∈ E) : z ∈ E := by
  sorry

/-- Blueprint, proof of Proposition 6.12 (lines 723-725): let `E` be as in `mem_of_pow_pow_mem`.
If `v ∈ W` and `p^j • v = [b]` with `b ∈ E`, then `b^M = c • y^{p^j}` for some `M` prime to `p`,
`c ∈ lˣ` and `y ∈ E`. (If `v ≠ 0`, take a representative `(M, g)` of `v` with `g ∈ L_B`; then
`b^M = c g^{p^j}` and `g ∈ E` by `eq:Epower`. If `v = 0`, `b ∈ l`.) -/
theorem exists_pow_eq_mul_pow_pow {B : ι → L} {s : L} (hs : s ∈ model l B)
    (hds : modelD l B s ≠ 0) {E : IntermediateField l L} (hsE : s ∈ E) (hE : E ≤ model l B)
    (hsep : ∀ y ∈ E, IsSeparable l⟮s⟯ y) {v : V l L} (hv : v ∈ W l p B) {j : ℕ} {b : Lˣ}
    (hb : (b : L) ∈ E) (h : p ^ j • v = cls (constUnits l L) (.ofMul b)) :
    ∃ (M : ℕ) (c : l) (y : L), M.Coprime p ∧ c ≠ 0 ∧ y ∈ E ∧
      (b : L) ^ M = algebraMap l L c * y ^ p ^ j := by
  sorry

omit [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L] in
/-- Blueprint, proof of Proposition 6.12 (lines 726-728), the norm argument: let `s` be
transcendental over `l`, `a ≠ 0` algebraic over `l(s)`, `E = l(s, a)`, and `e j` integers such
that for every `j`, `(a s^{-e_j})^{M_j} ∈ lˣ · E^{p^j}` for some `M_j` prime to `p`. Then there
are `M ≥ 1` (namely `[E : l(s)]`) and `ε` (namely the order at `s` of `N_{E|l(s)}(a)`) with
`ε ≡ M e_j (mod p^j)` for all `j`. (Take norms to `l(s)` and compare orders at `s` in `l[s]`.) -/
theorem exists_dvd_sub_of_forall_pow_eq {s a : L} (hs : Transcendental l s) (ha0 : a ≠ 0)
    (ha : IsAlgebraic l⟮s⟯ a) (e : ℕ → ℤ)
    (h : ∀ j : ℕ, ∃ (M : ℕ) (c : l) (y : L), M.Coprime p ∧ c ≠ 0 ∧ y ∈ l⟮s, a⟯ ∧
      (a * s ^ (-e j)) ^ M = algebraMap l L c * y ^ p ^ j) :
    ∃ (M : ℕ) (ε : ℤ), 0 < M ∧ ∀ j : ℕ, (p : ℤ) ^ j ∣ ε - M * e j := by
  sorry

omit [CharP L p] [PerfectField L] [IsRelAlgClosed l L] in
/-- Blueprint, proof of Proposition 6.12 (lines 729-731), arithmetic: if `ε ≡ M r_j (mod p^j)`
for all `j`, with `M ≥ 1`, write `M = p^β n'` with `p ∤ n'`; then `p^β ∣ ε`, say `ε = p^β m'`, and
`n' r_j ≡ m' (mod p^{j-β})` for all `j ≥ β`. -/
theorem exists_dvd_sub_of_dvd {M : ℕ} (hM : 0 < M) {ε : ℤ} {r : ℕ → ℤ}
    (h : ∀ j : ℕ, (p : ℤ) ^ j ∣ ε - M * r j) :
    ∃ (n' : ℕ) (m' : ℤ) (β : ℕ), 0 < n' ∧ ∀ j : ℕ, β ≤ j → (p : ℤ) ^ (j - β) ∣ n' * r j - m' := by
  sorry

end Fields

end MilnorAlgDep
