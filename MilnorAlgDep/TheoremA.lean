module

public import MilnorAlgDep.Reduction
public import MilnorAlgDep.Uniqueness

/-!
# Theorem A

Blueprint, Theorem A (Section 1.1), proved in Section 6.

Let `K` and `L` be fields, `k ⊆ K` a subfield, `l ⊆ L` a relatively algebraically closed subfield
and `ψ : Kˣ → V_{L|l}` a homomorphism such that

* (A1) `ker ψ = kˣ`;
* (A2) for every `x ∈ K \ k`, `ψ(x)` and `ψ(1 - x)` are algebraically dependent over `l`;
* (A3) there are `x_1, …, x_d ∈ K` with `ψ(x_1), …, ψ(x_d)` algebraically independent over `l`,
  where `d = 2` if `char L = 0` and `d = 3` if `char L > 0`;
* (A4) if `char L > 0`, then `char K > 0`.

Then `char K = char L`, `k` is relatively algebraically closed in `K`, and there are a field
embedding `τ : K → L^i` with `τ⁻¹(l^i) = k` and `r ∈ ℚ^×` with `ψ(x) = r · [τ(x)]` for all
`x ∈ K^×`. The pair `(τ, r)` is unique up to `(Frob^j ∘ τ, p^{-j} r)`, `p` the characteristic
exponent.

This file contains the statements (frozen interface, see `PLAN.md`):

* `theoremA_perfect`: Theorem A for a perfect field `L` (then `L^i = L`, `l^i = l`), `K` arbitrary;
* `theoremA_perfect_unique`: the uniqueness clause (Blueprint Lemma 6.13), for `L` perfect;
* `theoremA`: Theorem A for arbitrary `L`, with `L^i` a perfect closure of `L`;
* `theoremA_unique`: the uniqueness clause for arbitrary `L` (an addition to the frozen interface,
  deduced from `theoremA_perfect_unique`).

## Encoding

* The subfields are `k : Subfield K` and `l : Subfield L`; "`l` is relatively algebraically
  closed in `L`" is spelled out as `∀ x : L, IsAlgebraic l x → x ∈ l`.
* `V l L = VOf (constUnits l L) = ℚ ⊗[ℤ] Additive (Lˣ ⧸ lˣ)` is the blueprint's
  `V_{L|l} = (L^×/l^×) ⊗ ℚ`, written additively, and `〚a〛` is the class `[a]` of `a : Lˣ`.
* The homomorphism `ψ : K^× → V_{L|l}` is an additive group homomorphism
  `ψ : Additive Kˣ →+ V l L`; `ψ (.ofMul x)` is the blueprint's `ψ(x)`.
* (A1) is `∀ x : Kˣ, ψ x = 0 ↔ x ∈ k`.
* (A2) quantifies over pairs of units `x, y` with `x + y = 1` (so `y = 1 - x`, and `x ≠ 0, 1` is
  automatic); this avoids junk values of `1 - x`. "Algebraically dependent" is the negation of
  `VAlgIndep l ![ψ x, ψ y]` (algebraic independence in `V l L`, see
  `MilnorAlgDep.Foundations.AlgIndep`: some, equivalently every, choice of representatives
  `N • ψ x = [a]` gives algebraically independent elements of `L`).
* (A3) is the existence of a family `x : Fin d → Kˣ` with `VAlgIndep l (ψ ∘ x)`, where
  `d = if ringChar L = 0 then 2 else 3`.
* (A4) is `ringChar L ≠ 0 → ringChar K ≠ 0` (`ringChar` is `0` in characteristic zero).
* "`k` is relatively algebraically closed in `K`" is `∀ x : K, IsAlgebraic k x → x ∈ k`, and
  "`τ⁻¹(l^i) = k`" is `∀ x : K, τ x ∈ l^i ↔ x ∈ k`.
* The conclusion `ψ(x) = r · [τ(x)]` is `ψ (.ofMul x) = r • 〚Units.map τ x〛` (in `V l L` when
  `L` is perfect; after the comparison map `V l L → V l^i L^i` in general).
* In `theoremA`, `L^i` is any field `M` with `[Algebra L M]` which is a perfect closure of `L` in
  the sense of Mathlib (`[PerfectRing M p] [IsPerfectClosure (algebraMap L M) p]`, where `p` is
  the exponential characteristic of `L`, pinned down by `[ExpChar L p]`; for `p = 1` this forces
  `M ≅ L`). Then `l^i = perfectClosureIn l M p` is the subfield of elements of `M` some
  `p ^ n`-th power of which lies in `l`, and `V l L ≅ V l^i M` via `V.toPerfectClosure`
  (bijective by `V.toPerfectClosure_bijective`; this is the blueprint's "`V_{L|l} = V_{L^i|l^i}`").
  So `theoremA` is `theoremA_perfect` applied to `M`, `l^i` and `V.toPerfectClosure ∘ ψ`, and
  the uniqueness statement for arbitrary `L`, `theoremA_unique`, is `theoremA_perfect_unique` for
  the same data.
* `K` is not assumed perfect. The blueprint first replaces `K` by its perfect closure `K^i`
  (extending `ψ` by `ψ(x) = p_K^{-j} ψ(x^{p_K^j})`); this is harmless: the hypotheses (A1)–(A4)
  transfer to `K^i` with `k^i` in place of `k`, and an embedding `K^i → L` restricts to `K` with
  `τ⁻¹(l) = k^i ∩ K = k`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

variable {K L : Type*} [Field K] [Field L]

/-- **Blueprint Theorem A**, for a perfect field `L` (so `L^i = L` and `l^i = l`); `K` is
arbitrary.

Let `k ⊆ K` be a subfield, `l ⊆ L` a relatively algebraically closed subfield of the perfect field
`L`, and `ψ : Kˣ → V_{L|l}` a homomorphism satisfying (A1)–(A4) (see the module docstring for the
encoding). Then `char K = char L`, `k` is relatively algebraically closed in `K`, and there are a
ring homomorphism (field embedding) `τ : K → L` with `τ⁻¹(l) = k` and a rational number `r ≠ 0`
with `ψ(x) = r • [τ x]` for all `x ∈ Kˣ`. Uniqueness is `theoremA_perfect_unique`. -/
theorem theoremA_perfect [PerfectField L] (k : Subfield K) (l : Subfield L)
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
        ∀ x : Kˣ, ψ (.ofMul x) = r • 〚Units.map (τ : K →* L) x〛 :=
  theoremA_perfect_aux k l hl ψ A1 A2 A3 A4

/-- **Blueprint Theorem A, uniqueness** (Blueprint Lemma 6.13), for a perfect field `L`.

If `ψ = r • [τ ·] = r' • [τ' ·]` for ring homomorphisms `τ, τ' : K → L` and rationals `r, r'`,
and `ψ ≠ 0` (which follows from (A3)), then `τ' = Frob^j ∘ τ` and `r' = p^{-j} r` for some
`j ∈ ℤ`, where `p = ringExpChar L` is the characteristic exponent of `L` and
`Frob = frobeniusEquiv L p` is the Frobenius automorphism of the perfect field `L`. In
characteristic `0` we have `p = 1` and `Frob = id`, so this says `τ' = τ` and `r' = r`.

The hypotheses are weaker than in the blueprint ((A1)–(A4) and `τ⁻¹(l) = τ'⁻¹(l) = k` are not
assumed; `r, r' ≠ 0` follows from `ψ ≠ 0`), so this is a slightly stronger statement. The
Frobenius is that of `L`; no Frobenius of `K` is needed. -/
theorem theoremA_perfect_unique [PerfectField L] (l : Subfield L)
    (hl : ∀ x : L, IsAlgebraic l x → x ∈ l)
    (ψ : Additive Kˣ →+ V l L) (hψ : ψ ≠ 0)
    (τ τ' : K →+* L) (r r' : ℚ)
    (h : ∀ x : Kˣ, ψ (.ofMul x) = r • 〚Units.map (τ : K →* L) x〛)
    (h' : ∀ x : Kˣ, ψ (.ofMul x) = r' • 〚Units.map (τ' : K →* L) x〛) :
    ∃ j : ℤ, τ' = ((frobeniusEquiv L (ringExpChar L) ^ j : L ≃+* L) : L →+* L).comp τ ∧
      r' = (ringExpChar L : ℚ) ^ (-j) * r :=
  theoremA_perfect_unique_aux l hl ψ hψ τ τ' r r' h h'

/-- **Blueprint Theorem A**, for arbitrary fields `K` and `L`.

Let `p` be the exponential characteristic of `L` and `M` a perfect closure of `L` (the blueprint's
`L^i`): `M` is perfect and `algebraMap L M` is `p`-radical (Mathlib's `IsPerfectClosure`). Let
`l^i = perfectClosureIn l M p`, the elements of `M` some `p ^ n`-th power of which lies in `l`.
Under (A1)–(A4), `char K = char L`, `k` is relatively algebraically closed in `K`, and there are a
field embedding `τ : K → M` with `τ⁻¹(l^i) = k` and `r ∈ ℚ`, `r ≠ 0`, such that
`ψ(x) = r • [τ x]` for all `x ∈ Kˣ`, where `ψ(x)` is viewed in `V l^i M` via the comparison map
`V.toPerfectClosure : V l L → V l^i M` (a bijection, `V.toPerfectClosure_bijective`).

The uniqueness clause for arbitrary `L` is `theoremA_unique`. -/
theorem theoremA (k : Subfield K) (l : Subfield L)
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
        ∀ x : Kˣ, V.toPerfectClosure l M p (ψ (.ofMul x)) = r • 〚Units.map (τ : K →* M) x〛 :=
  theoremA_aux k l hl ψ A1 A2 A3 A4 p M

/-- **Blueprint Theorem A, uniqueness** (Blueprint Lemma 6.13), for arbitrary `L`.

Let `p` be the exponential characteristic of `L`, `M` a perfect closure of `L` and
`l^i = perfectClosureIn l M p`, as in `theoremA`. If `ψ ≠ 0` and `ψ = r • [τ ·] = r' • [τ' ·]`
after the comparison map `V.toPerfectClosure : V l L → V l^i M`, for ring homomorphisms
`τ, τ' : K → M` and rationals `r, r'`, then `τ' = Frob^j ∘ τ` and `r' = p^{-j} r` for some
`j ∈ ℤ`, where `Frob = frobeniusEquiv M p` is the Frobenius automorphism of `M`. (Here
`p = ringExpChar L = ringExpChar M`; in characteristic `0`, `p = 1` and `Frob = id`, so `τ' = τ`
and `r' = r`.) This is `theoremA_perfect_unique` applied to `M`, `l^i` and
`V.toPerfectClosure ∘ ψ`. -/
theorem theoremA_unique (l : Subfield L) (hl : ∀ x : L, IsAlgebraic l x → x ∈ l)
    (ψ : Additive Kˣ →+ V l L) (hψ : ψ ≠ 0)
    (p : ℕ) [ExpChar L p] (M : Type*) [Field M] [Algebra L M] [ExpChar M p] [PerfectRing M p]
    [IsPerfectClosure (algebraMap L M) p]
    (τ τ' : K →+* M) (r r' : ℚ)
    (h : ∀ x : Kˣ, V.toPerfectClosure l M p (ψ (.ofMul x)) = r • 〚Units.map (τ : K →* M) x〛)
    (h' : ∀ x : Kˣ, V.toPerfectClosure l M p (ψ (.ofMul x)) = r' • 〚Units.map (τ' : K →* M) x〛) :
    ∃ j : ℤ, τ' = ((frobeniusEquiv M p ^ j : M ≃+* M) : M →+* M).comp τ ∧
      r' = (p : ℚ) ^ (-j) * r := by
  have : PerfectField M := PerfectRing.toPerfectField M p
  let ψ' : Additive Kˣ →+ V (perfectClosureIn l M p) M :=
    (V.toPerfectClosure l M p).toAddMonoidHom.comp ψ
  have hψ' : ψ' ≠ 0 := fun h0 ↦ hψ <| AddMonoidHom.ext fun x ↦
    (V.toPerfectClosure_bijective l M p).1 (by
      rw [AddMonoidHom.zero_apply, map_zero]
      exact DFunLike.congr_fun h0 x)
  obtain ⟨j, hj, hr⟩ := theoremA_perfect_unique (perfectClosureIn l M p)
    (perfectClosureIn_isRelAlgClosed l M p hl) ψ' hψ' τ τ' r r' h h'
  have hp : ringExpChar M = p := ringExpChar.eq M p
  subst hp
  exact ⟨j, hj, hr⟩

end MilnorAlgDep
