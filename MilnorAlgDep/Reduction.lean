module

public import MilnorAlgDep.Reduction.ExtendPsi
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

The passage from `K` to its perfect closure is `theoremA_perfect_of_isPRadical`: it holds for any
field `Ki` over `K` which is perfect and `q`-radical over `K`; `theoremA_perfect_aux` uses
Mathlib's `PerfectClosure K q`, `q = ringChar K`. The extension `ψ^i` of `ψ` and the transfer of
(A1)–(A3) are in `MilnorAlgDep.Reduction.ExtendPsi`.

Note that `K` and `L` may have different characteristics until the core theorems show that they
agree: the characteristic exponent `q` used for `K^i` is that of `K`, not that of `L`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

variable {K L : Type*} [Field K] [Field L]

/-- Blueprint 6.1, reduction to perfect `K`: Theorem A for perfect `L` of positive characteristic
holds for `(K, k, ψ)` if `Ki` is a perfect field over `K` such that `K → Ki` is `q`-radical (for
instance a perfect closure of `K`). Indeed (A1)–(A4) hold for `(K^i, k^i, ψ^i)`, where
`k^i = perfectClosureIn k Ki q` and `ψ^i = extendPsi Ki q ψ`, so `theoremA_core_charP` applies;
its embedding `τ : K^i → L` restricts to `K`, with `τ⁻¹(l) ∩ K = k^i ∩ K = k`, and `k` is
relatively algebraically closed because `k^i` is.

Here `q` is the exponential characteristic of `Ki` (equivalently of `K`), which is not assumed
to be that of `L`. -/
theorem theoremA_perfect_of_isPRadical [PerfectField L] (hL : ringChar L ≠ 0)
    (q : ℕ) (Ki : Type*) [Field Ki] [Algebra K Ki] [ExpChar Ki q] [PerfectRing Ki q]
    [IsPRadical (algebraMap K Ki) q]
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
  have : PerfectField Ki := PerfectRing.toPerfectField Ki q
  have hchar : ringChar Ki = ringChar K := (Algebra.ringChar_eq K Ki).symm
  obtain ⟨hKi, hki, τ, r, hr, hτ, hψ⟩ := theoremA_core_charP hL (perfectClosureIn k Ki q) l hl
    (extendPsi Ki q ψ) (extendPsi_eq_zero_iff Ki q k ψ A1) (extendPsi_A2 Ki q k l ψ A2)
    (extendPsi_A3 Ki q l ψ A3) (fun h ↦ hchar ▸ A4 h)
  refine ⟨hchar ▸ hKi, isRelAlgClosed_of_perfectClosureIn Ki q k ψ A1 hki,
    τ.comp (algebraMap K Ki), r, hr, fun x ↦ ?_, fun x ↦ ?_⟩
  · rw [RingHom.comp_apply, hτ, algebraMap_mem_perfectClosureIn_iff Ki q k ψ A1]
  · rw [← extendPsi_algebraMap Ki q ψ x, hψ]
    rfl

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
  by_cases hL : ringChar L = 0
  · have : CharP L 0 := ringChar.of_eq hL
    have : CharZero L := CharP.charP_to_charZero L
    exact theoremA_perfect_of_charZero k l hl ψ A1 A2 A3 A4
  · obtain ⟨q, hq⟩ : ∃ q, ringChar K = q := ⟨_, rfl⟩
    have : CharP K q := ringChar.of_eq hq
    have : Fact q.Prime :=
      ⟨(CharP.char_is_prime_or_zero K q).resolve_right (hq ▸ A4 hL)⟩
    let : Algebra K (PerfectClosure K q) := (PerfectClosure.of K q).toAlgebra
    have : IsPRadical (algebraMap K (PerfectClosure K q)) q := PerfectClosure.isPRadical K q
    exact theoremA_perfect_of_isPRadical hL q (PerfectClosure K q) k l hl ψ A1 A2 A3 A4

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
  have : PerfectField M := PerfectRing.toPerfectField M p
  have hchar : ringChar M = ringChar L := (Algebra.ringChar_eq L M).symm
  let ψ' : Additive Kˣ →+ V (perfectClosureIn l M p) M :=
    (V.toPerfectClosure l M p).toAddMonoidHom.comp ψ
  have hψ' (x : Additive Kˣ) : ψ' x = V.toPerfectClosure l M p (ψ x) := rfl
  have A1' (x : Kˣ) : ψ' (.ofMul x) = 0 ↔ (x : K) ∈ k := by
    rw [hψ', map_eq_zero_iff _ (V.toPerfectClosure_bijective l M p).injective, A1]
  have A2' (x y : Kˣ) (hxy : (x : K) + y = 1) (hx : (x : K) ∉ k) :
      ¬ VAlgIndep (perfectClosureIn l M p) ![ψ' (.ofMul x), ψ' (.ofMul y)] := by
    have hfun : (fun i ↦ V.toPerfectClosure l M p (![ψ (.ofMul x), ψ (.ofMul y)] i)) =
        ![ψ' (.ofMul x), ψ' (.ofMul y)] := by
      funext i
      fin_cases i <;> rfl
    rw [← hfun, V.vAlgIndep_toPerfectClosure_iff]
    exact A2 x y hxy hx
  have A3' : ∃ x : Fin (if ringChar M = 0 then 2 else 3) → Kˣ,
      VAlgIndep (perfectClosureIn l M p) fun i ↦ ψ' (.ofMul (x i)) := by
    rw [hchar]
    obtain ⟨x, hx⟩ := A3
    exact ⟨x, (V.vAlgIndep_toPerfectClosure_iff l M p _).2 hx⟩
  obtain ⟨hK, hk, τ, r, hr, hτ, hψ⟩ := theoremA_perfect_aux k (perfectClosureIn l M p)
    (perfectClosureIn_isRelAlgClosed l M p hl) ψ' A1' A2' A3' (hchar ▸ A4)
  exact ⟨hK.trans hchar, hk, τ, r, hr, hτ, hψ⟩

end MilnorAlgDep
