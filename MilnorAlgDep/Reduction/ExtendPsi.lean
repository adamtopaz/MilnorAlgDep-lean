module

public import MilnorAlgDep.Foundations.PerfectClosure

/-!
# Extending `ψ` to the perfect closure of `K`

Blueprint Section 6.1 ("Reductions"), first sentence: the homomorphism `ψ : K^× → V` extends
uniquely to `(K^i)^×` by `ψ(x) = q^{-j} ψ(x^{q^j})`, where `q` is the characteristic exponent of
`K`; the extension satisfies (A1)–(A3) with `k` replaced by its perfect closure `k^i ⊆ K^i`, and
`k^i ∩ K = k` by (A1).

Throughout, `Ki` is a field with an algebra structure over `K` such that `algebraMap K Ki` is
`q`-radical (every element of `Ki` has a `q ^ n`-th power in `K`), for instance a perfect closure
of `K` (`IsPerfectClosure (algebraMap K Ki) q`). The target of `ψ` is any `ℚ`-vector space `W`
for the construction, and `W = V l L` for the transfer of (A1)–(A3).

## Main definitions

* `MilnorAlgDep.extendPsi Ki q ψ : Additive Kiˣ →+ W`: the extension of `ψ : Additive Kˣ →+ W`.

## Main statements

* `extendPsi_spec`: if `x ^ q ^ n = y` with `y ∈ Kˣ`, then `q ^ n • ψ^i(x) = ψ(y)`.
* `extendPsi_algebraMap`: `ψ^i` extends `ψ`.
* `extendPsi_eq_zero_iff`: (A1) for `(K^i, k^i, ψ^i)`.
* `algebraMap_mem_perfectClosureIn_iff`: `k^i ∩ K = k`, assuming (A1).
* `isRelAlgClosed_of_perfectClosureIn`: if `k^i` is relatively algebraically closed in `K^i`, then
  `k` is relatively algebraically closed in `K`, assuming (A1).
* `extendPsi_A2`, `extendPsi_A3`: (A2) and (A3) for `(K^i, k^i, ψ^i)`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

variable {K : Type*} [Field K] (Ki : Type*) [Field Ki] [Algebra K Ki] (q : ℕ) [ExpChar Ki q]
  [IsPRadical (algebraMap K Ki) q]

section Construction

variable {W : Type*} [AddCommGroup W] [Module ℚ W]

namespace ExtendPsi

omit [ExpChar Ki q] in
/-- Every unit of `Ki` has a `q ^ n`-th power coming from a unit of `K`. -/
theorem exists_units_map_eq_pow (x : Kiˣ) :
    ∃ (n : ℕ) (y : Kˣ), Units.map (algebraMap K Ki : K →* Ki) y = x ^ q ^ n := by
  obtain ⟨n, y, hy⟩ := IsPRadical.pow_mem (algebraMap K Ki) q (x : Ki)
  have hy0 : y ≠ 0 := by
    rintro rfl
    rw [map_zero] at hy
    exact pow_ne_zero _ x.ne_zero hy.symm
  exact ⟨n, Units.mk0 y hy0, Units.ext (by simp [hy])⟩

omit [IsPRadical (algebraMap K Ki) q] in
/-- `Kˣ → Kiˣ` is injective. -/
theorem units_map_injective :
    Function.Injective (Units.map (algebraMap K Ki : K →* Ki)) :=
  Units.map_injective (algebraMap K Ki).injective

omit [ExpChar Ki q] [IsPRadical (algebraMap K Ki) q] in
/-- Auxiliary: two representatives `(n, y)`, `(m, z)` of the same `x` give the same value
`q ^ (-n) ψ(y) = q ^ (-m) ψ(z)`, in the form `q ^ m ψ(y) = q ^ n ψ(z)`. -/
theorem pow_smul_eq_pow_smul_of_units_map_eq (ψ : Additive Kˣ →+ W) {x : Kiˣ} {n m : ℕ}
    {y z : Kˣ} (hy : Units.map (algebraMap K Ki : K →* Ki) y = x ^ q ^ n)
    (hz : Units.map (algebraMap K Ki : K →* Ki) z = x ^ q ^ m) :
    ((q : ℚ) ^ m) • ψ (.ofMul y) = ((q : ℚ) ^ n) • ψ (.ofMul z) := by
  have hyz : y ^ q ^ m = z ^ q ^ n := by
    refine units_map_injective Ki ?_
    rw [map_pow, map_pow, hy, hz, ← pow_mul, ← pow_mul, mul_comm]
  have h := congrArg (fun u ↦ ψ (.ofMul u)) hyz
  simp only [ofMul_pow, map_nsmul] at h
  rw [← Nat.cast_pow, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, h]

/-- The underlying function of `extendPsi`: `x ↦ q ^ (-n) ψ(y)` for a chosen `n` and `y ∈ Kˣ`
with `y = x ^ q ^ n`. -/
noncomputable def extendPsiFun (ψ : Additive Kˣ →+ W) (x : Kiˣ) : W :=
  ((q : ℚ) ^ (exists_units_map_eq_pow (K := K) Ki q x).choose)⁻¹ •
    ψ (.ofMul (exists_units_map_eq_pow (K := K) Ki q x).choose_spec.choose)

theorem extendPsiFun_spec (ψ : Additive Kˣ →+ W) {x : Kiˣ} {n : ℕ} {y : Kˣ}
    (hy : Units.map (algebraMap K Ki : K →* Ki) y = x ^ q ^ n) :
    ((q : ℚ) ^ n) • extendPsiFun Ki q ψ x = ψ (.ofMul y) := by
  have hq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (expChar_ne_zero Ki q)
  have h0 := (exists_units_map_eq_pow (K := K) Ki q x).choose_spec.choose_spec
  have key := pow_smul_eq_pow_smul_of_units_map_eq Ki q ψ h0 hy
  rw [extendPsiFun, smul_comm, key, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hq), one_smul]

end ExtendPsi

open ExtendPsi

/-- Blueprint 6.1: the extension `ψ^i : (K^i)^× → W` of `ψ : K^× → W`, given by
`ψ^i(x) = q ^ (-n) ψ(x ^ q ^ n)` for any `n` such that `x ^ q ^ n ∈ K` (well defined because `W`
is a `ℚ`-vector space). -/
noncomputable def extendPsi (ψ : Additive Kˣ →+ W) : Additive Kiˣ →+ W where
  toFun x := extendPsiFun Ki q ψ x.toMul
  map_zero' := by
    have h : Units.map (algebraMap K Ki : K →* Ki) 1 = (1 : Kiˣ) ^ q ^ 0 := by simp
    have := extendPsiFun_spec Ki q ψ h
    rwa [pow_zero, one_smul, ofMul_one, map_zero] at this
  map_add' x₁ x₂ := by
    have hq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (expChar_ne_zero Ki q)
    obtain ⟨n₁, y₁, h₁⟩ := exists_units_map_eq_pow (K := K) Ki q x₁.toMul
    obtain ⟨n₂, y₂, h₂⟩ := exists_units_map_eq_pow (K := K) Ki q x₂.toMul
    have h : Units.map (algebraMap K Ki : K →* Ki) (y₁ ^ q ^ n₂ * y₂ ^ q ^ n₁) =
        (x₁ + x₂).toMul ^ q ^ (n₁ + n₂) := by
      rw [toMul_add, map_mul, map_pow, map_pow, h₁, h₂, ← pow_mul, ← pow_mul, ← pow_add,
        ← pow_add, mul_pow, add_comm n₂]
    have e := extendPsiFun_spec Ki q ψ h
    have e₁ := extendPsiFun_spec Ki q ψ h₁
    have e₂ := extendPsiFun_spec Ki q ψ h₂
    refine smul_right_injective W (pow_ne_zero (n₁ + n₂) hq) ?_
    dsimp only
    rw [e, ofMul_mul, map_add, ofMul_pow, ofMul_pow, map_nsmul, map_nsmul, ← e₁, ← e₂,
      ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, smul_smul, smul_add]
    congr 1 <;> congr 1 <;> push_cast <;> ring

/-- `q ^ n • ψ^i(x) = ψ(y)` whenever `y = x ^ q ^ n` with `y ∈ Kˣ`. -/
theorem extendPsi_spec (ψ : Additive Kˣ →+ W) {x : Kiˣ} {n : ℕ} {y : Kˣ}
    (hy : Units.map (algebraMap K Ki : K →* Ki) y = x ^ q ^ n) :
    ((q : ℚ) ^ n) • extendPsi Ki q ψ (.ofMul x) = ψ (.ofMul y) :=
  extendPsiFun_spec Ki q ψ hy

/-- `ψ^i(x) = q ^ (-n) ψ(y)` whenever `y = x ^ q ^ n` with `y ∈ Kˣ`. -/
theorem extendPsi_eq (ψ : Additive Kˣ →+ W) {x : Kiˣ} {n : ℕ} {y : Kˣ}
    (hy : Units.map (algebraMap K Ki : K →* Ki) y = x ^ q ^ n) :
    extendPsi Ki q ψ (.ofMul x) = ((q : ℚ) ^ n)⁻¹ • ψ (.ofMul y) := by
  have hq : (q : ℚ) ^ n ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (expChar_ne_zero Ki q))
  rw [← extendPsi_spec Ki q ψ hy, inv_smul_smul₀ hq]

/-- `ψ^i` extends `ψ`. -/
@[simp]
theorem extendPsi_algebraMap (ψ : Additive Kˣ →+ W) (y : Kˣ) :
    extendPsi Ki q ψ (.ofMul (Units.map (algebraMap K Ki : K →* Ki) y)) = ψ (.ofMul y) := by
  have := extendPsi_spec Ki q ψ (x := Units.map (algebraMap K Ki : K →* Ki) y) (n := 0)
    (y := y) (by rw [pow_zero, pow_one])
  rwa [pow_zero, one_smul] at this

end Construction

section Transfer

open ExtendPsi

variable (k : Subfield K) {W : Type*} [AddCommGroup W] [Module ℚ W] (ψ : Additive Kˣ →+ W)

/-- Blueprint 6.1: (A1) for `(K^i, k^i, ψ^i)` follows from (A1) for `(K, k, ψ)`, where
`k^i = perfectClosureIn k Ki q`. -/
theorem extendPsi_eq_zero_iff (A1 : ∀ x : Kˣ, ψ (.ofMul x) = 0 ↔ (x : K) ∈ k) (x : Kiˣ) :
    extendPsi Ki q ψ (.ofMul x) = 0 ↔ (x : Ki) ∈ perfectClosureIn k Ki q := by
  have hq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (expChar_ne_zero Ki q)
  obtain ⟨n, y, hy⟩ := exists_units_map_eq_pow (K := K) Ki q x
  rw [extendPsi_eq Ki q ψ hy, smul_eq_zero, A1, or_iff_right (inv_ne_zero (pow_ne_zero _ hq))]
  constructor
  · intro h
    refine ⟨n, Subfield.mem_map.2 ⟨y, h, ?_⟩⟩
    rw [← Units.val_pow_eq_pow_val, ← hy]
    rfl
  · rintro ⟨m, hm⟩
    obtain ⟨z, hz, hzx⟩ := Subfield.mem_map.1 hm
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [map_zero] at hzx
      exact pow_ne_zero _ x.ne_zero hzx.symm
    have hz' : Units.map (algebraMap K Ki : K →* Ki) (Units.mk0 z hz0) = x ^ q ^ m :=
      Units.ext (by simp [hzx])
    have hψz : ψ (.ofMul (Units.mk0 z hz0)) = 0 := (A1 _).2 hz
    have key := pow_smul_eq_pow_smul_of_units_map_eq Ki q ψ hy hz'
    rw [hψz, smul_zero, smul_eq_zero, or_iff_right (pow_ne_zero _ hq), A1] at key
    exact key

/-- Blueprint 6.1: `k^i ∩ K = k`, by (A1): if `x ^ q ^ n ∈ k` then `q ^ n ψ(x) = 0`, so
`ψ(x) = 0` and `x ∈ k`. -/
theorem algebraMap_mem_perfectClosureIn_iff (A1 : ∀ x : Kˣ, ψ (.ofMul x) = 0 ↔ (x : K) ∈ k)
    (x : K) : algebraMap K Ki x ∈ perfectClosureIn k Ki q ↔ x ∈ k := by
  refine ⟨fun h ↦ ?_, algebraMap_mem_perfectClosureIn k Ki q⟩
  rcases eq_or_ne x 0 with rfl | hx0
  · exact k.zero_mem
  have hu : ((Units.map (algebraMap K Ki : K →* Ki) (Units.mk0 x hx0) : Kiˣ) : Ki) =
      algebraMap K Ki x := rfl
  rw [← hu, ← extendPsi_eq_zero_iff Ki q k ψ A1, extendPsi_algebraMap, A1] at h
  exact h

/-- Blueprint 6.1: if `k^i` is relatively algebraically closed in `K^i`, then `k` is relatively
algebraically closed in `K` (assuming (A1), which gives `k^i ∩ K = k`). -/
theorem isRelAlgClosed_of_perfectClosureIn (A1 : ∀ x : Kˣ, ψ (.ofMul x) = 0 ↔ (x : K) ∈ k)
    (h : ∀ y : Ki, IsAlgebraic (perfectClosureIn k Ki q) y → y ∈ perfectClosureIn k Ki q) :
    ∀ x : K, IsAlgebraic k x → x ∈ k := by
  intro x hx
  rw [← algebraMap_mem_perfectClosureIn_iff Ki q k ψ A1]
  refine h _ (hx.ringHom_of_comp_eq
    ((algebraMap K Ki).restrict k (perfectClosureIn k Ki q)
      fun z hz ↦ algebraMap_mem_perfectClosureIn k Ki q hz)
    (algebraMap K Ki) ?_ rfl)
  exact fun a b hab ↦ Subtype.ext ((algebraMap K Ki).injective (congrArg Subtype.val hab))

end Transfer

section TransferV

open ExtendPsi

variable {L : Type*} [Field L] (k : Subfield K) (l : Subfield L) (ψ : Additive Kˣ →+ V l L)

/-- Blueprint 6.1: (A2) for `(K^i, k^i, ψ^i)`. If `x ∈ K^i \ k^i`, `x + y = 1` and
`x ^ q ^ n = a ∈ K`, then `y ^ q ^ n = 1 - a`, `a ∉ k`, and `ψ^i(x)`, `ψ^i(y)` are the multiples
`q ^ (-n) ψ(a)`, `q ^ (-n) ψ(1 - a)`, which are algebraically dependent by (A2) for `K`. -/
theorem extendPsi_A2
    (A2 : ∀ x y : Kˣ, (x : K) + y = 1 → (x : K) ∉ k →
      ¬ VAlgIndep l ![ψ (.ofMul x), ψ (.ofMul y)]) :
    ∀ x y : Kiˣ, (x : Ki) + y = 1 → (x : Ki) ∉ perfectClosureIn k Ki q →
      ¬ VAlgIndep l ![extendPsi Ki q ψ (.ofMul x), extendPsi Ki q ψ (.ofMul y)] := by
  intro x y hxy hx
  have hq : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (expChar_ne_zero Ki q)
  obtain ⟨n, a, ha⟩ := exists_units_map_eq_pow (K := K) Ki q x
  have ha' : algebraMap K Ki a = (x : Ki) ^ q ^ n := congrArg Units.val ha
  have h1 : (x : Ki) ^ q ^ n + (y : Ki) ^ q ^ n = 1 := by
    rw [← add_pow_expChar_pow, hxy, one_pow]
  have hb : (y : Ki) ^ q ^ n = algebraMap K Ki (1 - a) := by
    rw [map_sub, map_one, ha']
    linear_combination h1
  have hb0 : 1 - (a : K) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hb
    exact pow_ne_zero _ y.ne_zero hb
  set b : Kˣ := Units.mk0 _ hb0
  have hb' : Units.map (algebraMap K Ki : K →* Ki) b = y ^ q ^ n :=
    Units.ext (by simp [b, hb])
  have hak : (a : K) ∉ k := fun h ↦ hx ⟨n, Subfield.mem_map.2 ⟨a, h, ha'⟩⟩
  have hab : (a : K) + b = 1 := by simp [b]
  set c : ℚ := ((q : ℚ) ^ n)⁻¹
  have hc : c ≠ 0 := inv_ne_zero (pow_ne_zero _ hq)
  have hfun : (fun i ↦ (fun _ ↦ c) i • ![ψ (.ofMul a), ψ (.ofMul b)] i) =
      ![c • ψ (.ofMul a), c • ψ (.ofMul b)] := by
    funext i
    fin_cases i <;> rfl
  rw [extendPsi_eq Ki q ψ ha, extendPsi_eq Ki q ψ hb', ← hfun, VAlgIndep.smul_iff fun _ ↦ hc]
  exact A2 a b hab hak

/-- Blueprint 6.1: (A3) for `(K^i, k^i, ψ^i)` is inherited from (A3) for `(K, k, ψ)`, since `ψ^i`
extends `ψ`. -/
theorem extendPsi_A3 {ι : Type*} (A3 : ∃ x : ι → Kˣ, VAlgIndep l fun i ↦ ψ (.ofMul (x i))) :
    ∃ x : ι → Kiˣ, VAlgIndep l fun i ↦ extendPsi Ki q ψ (.ofMul (x i)) := by
  obtain ⟨x, hx⟩ := A3
  exact ⟨fun i ↦ Units.map (algebraMap K Ki : K →* Ki) (x i), by
    simpa only [extendPsi_algebraMap] using hx⟩

end TransferV

end MilnorAlgDep
