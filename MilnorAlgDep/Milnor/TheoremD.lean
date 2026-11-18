module

public import MilnorAlgDep.Milnor.PerfectClosure
public import MilnorAlgDep.Milnor.TheoremC
public import MilnorAlgDep.TheoremA

/-!
# Theorem D (isomorphisms)

Blueprint, Theorem D (Section 1.2), proved in Section 7.4.

Let `K` and `L` be fields each of which contains three elements that are algebraically
independent over the prime field; if one of them has characteristic `0`, two such elements
suffice. Then every isomorphism of graded `ℚ`-algebras `φ : 𝒦_*(K) → 𝒦_*(L)` is of the form
`r^deg ∘ τ_*` for an isomorphism of fields `τ : K^i → L^i` and some `r ∈ ℚ^×`. In particular
`K^i ≅ L^i`.

## Encoding

* The fields are arbitrary (not assumed perfect). The hypothesis on transcendence degrees is: with
  `d = 2` if `ringChar K = 0` or `ringChar L = 0`, and `d = 3` otherwise, both `K` and `L` contain
  a family `Fin d → _` algebraically independent over the prime field `⊥ : Subfield _`.
* `𝒦_*(K) = MilnorKQ (⊥ : Subgroup Kˣ)` (see `MilnorAlgDep.Milnor.Defs`). "Isomorphism of graded
  `ℚ`-algebras" is a `ℚ`-algebra isomorphism `φ` which is graded (`MilnorKQ.IsGraded`); its
  inverse is then graded too (`MilnorKQ.IsGraded.symm`, since `𝒦_*` is the direct sum of its
  homogeneous parts).
* `K^i` is any perfect closure of `K` in the sense of Mathlib: a perfect field `Ki` with
  `[Algebra K Ki]` and `IsPerfectClosure (algebraMap K Ki) pK`, where `pK` is the exponential
  characteristic of `K` (pinned down by `[ExpChar K pK]`); similarly `L^i`, with its own `pL`
  (that `pK = pL` is part of the conclusion, since `K^i ≅ L^i`).
* Since `φ` is a map `𝒦_*(K) → 𝒦_*(L)`, "`φ = r^deg ∘ τ_*`" is read through the maps
  `𝒦_*(K) → 𝒦_*(K^i)` and `𝒦_*(L) → 𝒦_*(L^i)` induced by the inclusions (both are isomorphisms,
  as `𝒦_*` does not change under purely inseparable extensions): the square
  `𝒦_*(K) → 𝒦_*(L) → 𝒦_*(L^i)` equals `𝒦_*(K) → 𝒦_*(K^i) → 𝒦_*(L^i)`, the last map being
  `r^deg ∘ τ_*`.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf MilnorKQ

variable {K L : Type*} [Field K] [Field L]

namespace TheoremD

/-- Blueprint 7.4: if `σ` is an endomorphism of a perfect field `M` containing a transcendental
element, and `s [σ x] = [x]` in `M^×_ℚ` for all `x`, then `σ` is a power of the Frobenius (by the
uniqueness in Theorem A, applied to the canonical map `M^× → V_{M|k₀}`), hence bijective. -/
theorem bijective_of_smul_cls_map_eq {M : Type*} [Field M] [PerfectField M]
    (hM : ∃ x : M, Transcendental (⊥ : Subfield M) x) (σ : M →+* M) (s : ℚ)
    (h : ∀ x : Mˣ, s • cls (⊥ : Subgroup Mˣ) (.ofMul (Units.map (σ : M →* M) x)) =
      cls ⊥ (.ofMul x)) :
    Function.Bijective σ := by
  have : IsRelAlgClosed (primeAlgClosure M) M :=
    IsRelAlgClosed.of_subfield isRelAlgClosed_primeAlgClosure
  let ψ : Additive Mˣ →+ V (primeAlgClosure M) M := (VOf.proj bot_le).toAddMonoidHom.comp (cls ⊥)
  have h₁ (x : Mˣ) : ψ (.ofMul x) = (1 : ℚ) • 〚Units.map (RingHom.id M : M →* M) x〛 := by
    change VOf.proj _ _ = _
    rw [show Units.map (RingHom.id M : M →* M) x = x from Units.ext rfl, proj_cls, one_smul]
  have h₂ (x : Mˣ) : ψ (.ofMul x) = s • 〚Units.map (σ : M →* M) x〛 := by
    change VOf.proj _ _ = _
    rw [← h x, map_smul, proj_cls]
  have hψ : ψ ≠ 0 := by
    obtain ⟨x, hx⟩ := hM
    intro h0
    have h0x := DFunLike.congr_fun h0 (.ofMul (Units.mk0 x hx.ne_zero))
    change VOf.proj _ _ = _ at h0x
    rw [proj_cls, AddMonoidHom.zero_apply, V.cls_eq_zero_iff, mem_constUnits_subfield,
      Units.val_mk0, mem_primeAlgClosure] at h0x
    exact hx h0x
  obtain ⟨j, hj, -⟩ :=
    theoremA_perfect_unique _ isRelAlgClosed_primeAlgClosure ψ hψ (RingHom.id M) σ 1 s h₁ h₂
  rw [hj, RingHom.comp_id]
  exact (frobeniusEquiv M (ringExpChar M) ^ j).bijective

/-- Blueprint 7.4: Theorem C for a graded homomorphism `φ : 𝒦_*(K) → 𝒦_*(L)` of perfect fields
whose degree one part is bijective: (A3) holds as soon as `L` contains `d` elements algebraically
independent over the prime field (with `d` as in (A3)), because `φ₁` is surjective. -/
theorem exists_eq_of_degOne_bijective [PerfectField K] [PerfectField L]
    (φ : MilnorKQ (⊥ : Subgroup Kˣ) →ₐ[ℚ] MilnorKQ (⊥ : Subgroup Lˣ)) (hφ : IsGraded φ)
    (hφ₁ : Function.Bijective (degOne φ)) (hK : ∃ x : K, Transcendental (⊥ : Subfield K) x)
    (hL : ∃ y : Fin (if ringChar L = 0 then 2 else 3) → L,
      AlgebraicIndependent (⊥ : Subfield L) y)
    (A4 : ringChar L ≠ 0 → ringChar K ≠ 0) :
    ∃ (τ : K →+* L) (r : ℚ), r ≠ 0 ∧ φ = (degScale (⊥ : Subgroup Lˣ) r).comp (map τ bot_le) := by
  obtain ⟨y, hy⟩ := hL
  let yu i := Units.mk0 (y i) (hy.ne_zero i)
  choose w hw using fun i ↦ hφ₁.2 (cls ⊥ (.ofMul (yu i)))
  choose N x hN hx using fun i ↦ exists_nsmul_eq_cls (w i)
  have A3 : ∃ x : Fin (if ringChar L = 0 then 2 else 3) → Kˣ,
      VAlgIndep (primeAlgClosure L)
        fun i ↦ VOf.proj (bot_le : ⊥ ≤ constUnits (primeAlgClosure L) L) (degOne φ 〚x i〛) := by
    refine ⟨x, ?_⟩
    have hv : (fun i ↦ VOf.proj (bot_le : ⊥ ≤ constUnits (primeAlgClosure L) L)
        (degOne φ 〚x i〛)) =
        fun i ↦ (N i : ℚ) • cls (constUnits (primeAlgClosure L) L) (.ofMul (yu i)) := by
      ext i
      rw [← hx i, map_nsmul, hw i, map_nsmul, proj_cls, Nat.cast_smul_eq_nsmul]
    rw [hv, VAlgIndep.smul_iff fun i ↦ Nat.cast_ne_zero.2 (hN i).ne', VAlgIndep.cls_iff]
    exact (algebraicIndependent_bot_iff fun _ ↦ mem_primeAlgClosure).1 hy
  obtain ⟨τ, r, hr, -, hφτ⟩ := theoremC (primeAlgClosure K) (fun _ ↦ mem_primeAlgClosure)
    (primeAlgClosure L) (fun _ ↦ mem_primeAlgClosure) hK φ hφ hφ₁.1 A3 A4
  exact ⟨τ, r, hr, hφτ⟩

/-- If `φ = r^deg ∘ τ_*` and `ψ = r'^deg ∘ τ'_*` with `ψ ∘ φ = id`, then
`r' r [τ' τ x] = [x]`. -/
theorem smul_cls_comp_eq {M N : Type*} [Field M] [Field N]
    {φ : MilnorKQ (⊥ : Subgroup Mˣ) →ₐ[ℚ] MilnorKQ (⊥ : Subgroup Nˣ)}
    {ψ : MilnorKQ (⊥ : Subgroup Nˣ) →ₐ[ℚ] MilnorKQ (⊥ : Subgroup Mˣ)}
    (hψφ : ∀ y, ψ (φ y) = y) {τ : M →+* N} {τ' : N →+* M} {r r' : ℚ}
    (hφ : φ = (degScale (⊥ : Subgroup Nˣ) r).comp (map τ bot_le))
    (hψ : ψ = (degScale (⊥ : Subgroup Mˣ) r').comp (map τ' bot_le)) (x : Mˣ) :
    (r' * r) • cls (⊥ : Subgroup Mˣ) (.ofMul (Units.map ((τ'.comp τ : M →+* M) : M →* M) x)) =
      cls ⊥ (.ofMul x) := by
  have h := hψφ (ι ⊥ (cls ⊥ (.ofMul x)))
  rw [hφ, hψ] at h
  simp only [AlgHom.comp_apply, map_ι, degScale_ι, map_smul, mapRingHom_cls, smul_smul] at h
  rw [← map_smul, ι_inj, mul_comm] at h
  exact h

end TheoremD

open TheoremD

/-- **Blueprint Theorem D** (isomorphisms). Let `K` and `L` be fields each containing `d`
elements algebraically independent over the prime field, where `d = 2` if one of them has
characteristic `0` and `d = 3` otherwise. Let `φ : 𝒦_*(K) ≅ 𝒦_*(L)` be an isomorphism of graded
`ℚ`-algebras (a graded algebra isomorphism; its inverse is then graded by
`MilnorKQ.IsGraded.symm`), and let `K^i`, `L^i` be perfect closures. Then there are a field
isomorphism `τ : K^i ≅ L^i` and `r ∈ ℚ`, `r ≠ 0`, such that `φ` corresponds to `r^deg ∘ τ_*`
under the maps `𝒦_*(K) → 𝒦_*(K^i)` and `𝒦_*(L) → 𝒦_*(L^i)` induced by the inclusions. -/
theorem theoremD
    (hK : ∃ x : Fin (if ringChar K = 0 ∨ ringChar L = 0 then 2 else 3) → K,
      AlgebraicIndependent (⊥ : Subfield K) x)
    (hL : ∃ x : Fin (if ringChar K = 0 ∨ ringChar L = 0 then 2 else 3) → L,
      AlgebraicIndependent (⊥ : Subfield L) x)
    (φ : MilnorKQ (⊥ : Subgroup Kˣ) ≃ₐ[ℚ] MilnorKQ (⊥ : Subgroup Lˣ))
    (hφ : IsGraded φ.toAlgHom)
    (pK : ℕ) [ExpChar K pK] (Ki : Type*) [Field Ki] [Algebra K Ki] [ExpChar Ki pK]
    [PerfectRing Ki pK] [IsPerfectClosure (algebraMap K Ki) pK]
    (pL : ℕ) [ExpChar L pL] (Li : Type*) [Field Li] [Algebra L Li] [ExpChar Li pL]
    [PerfectRing Li pL] [IsPerfectClosure (algebraMap L Li) pL] :
    ∃ (τ : Ki ≃+* Li) (r : ℚ), r ≠ 0 ∧
      (map (algebraMap L Li) bot_le).comp φ.toAlgHom =
        ((degScale (⊥ : Subgroup Liˣ) r).comp (map (τ : Ki →+* Li) bot_le)).comp
          (map (algebraMap K Ki) bot_le) := by
  have : PerfectField Ki := PerfectRing.toPerfectField Ki pK
  have : PerfectField Li := PerfectRing.toPerfectField Li pL
  -- Replace `K`, `L` by their perfect closures: `φ' : 𝒦_*(K^i) ≅ 𝒦_*(L^i)`.
  let jK := MilnorKQ.perfectClosureEquiv K Ki pK
  let jL := MilnorKQ.perfectClosureEquiv L Li pL
  let φ' : MilnorKQ (⊥ : Subgroup Kiˣ) ≃ₐ[ℚ] MilnorKQ (⊥ : Subgroup Liˣ) :=
    (jK.symm.trans φ).trans jL
  have hφ' : IsGraded φ'.toAlgHom := (isGraded_perfectClosureEquiv L Li pL).comp
    (hφ.comp (isGraded_perfectClosureEquiv_symm K Ki pK))
  have hφ's : IsGraded φ'.symm.toAlgHom := hφ'.symm
  have hφ'₁ := degOne_bijective φ' hφ'
  have hφ's₁ := degOne_bijective φ'.symm hφ's
  -- characteristics and transcendental elements
  have hcK : ringChar Ki = ringChar K := (ringChar_eq_of_ringHom (algebraMap K Ki)).symm
  have hcL : ringChar Li = ringChar L := (ringChar_eq_of_ringHom (algebraMap L Li)).symm
  set d := if ringChar K = 0 ∨ ringChar L = 0 then 2 else 3 with hd
  obtain ⟨xK, hxK⟩ := hK
  obtain ⟨xL, hxL⟩ := hL
  have hd2 : 2 ≤ d := by
    rw [hd]
    split_ifs <;> norm_num
  have hxK' : AlgebraicIndependent (⊥ : Subfield Ki) (algebraMap K Ki ∘ xK) :=
    (algebraicIndependent_bot_map_iff _).2 hxK
  have hxL' : AlgebraicIndependent (⊥ : Subfield Li) (algebraMap L Li ∘ xL) :=
    (algebraicIndependent_bot_map_iff _).2 hxL
  have htK : ∃ x : Ki, Transcendental (⊥ : Subfield Ki) x :=
    ⟨_, hxK'.transcendental ⟨0, by omega⟩⟩
  have htL : ∃ x : Li, Transcendental (⊥ : Subfield Li) x :=
    ⟨_, hxL'.transcendental ⟨0, by omega⟩⟩
  have famK (h : (if ringChar Ki = 0 then 2 else 3) ≤ d) :
      ∃ y : Fin (if ringChar Ki = 0 then 2 else 3) → Ki, AlgebraicIndependent (⊥ : Subfield Ki) y :=
    ⟨(algebraMap K Ki ∘ xK) ∘ Fin.castLE h, hxK'.comp _ (Fin.castLE_injective h)⟩
  have famL (h : (if ringChar Li = 0 then 2 else 3) ≤ d) :
      ∃ y : Fin (if ringChar Li = 0 then 2 else 3) → Li, AlgebraicIndependent (⊥ : Subfield Li) y :=
    ⟨(algebraMap L Li ∘ xL) ∘ Fin.castLE h, hxL'.comp _ (Fin.castLE_injective h)⟩
  -- The mixed characteristic cases are excluded by Theorem C: an embedding `L^i → K^i` (or
  -- `K^i → L^i`) forces equal characteristics.
  have hchar : ringChar K = 0 ↔ ringChar L = 0 := by
    constructor
    · intro hK0
      by_contra hL0
      obtain ⟨τ', -⟩ := exists_eq_of_degOne_bijective φ'.symm.toAlgHom hφ's hφ's₁ htL
        (famK (by simp [hd, hcK, hK0])) fun h ↦ absurd (hcK.trans hK0) h
      exact hL0 (by rw [← hcL, ringChar_eq_of_ringHom τ', hcK, hK0])
    · intro hL0
      by_contra hK0
      obtain ⟨τ, -⟩ := exists_eq_of_degOne_bijective φ'.toAlgHom hφ' hφ'₁ htK
        (famL (by simp [hd, hcL, hL0])) fun h ↦ absurd (hcL.trans hL0) h
      exact hK0 (by rw [← hcK, ringChar_eq_of_ringHom τ, hcL, hL0])
  -- So (A4) holds in both directions, and Theorem C applies to `φ'` and `φ'⁻¹`.
  have A4 : ringChar Li ≠ 0 → ringChar Ki ≠ 0 := by
    rw [hcK, hcL]
    exact fun h h' ↦ h (hchar.1 h')
  have A4' : ringChar Ki ≠ 0 → ringChar Li ≠ 0 := by
    rw [hcK, hcL]
    exact fun h h' ↦ h (hchar.2 h')
  have hdL : (if ringChar Li = 0 then 2 else 3) ≤ d := by
    rw [hd, hcL]
    by_cases h : ringChar L = 0
    · simp [h]
    · simp [h, (not_congr hchar).2 h]
  have hdK : (if ringChar Ki = 0 then 2 else 3) ≤ d := by
    rw [hd, hcK]
    by_cases h : ringChar K = 0
    · simp [h]
    · simp [h, (not_congr hchar).1 h]
  obtain ⟨τ, r, hr, hτ⟩ := exists_eq_of_degOne_bijective φ'.toAlgHom hφ' hφ'₁ htK (famL hdL) A4
  obtain ⟨τ', r', -, hτ'⟩ :=
    exists_eq_of_degOne_bijective φ'.symm.toAlgHom hφ's hφ's₁ htL (famK hdK) A4'
  -- `τ' ∘ τ` and `τ ∘ τ'` are powers of the Frobenius (uniqueness in Theorem A), so `τ` is an
  -- isomorphism.
  have hb : Function.Bijective (τ.comp τ') := bijective_of_smul_cls_map_eq htL _ _
    (smul_cls_comp_eq (fun y ↦ φ'.apply_symm_apply y) hτ' hτ)
  let τe : Ki ≃+* Li :=
    RingEquiv.ofBijective τ ⟨τ.injective, (show Function.Surjective (τ ∘ τ') from hb.2).of_comp⟩
  refine ⟨τe, r, hr, ?_⟩
  have hτe : (τe : Ki →+* Li) = τ := RingHom.ext fun _ ↦ rfl
  rw [hτe, ← hτ]
  refine AlgHom.ext fun y ↦ ?_
  change jL (φ y) = jL (φ (jK.symm (jK y)))
  rw [AlgEquiv.symm_apply_apply]

end MilnorAlgDep
