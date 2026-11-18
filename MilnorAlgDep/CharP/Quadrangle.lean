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

## Proof

We follow the blueprint. Choose `(a, b, d)` normalized with `a = a₀`, then `(b, c, e)`
normalized, and extend `a, b, c` to a transcendence basis `B` of `L / l`. In the model `L_B` the
elements `a, b, c` are model generators, and so are `d, e` by Lemma 4.6(b); in coordinates with
respect to the basis `(d B i)ᵢ` of `Ω_B` we get `d d = d_a da + d_b db`, `d e = e_b db + e_c dc`
with non-zero coefficients (`IsNormalized.coord_modelD`). Let `g, h` be model generators of
`G, H`. By the lax property (`omega_le_sup_of_isAlgebraic`), `d g` lies in the planes
`ω(D) + ω(C)` and `ω(A) + ω(E)`, which forces all three coordinates of `d g` to be non-zero
(`coord_ne_zero_of_mem_sup_of_mem_sup`); then `d h`, which lies in `ω(A) + ω(C)` and
`ω(B) + ω(G)`, has non-zero `a`- and `c`-coordinates and zero `b`-coordinate
(`coord_of_mem_sup_of_mem_sup`). Comparing coordinates shows that the lines of the points in each
of the four remaining collinear triples are pairwise distinct, and Lemma 4.6(d)
(`isNormalized_of_hgt_eq_zero`) finishes the proof.

The blueprint first proves the incidences `G ∉ {A, C, D, E}` and `H ∉ {A, B, C, G}`; here they
are not needed separately: they follow from the distinctness of the lines (only the inclusion
half of propagation is used, and it does not need the planes to be distinct).

## Auxiliary results

* `coord_ne_zero_of_mem_sup_of_mem_sup`, `coord_of_mem_sup_of_mem_sup`: the linear algebra of
  the points `G` and `H`.
* `isAlgebraic_adjoin_pair_of_samePoint`: "`Z` lies on `⟨X, Y⟩`" only depends on the points.
* `modelBasis_coord_self`, `modelBasis_coord_of_ne`, `omega_ne_of_coord`,
  `algebraicIndependent_pair_of_omega_ne`, `isCollinearTriple_of_omega_ne`: lines of points in
  coordinates.
* `IsNormalized.coord_modelD`: the coordinates of `d z` for a normalized triple `(B i, B j, z)`.
* `quadrangle_of_isTranscendenceBasis`: the main step, inside the model.
-/

@[expose] public section

namespace MilnorAlgDep

open IntermediateField

section LinearAlgebra

/-! ### The linear algebra of the points `G` and `H` -/

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {f₁ f₂ f₃ : V →ₗ[K] K}

/-- The point `G` in the proof of Lemma 5.1: let `f₁, f₂, f₃` be the coordinate functions for
`da, db, dc`, and let `d d = d_a da + d_b db` and `d e = e_b db + e_c dc` with non-zero
coefficients. Then every non-zero vector in both planes `L_B d d + L_B dc` and `L_B da + L_B d e`
has three non-zero coordinates. -/
theorem coord_ne_zero_of_mem_sup_of_mem_sup {ua uc ud ue ug : V} (ha₁ : f₁ ua = 1)
    (ha₂ : f₂ ua = 0) (ha₃ : f₃ ua = 0) (hc₁ : f₁ uc = 0) (hc₂ : f₂ uc = 0) (hc₃ : f₃ uc = 1)
    (hd₁ : f₁ ud ≠ 0) (hd₂ : f₂ ud ≠ 0) (hd₃ : f₃ ud = 0) (he₁ : f₁ ue = 0) (he₂ : f₂ ue ≠ 0)
    (he₃ : f₃ ue ≠ 0) (hg : ug ≠ 0) (hgDC : ug ∈ K ∙ ud ⊔ K ∙ uc) (hgAE : ug ∈ K ∙ ua ⊔ K ∙ ue) :
    f₁ ug ≠ 0 ∧ f₂ ug ≠ 0 ∧ f₃ ug ≠ 0 := by
  obtain ⟨_, h1, _, h2, rfl⟩ := Submodule.mem_sup.1 hgDC
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 h2
  obtain ⟨_, h3, _, h4, hst⟩ := Submodule.mem_sup.1 hgAE
  obtain ⟨s', rfl⟩ := Submodule.mem_span_singleton.1 h3
  obtain ⟨t', rfl⟩ := Submodule.mem_span_singleton.1 h4
  have e₁ := congrArg f₁ hst
  have e₂ := congrArg f₂ hst
  have e₃ := congrArg f₃ hst
  simp only [map_add, map_smul, smul_eq_mul, ha₁, ha₂, ha₃, hc₁, hc₂, hc₃, hd₃, he₁, mul_one,
    mul_zero, add_zero, zero_add] at e₁ e₂ e₃ ⊢
  have hs : s ≠ 0 := by
    rintro rfl
    simp only [zero_mul, mul_eq_zero, he₂, or_false] at e₁ e₂
    apply hg
    rw [← hst, e₁, e₂, zero_smul, zero_smul, add_zero]
  have ht' : t' ≠ 0 := by
    rintro rfl
    rw [zero_mul, eq_comm] at e₂
    exact mul_ne_zero hs hd₂ e₂
  exact ⟨mul_ne_zero hs hd₁, mul_ne_zero hs hd₂, e₃ ▸ mul_ne_zero ht' he₃⟩

/-- The point `H` in the proof of Lemma 5.1: let `f₁, f₂, f₃` be the coordinate functions for
`da, db, dc`, and let `d g` have non-zero first and third coordinates. Then every non-zero vector
in both planes `L_B da + L_B dc` and `L_B db + L_B d g` has non-zero first and third coordinates
and zero second coordinate. -/
theorem coord_of_mem_sup_of_mem_sup {ua ub uc ug uh : V} (ha₁ : f₁ ua = 1) (ha₂ : f₂ ua = 0)
    (ha₃ : f₃ ua = 0) (hb₁ : f₁ ub = 0) (hb₂ : f₂ ub = 1) (hb₃ : f₃ ub = 0) (hc₁ : f₁ uc = 0)
    (hc₂ : f₂ uc = 0) (hc₃ : f₃ uc = 1) (hg₁ : f₁ ug ≠ 0) (hg₃ : f₃ ug ≠ 0) (hh : uh ≠ 0)
    (hhAC : uh ∈ K ∙ ua ⊔ K ∙ uc) (hhBG : uh ∈ K ∙ ub ⊔ K ∙ ug) :
    f₁ uh ≠ 0 ∧ f₂ uh = 0 ∧ f₃ uh ≠ 0 := by
  obtain ⟨_, h1, _, h2, rfl⟩ := Submodule.mem_sup.1 hhAC
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 h2
  obtain ⟨_, h3, _, h4, hst⟩ := Submodule.mem_sup.1 hhBG
  obtain ⟨s', rfl⟩ := Submodule.mem_span_singleton.1 h3
  obtain ⟨t', rfl⟩ := Submodule.mem_span_singleton.1 h4
  have e₁ := congrArg f₁ hst
  have e₂ := congrArg f₂ hst
  have e₃ := congrArg f₃ hst
  simp only [map_add, map_smul, smul_eq_mul, ha₁, ha₂, ha₃, hb₁, hb₂, hb₃, hc₁, hc₂, hc₃,
    mul_one, mul_zero, add_zero, zero_add, true_and] at e₁ e₂ e₃ ⊢
  have ht' : t' ≠ 0 := by
    rintro rfl
    simp only [zero_mul, add_zero] at e₂
    apply hh
    rw [← hst, e₂, zero_smul, zero_smul, add_zero]
  exact ⟨e₁ ▸ mul_ne_zero ht' hg₁, e₃ ▸ mul_ne_zero ht' hg₃⟩

end LinearAlgebra

section Model

/-! ### Lines of points in coordinates -/

variable {l L : Type*} [Field l] [Field L] [Algebra l L] {ι : Type*} {B : ι → L}

-- TODO(move): `MilnorAlgDep.CharP.Normalized` (next to `IsCollinearTriple.of_samePoint`).
/-- "`Z` lies on the line `⟨X, Y⟩`" only depends on the points `X, Y, Z`: if `z` is algebraic over
`l(x, y)`, then so is `z'` over `l(x', y')` for `x', y', z'` in the points of `x, y, z`. -/
theorem isAlgebraic_adjoin_pair_of_samePoint {x y z x' y' z' : L} (h : IsAlgebraic l⟮x, y⟯ z)
    (hx : SamePoint l x' x) (hy : SamePoint l y' y) (hz : SamePoint l z' z) :
    IsAlgebraic l⟮x', y'⟯ z' := by
  set M := AlgebraicIndependent.matroid l L
  have key : ∀ {s : Set L} {w : L}, IsAlgebraic (adjoin l s) w ↔ w ∈ M.closure s := by
    intro s w
    rw [mem_matroid_closure_iff, IntermediateField.isAlgebraic_adjoin_iff]
  have hsub : ({x, y} : Set L) ⊆ M.closure {x', y'} := by
    refine Set.insert_subset ?_ (Set.singleton_subset_iff.2 ?_)
    · exact M.closure_mono (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
        (isAlgebraic_adjoin_simple_iff_mem_closure.1 hx.symm.isAlgebraic)
    · exact M.closure_mono (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem _ rfl))
        (isAlgebraic_adjoin_simple_iff_mem_closure.1 hy.symm.isAlgebraic)
  have hz' : z ∈ M.closure {x', y'} := M.closure_subset_closure_of_subset_closure hsub (key.1 h)
  exact key.2 (M.closure_subset_closure_of_subset_closure (Set.singleton_subset_iff.2 hz')
    (isAlgebraic_adjoin_simple_iff_mem_closure.1 hz.isAlgebraic))

-- TODO(move): `MilnorAlgDep.CharP.Model`.
/-- The `i`-th coordinate of `d (B i)` with respect to the basis `(d B j)ⱼ` of `Ω_B` is `1`. -/
theorem modelBasis_coord_self (hB : AlgebraicIndependent l B) (i : ι) :
    (modelBasis hB).coord i (modelD l B (B i)) = 1 := by
  rw [← modelBasis_apply hB i, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_same]

-- TODO(move): `MilnorAlgDep.CharP.Model`.
/-- The `i`-th coordinate of `d (B j)`, `j ≠ i`, with respect to the basis `(d B k)ₖ` of `Ω_B` is
`0`. -/
theorem modelBasis_coord_of_ne (hB : AlgebraicIndependent l B) {i j : ι} (h : j ≠ i) :
    (modelBasis hB).coord i (modelD l B (B j)) = 0 := by
  rw [← modelBasis_apply hB j, Module.Basis.coord_apply, Module.Basis.repr_self,
    Finsupp.single_eq_of_ne' h]

variable (p : ℕ) [Fact p.Prime] [CharP L p] [PerfectField L] [IsRelAlgClosed l L]

omit [IsRelAlgClosed l L] in
/-- Two lines `ω(Q_x) = L_B v_x`, `ω(Q_y) = L_B v_y` differ if some linear form vanishes on exactly
one of `v_x, v_y`. -/
theorem omega_ne_of_coord {x y : L} {vx vy : Ω[model l B⁄l]}
    (hx : omega l p B x = model l B ∙ vx) (hy : omega l p B y = model l B ∙ vy)
    (f : Ω[model l B⁄l] →ₗ[model l B] model l B)
    (h : f vx ≠ 0 ∧ f vy = 0 ∨ f vx = 0 ∧ f vy ≠ 0) : omega l p B x ≠ omega l p B y := by
  rw [hx, hy]
  rcases h with h | h
  · exact span_singleton_ne_of_apply f h.1 h.2
  · exact (span_singleton_ne_of_apply f h.2 h.1).symm

/-- Points with different lines are different: if `ω(Q_x) ≠ ω(Q_y)`, then `x, y` are
algebraically independent. -/
theorem algebraicIndependent_pair_of_omega_ne (hB : IsTranscendenceBasis l B) {x y : L}
    (hx : Transcendental l x) (hy : Transcendental l y) (h : omega l p B x ≠ omega l p B y) :
    AlgebraicIndependent l ![x, y] := by
  by_contra hdep
  exact h (omega_eq_of_samePoint p hB (samePoint_iff_not_algebraicIndependent.2 ⟨hx, hy, hdep⟩))

/-- If `z` is algebraic over `l(x, y)` and the lines of `Q_x, Q_y, Q_z` are pairwise distinct,
then `Q_x, Q_y, Q_z` are three distinct collinear points. -/
theorem isCollinearTriple_of_omega_ne (hB : IsTranscendenceBasis l B) {x y z : L}
    (hx : Transcendental l x) (hy : Transcendental l y) (hz : Transcendental l z)
    (hxy : omega l p B x ≠ omega l p B y) (hxz : omega l p B x ≠ omega l p B z)
    (hyz : omega l p B y ≠ omega l p B z) (halg : IsAlgebraic l⟮x, y⟯ z) :
    IsCollinearTriple l x y z :=
  ⟨algebraicIndependent_pair_of_omega_ne p hB hx hy hxy,
    algebraicIndependent_pair_of_omega_ne p hB hx hz hxz,
    algebraicIndependent_pair_of_omega_ne p hB hy hz hyz, halg⟩

/-- **Blueprint Lemma 4.6(b)** for a normalized triple `(B i, B j, z)`, in coordinates: `z` is a
model generator, and `d z = s d(B i) + t d(B j)` with `s, t ≠ 0`. -/
theorem IsNormalized.coord_modelD (hB : IsTranscendenceBasis l B) {i j : ι} (hij : i ≠ j) {z : L}
    (h : IsNormalized l (B i) (B j) z) :
    hgt l p B z = 0 ∧ (modelBasis hB.1).coord i (modelD l B z) ≠ 0 ∧
      (modelBasis hB.1).coord j (modelD l B z) ≠ 0 ∧
      ∀ k, k ≠ i → k ≠ j → (modelBasis hB.1).coord k (modelD l B z) = 0 := by
  have hi := hgt_apply p hB i
  have hj := hgt_apply p hB j
  have hne : omega l p B (B i) ≠ omega l p B (B j) :=
    omega_ne_of_coord p (omega_apply p hB i) (omega_apply p hB j) ((modelBasis hB.1).coord i)
      (Or.inl ⟨by rw [modelBasis_coord_self]; exact one_ne_zero,
        modelBasis_coord_of_ne hB.1 hij.symm⟩)
  obtain ⟨hz, hle, hzi, hzj⟩ := h.trichotomy_eq_of_omega_ne p hB (hi.trans hj.symm) hne
  rw [hi] at hz
  obtain ⟨-, hdz⟩ := (hgt_eq_zero_iff p hB h.transcendental₃).1 hz
  rw [omega_eq_span_of_hgt_eq_zero p hz, omega_apply p hB i, omega_apply p hB j,
    Submodule.span_singleton_le_iff_mem] at hle
  rw [omega_eq_span_of_hgt_eq_zero p hz, omega_apply p hB i] at hzi
  rw [omega_eq_span_of_hgt_eq_zero p hz, omega_apply p hB j] at hzj
  obtain ⟨s, t, hs, ht, hst⟩ := exists_smul_add_smul_of_mem_sup hdz hle hzi hzj
  refine ⟨hz, ?_, ?_, fun k hki hkj ↦ ?_⟩
  · simpa only [hst, map_add, map_smul, smul_eq_mul, modelBasis_coord_self,
      modelBasis_coord_of_ne hB.1 hij.symm, mul_one, mul_zero, add_zero] using hs
  · simpa only [hst, map_add, map_smul, smul_eq_mul, modelBasis_coord_self,
      modelBasis_coord_of_ne hB.1 hij, mul_one, mul_zero, zero_add] using ht
  · simp only [hst, map_add, map_smul, smul_eq_mul, modelBasis_coord_of_ne hB.1 hki.symm,
      modelBasis_coord_of_ne hB.1 hkj.symm, mul_zero, add_zero]

include p in
/-- The main step of the proof of **blueprint Lemma 5.1**, inside a model: let `B` be a
transcendence basis of `L / l`, let `a = B ia`, `b = B ib`, `c = B ic` be three distinct elements
of `B`, and let `(a, b, d)` and `(b, c, e)` be normalized. Let `G = Q_{g₀}` lie on `⟨D, C⟩` and
`⟨A, E⟩`, and `H = Q_{h₀}` on `⟨A, C⟩` and `⟨B, G⟩`. Then for model generators `g, h` of `G, H`
the triples `(d, c, g)`, `(a, e, g)`, `(a, c, h)`, `(b, h, g)` are normalized. -/
theorem quadrangle_of_isTranscendenceBasis (hB : IsTranscendenceBasis l B) {ia ib ic : ι}
    (hab : ia ≠ ib) (hac : ia ≠ ic) (hbc : ib ≠ ic) {d e g₀ h₀ : L}
    (habd : IsNormalized l (B ia) (B ib) d) (hbce : IsNormalized l (B ib) (B ic) e)
    (hg : Transcendental l g₀) (hgDC : IsAlgebraic l⟮d, B ic⟯ g₀)
    (hgAE : IsAlgebraic l⟮B ia, e⟯ g₀) (hh : Transcendental l h₀)
    (hhAC : IsAlgebraic l⟮B ia, B ic⟯ h₀) (hhBG : IsAlgebraic l⟮B ib, g₀⟯ h₀) :
    ∃ g h : L, SamePoint l g g₀ ∧ SamePoint l h h₀ ∧ IsNormalized l d (B ic) g ∧
      IsNormalized l (B ia) e g ∧ IsNormalized l (B ia) (B ic) h ∧ IsNormalized l (B ib) h g := by
  set bas := modelBasis hB.1
  -- the points `A, B, C`: coordinates of `da, db, dc`
  have hta := habd.transcendental₁
  have htb := habd.transcendental₂
  have htc := hbce.transcendental₂
  have hωa := omega_apply p hB ia
  have hωb := omega_apply p hB ib
  have hωc := omega_apply p hB ic
  have caa : bas.coord ia (modelD l B (B ia)) = 1 := modelBasis_coord_self hB.1 ia
  have cbb : bas.coord ib (modelD l B (B ib)) = 1 := modelBasis_coord_self hB.1 ib
  have ccc : bas.coord ic (modelD l B (B ic)) = 1 := modelBasis_coord_self hB.1 ic
  have cab : bas.coord ia (modelD l B (B ib)) = 0 := modelBasis_coord_of_ne hB.1 hab.symm
  have cac : bas.coord ia (modelD l B (B ic)) = 0 := modelBasis_coord_of_ne hB.1 hac.symm
  have cba : bas.coord ib (modelD l B (B ia)) = 0 := modelBasis_coord_of_ne hB.1 hab
  have cbc : bas.coord ib (modelD l B (B ic)) = 0 := modelBasis_coord_of_ne hB.1 hbc.symm
  have cca : bas.coord ic (modelD l B (B ia)) = 0 := modelBasis_coord_of_ne hB.1 hac
  have ccb : bas.coord ic (modelD l B (B ib)) = 0 := modelBasis_coord_of_ne hB.1 hbc
  -- the points `D, E`: `d, e` are model generators (Lemma 4.6(b))
  have htd := habd.transcendental₃
  have hte := hbce.transcendental₃
  obtain ⟨hd0, cad, cbd, hd'⟩ := habd.coord_modelD p hB hab
  have ccd := hd' ic hac.symm hbc.symm
  obtain ⟨he0, cbe, cce, he'⟩ := hbce.coord_modelD p hB hbc
  have cae := he' ia hab hac
  have hωd := omega_eq_span_of_hgt_eq_zero p hd0
  have hωe := omega_eq_span_of_hgt_eq_zero p he0
  -- model generators `g, h` of `G, H`
  obtain ⟨g, hgg, hg0⟩ : ∃ g, SamePoint l g g₀ ∧ hgt l p B g = 0 :=
    ⟨_, (samePoint_frobZ_left_iff p _).2 (samePoint_refl hg), hgt_frobZ_neg_hgt p hB hg⟩
  obtain ⟨h, hhh, hh0⟩ : ∃ h, SamePoint l h h₀ ∧ hgt l p B h = 0 :=
    ⟨_, (samePoint_frobZ_left_iff p _).2 (samePoint_refl hh), hgt_frobZ_neg_hgt p hB hh⟩
  have htg := hgg.transcendental_left
  have hth := hhh.transcendental_left
  have hdg := ((hgt_eq_zero_iff p hB htg).1 hg0).2
  have hdh := ((hgt_eq_zero_iff p hB hth).1 hh0).2
  have hωg := omega_eq_span_of_hgt_eq_zero p hg0
  have hωh := omega_eq_span_of_hgt_eq_zero p hh0
  have hωg₀ := (omega_eq_of_samePoint p hB hgg).symm.trans hωg
  have hωh₀ := (omega_eq_of_samePoint p hB hhh).symm.trans hωh
  -- the point `G`: propagation
  have hDC : omega l p B d ≠ omega l p B (B ic) :=
    omega_ne_of_coord p hωd hωc (bas.coord ic) (Or.inr ⟨ccd, by rw [ccc]; exact one_ne_zero⟩)
  have hAE : omega l p B (B ia) ≠ omega l p B e :=
    omega_ne_of_coord p hωa hωe (bas.coord ia) (Or.inl ⟨by rw [caa]; exact one_ne_zero, cae⟩)
  have hgDC' := omega_le_sup_of_isAlgebraic p hB hg htd htc hgDC hDC
  have hgAE' := omega_le_sup_of_isAlgebraic p hB hg hta hte hgAE hAE
  rw [hωg₀, hωd, hωc, Submodule.span_singleton_le_iff_mem] at hgDC'
  rw [hωg₀, hωa, hωe, Submodule.span_singleton_le_iff_mem] at hgAE'
  obtain ⟨cag, cbg, ccg⟩ := coord_ne_zero_of_mem_sup_of_mem_sup caa cba cca cac cbc ccc cad cbd
    ccd cae cbe cce hdg hgDC' hgAE'
  -- the point `H`: propagation
  have hAC : omega l p B (B ia) ≠ omega l p B (B ic) :=
    omega_ne_of_coord p hωa hωc (bas.coord ia) (Or.inl ⟨by rw [caa]; exact one_ne_zero, cac⟩)
  have hBG₀ : omega l p B (B ib) ≠ omega l p B g₀ :=
    omega_ne_of_coord p hωb hωg₀ (bas.coord ia) (Or.inr ⟨cab, cag⟩)
  have hhAC' := omega_le_sup_of_isAlgebraic p hB hh hta htc hhAC hAC
  have hhBG' := omega_le_sup_of_isAlgebraic p hB hh htb hg hhBG hBG₀
  rw [hωh₀, hωa, hωc, Submodule.span_singleton_le_iff_mem] at hhAC'
  rw [hωh₀, hωb, hωg₀, Submodule.span_singleton_le_iff_mem] at hhBG'
  obtain ⟨cah, cbh, cch⟩ := coord_of_mem_sup_of_mem_sup caa cba cca cab cbb ccb cac cbc ccc cag
    ccg hdh hhAC' hhBG'
  -- the four remaining triples: Lemma 4.6(d)
  refine ⟨g, h, hgg, hhh, ?_, ?_, ?_, ?_⟩
  · have hdg := omega_ne_of_coord p hωd hωg (bas.coord ic) (Or.inr ⟨ccd, ccg⟩)
    have hcg := omega_ne_of_coord p hωc hωg (bas.coord ia) (Or.inr ⟨cac, cag⟩)
    exact isNormalized_of_hgt_eq_zero p hB
      (isCollinearTriple_of_omega_ne p hB htd htc htg hDC hdg hcg
        (isAlgebraic_adjoin_pair_of_samePoint hgDC (samePoint_refl htd) (samePoint_refl htc) hgg))
      hd0 (hgt_apply p hB ic) hg0 hDC hdg hcg
  · have hag := omega_ne_of_coord p hωa hωg (bas.coord ib) (Or.inr ⟨cba, cbg⟩)
    have heg := omega_ne_of_coord p hωe hωg (bas.coord ia) (Or.inr ⟨cae, cag⟩)
    exact isNormalized_of_hgt_eq_zero p hB
      (isCollinearTriple_of_omega_ne p hB hta hte htg hAE hag heg
        (isAlgebraic_adjoin_pair_of_samePoint hgAE (samePoint_refl hta) (samePoint_refl hte) hgg))
      (hgt_apply p hB ia) he0 hg0 hAE hag heg
  · have hah := omega_ne_of_coord p hωa hωh (bas.coord ic) (Or.inr ⟨cca, cch⟩)
    have hch := omega_ne_of_coord p hωc hωh (bas.coord ia) (Or.inr ⟨cac, cah⟩)
    exact isNormalized_of_hgt_eq_zero p hB
      (isCollinearTriple_of_omega_ne p hB hta htc hth hAC hah hch
        (isAlgebraic_adjoin_pair_of_samePoint hhAC (samePoint_refl hta) (samePoint_refl htc) hhh))
      (hgt_apply p hB ia) (hgt_apply p hB ic) hh0 hAC hah hch
  · have hbg := omega_ne_of_coord p hωb hωg (bas.coord ia) (Or.inr ⟨cab, cag⟩)
    have hbh := omega_ne_of_coord p hωb hωh (bas.coord ib)
      (Or.inl ⟨by rw [cbb]; exact one_ne_zero, cbh⟩)
    have hgh := omega_ne_of_coord p hωg hωh (bas.coord ib) (Or.inl ⟨cbg, cbh⟩)
    exact isNormalized_of_hgt_eq_zero p hB
      (isCollinearTriple_of_omega_ne p hB htb htg hth hbg hbh hgh
        (isAlgebraic_adjoin_pair_of_samePoint hhBG (samePoint_refl htb) hgg hhh)).swap₂₃
      (hgt_apply p hB ib) hh0 hg0 hbh hbg hgh.symm

end Model

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
  have ha₀ : Transcendental l a₀ := hd.transcendental₁
  have hb₀ : Transcendental l b₀ := hd.transcendental₂
  have hc₀ : Transcendental l c₀ := he.transcendental₂
  have hd₀ : Transcendental l d₀ := hd.transcendental₃
  have he₀ : Transcendental l e₀ := he.transcendental₃
  -- a normalized triple `(a, b, d)` for `(A, B, D)` with `a = a₀` (Lemma 3.5(a))
  obtain ⟨b, d, hbb, hdd, habd⟩ :
      ∃ b d, SamePoint l b b₀ ∧ SamePoint l d d₀ ∧ IsNormalized l a₀ b d := by
    obtain ⟨j, k, h⟩ := exists_isNormalized p hd
    exact ⟨_, _, (samePoint_frobZ_left_iff p j).2 (samePoint_refl hb₀),
      (samePoint_frobZ_left_iff p k).2 (samePoint_refl hd₀), h⟩
  -- a normalized triple `(b, c, e)` for `(B, C, E)` (Lemma 3.5(a))
  obtain ⟨c, e, hcc, hee, hbce⟩ :
      ∃ c e, SamePoint l c c₀ ∧ SamePoint l e e₀ ∧ IsNormalized l b c e := by
    obtain ⟨j, k, h⟩ :=
      exists_isNormalized p (he.of_samePoint hbb (samePoint_refl hc₀) (samePoint_refl he₀))
    exact ⟨_, _, (samePoint_frobZ_left_iff p j).2 (samePoint_refl hc₀),
      (samePoint_frobZ_left_iff p k).2 (samePoint_refl he₀), h⟩
  -- `a, b, c` are algebraically independent; extend them to a transcendence basis `T`
  have habc' : AlgebraicIndependent l ![a₀, b, c] := by
    refine algebraicIndependent_of_isAlgebraic_adjoin habc (fun i ↦ ?_) (fun i ↦ ?_) <;>
      fin_cases i
    exacts [(samePoint_refl ha₀).isAlgebraic, hbb.symm.isAlgebraic, hcc.symm.isAlgebraic,
      (samePoint_refl ha₀).isAlgebraic, hbb.isAlgebraic, hcc.isAlgebraic]
  obtain ⟨T, hT, hB⟩ := exists_isTranscendenceBasis_superset habc'.to_subtype_range
  have hinj := habc'.injective
  obtain ⟨g, h, hgg, hhh, hdcg, haeg, hach, hbhg⟩ := quadrangle_of_isTranscendenceBasis p hB
    (ia := ⟨a₀, hT (Set.mem_range_self 0)⟩) (ib := ⟨b, hT (Set.mem_range_self 1)⟩)
    (ic := ⟨c, hT (Set.mem_range_self 2)⟩)
    (fun h ↦ hinj.ne (by decide : (0 : Fin 3) ≠ 1) (congrArg Subtype.val h))
    (fun h ↦ hinj.ne (by decide : (0 : Fin 3) ≠ 2) (congrArg Subtype.val h))
    (fun h ↦ hinj.ne (by decide : (1 : Fin 3) ≠ 2) (congrArg Subtype.val h)) habd hbce hg
    (isAlgebraic_adjoin_pair_of_samePoint hgDC hdd hcc (samePoint_refl hg))
    (isAlgebraic_adjoin_pair_of_samePoint hgAE (samePoint_refl ha₀) hee (samePoint_refl hg)) hh
    (isAlgebraic_adjoin_pair_of_samePoint hhAC (samePoint_refl ha₀) hcc (samePoint_refl hh))
    (isAlgebraic_adjoin_pair_of_samePoint hhBG hbb (samePoint_refl hg) (samePoint_refl hh))
  exact ⟨a₀, b, c, d, e, g, h, samePoint_refl ha₀, hbb, hcc, hdd, hee, hgg, hhh, habd, hbce, hdcg,
    haeg, hach, hbhg⟩

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
