module

public import MilnorAlgDep.Foundations.Points
public import Mathlib.FieldTheory.IsPerfectClosure

/-!
# `V_{L|l}` does not change under perfect closure

Blueprint, Section 1.1 ("The group does not change if `L` and `l` are replaced by their perfect
closures `L^i` and `l^i`") and Section 6.1 ("Also `V_{L|l} = V_{L^i|l^i}`").

Let `M / L` be a field extension of exponential characteristic `p` and `l` a subfield of `L`.
We define `perfectClosureIn l M p`, the subfield of `M` of elements some `p ^ n`-th power of which
lies in (the image of) `l`. When `M` is a perfect closure of `L` (Mathlib's
`IsPerfectClosure (algebraMap L M) p`), this is the blueprint's `l^i`, and the natural map
`V.toPerfectClosure : V l L → V l^i M`, `[a] ↦ [a]`, is a bijection.

## Main definitions

* `MilnorAlgDep.perfectClosureIn l M p : Subfield M`: the blueprint's `l^i`.
* `MilnorAlgDep.V.toPerfectClosure l M p : V l L →ₗ[ℚ] V (perfectClosureIn l M p) M`: the
  comparison map.

## Main statements

* `V.toPerfectClosure_bijective`: the comparison map is bijective when `M` is a perfect closure
  of `L`.
* `perfectClosureIn_isRelAlgClosed`: `l^i` is relatively algebraically closed in `M` if `l` is
  relatively algebraically closed in `L`.
* `V.vAlgIndep_toPerfectClosure_iff`: the comparison map preserves and reflects algebraic
  independence.

## Implementation notes

`algebraPerfectClosureIn` is the inclusion `l.map (algebraMap L M) ≤ l^i` as an algebra structure;
it is only a *local* instance (in this file), together with the global instances
`IsScalarTower (l.map _) l^i M` and `Algebra.IsAlgebraic (l.map _) l^i` stated in terms of it.
`toMapSubfield : l →+* l.map (algebraMap L M)` is the canonical isomorphism.
-/

@[expose] public section

namespace MilnorAlgDep

open VOf

variable {L : Type*} [Field L]

section perfectClosureIn

variable (l : Subfield L) (M : Type*) [Field M] [Algebra L M] (p : ℕ) [ExpChar M p]

omit [ExpChar M p] in
/-- Auxiliary: if `y ^ p ^ n` lies in a subfield `S`, so does `y ^ p ^ m` for `m ≥ n`. -/
private theorem pow_expChar_pow_mem_of_le {S : Subfield M} {y : M} {n m : ℕ}
    (h : y ^ p ^ n ∈ S) (hnm : n ≤ m) : y ^ p ^ m ∈ S := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [pow_add, pow_mul]
  exact S.pow_mem h _

/-- For a field extension `M / L` of exponential characteristic `p` and a subfield `l` of `L`,
the subfield of `M` consisting of the elements `y` such that `y ^ p ^ n` lies in (the image of)
`l` for some `n`. When `M` is a perfect closure of `L`, this is the blueprint's `l^i`, the perfect
closure of `l` inside `M`. -/
def perfectClosureIn : Subfield M where
  carrier := {y | ∃ n : ℕ, y ^ p ^ n ∈ l.map (algebraMap L M)}
  mul_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    refine ⟨n + m, ?_⟩
    rw [mul_pow]
    exact Subfield.mul_mem _ (pow_expChar_pow_mem_of_le M p hx le_self_add)
      (pow_expChar_pow_mem_of_le M p hy le_add_self)
  one_mem' := ⟨0, by rw [one_pow]; exact Subfield.one_mem _⟩
  add_mem' := by
    rintro x y ⟨n, hx⟩ ⟨m, hy⟩
    refine ⟨n + m, ?_⟩
    rw [add_pow_expChar_pow]
    exact Subfield.add_mem _ (pow_expChar_pow_mem_of_le M p hx le_self_add)
      (pow_expChar_pow_mem_of_le M p hy le_add_self)
  zero_mem' := ⟨0, by rw [zero_pow (by positivity)]; exact Subfield.zero_mem _⟩
  neg_mem' := by
    rintro x ⟨n, hx⟩
    refine ⟨n, ?_⟩
    rw [neg_pow]
    exact Subfield.mul_mem _ (Subfield.pow_mem _ (Subfield.neg_mem _ (Subfield.one_mem _)) _) hx
  inv_mem' := by
    rintro x ⟨n, hx⟩
    exact ⟨n, by rw [inv_pow]; exact Subfield.inv_mem _ hx⟩

variable {l M p} in
theorem mem_perfectClosureIn {y : M} :
    y ∈ perfectClosureIn l M p ↔ ∃ n : ℕ, y ^ p ^ n ∈ l.map (algebraMap L M) :=
  Iff.rfl

theorem algebraMap_mem_perfectClosureIn {x : L} (hx : x ∈ l) :
    algebraMap L M x ∈ perfectClosureIn l M p :=
  ⟨0, by rw [pow_zero, pow_one]; exact Subfield.mem_map.2 ⟨x, hx, rfl⟩⟩

theorem constUnits_le_comap_perfectClosureIn :
    constUnits l L ≤
      (constUnits (perfectClosureIn l M p) M).comap (Units.map (algebraMap L M : L →* M)) := by
  intro a ha
  rw [Subgroup.mem_comap, mem_constUnits_subfield]
  exact algebraMap_mem_perfectClosureIn l M p (mem_constUnits_subfield.1 ha)

theorem map_le_perfectClosureIn : l.map (algebraMap L M) ≤ perfectClosureIn l M p :=
  fun _ hy ↦ ⟨0, by rwa [pow_zero, pow_one]⟩

/-- Every element of `l^i` is algebraic over (the image of) `l`. -/
theorem isAlgebraic_map_of_mem_perfectClosureIn {y : M} (hy : y ∈ perfectClosureIn l M p) :
    IsAlgebraic (l.map (algebraMap L M)) y := by
  obtain ⟨n, hn⟩ := hy
  exact IsAlgebraic.of_pow (expChar_pow_pos M p n)
    (isAlgebraic_algebraMap (⟨_, hn⟩ : l.map (algebraMap L M)))

/-- The isomorphism `l → l.map (algebraMap L M)`, as a ring homomorphism. -/
noncomputable def toMapSubfield : l →+* l.map (algebraMap L M) :=
  (algebraMap L M).restrict l _ fun x hx ↦ Subfield.mem_map.2 ⟨x, hx, rfl⟩

omit [ExpChar M p] in
theorem toMapSubfield_injective : Function.Injective (toMapSubfield l M) :=
  (toMapSubfield l M).injective

omit [ExpChar M p] in
theorem toMapSubfield_surjective : Function.Surjective (toMapSubfield l M) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Subfield.mem_map.1 hy
  exact ⟨⟨x, hx⟩, rfl⟩

omit [ExpChar M p] in
theorem algebraMap_comp_toMapSubfield :
    (algebraMap (l.map (algebraMap L M)) M).comp (toMapSubfield l M) =
      (algebraMap L M).comp (algebraMap l L) :=
  rfl

/-- The inclusion `l.map (algebraMap L M) ≤ l^i` as an algebra structure (auxiliary). -/
noncomputable abbrev algebraPerfectClosureIn :
    Algebra (l.map (algebraMap L M)) (perfectClosureIn l M p) :=
  (Subfield.inclusion (map_le_perfectClosureIn l M p)).toAlgebra

attribute [local instance] algebraPerfectClosureIn

instance : IsScalarTower (l.map (algebraMap L M)) (perfectClosureIn l M p) M :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

instance : Algebra.IsAlgebraic (l.map (algebraMap L M)) (perfectClosureIn l M p) :=
  ⟨fun z ↦ (isAlgebraic_algebraMap_iff (algebraMap (perfectClosureIn l M p) M).injective).1
    (isAlgebraic_map_of_mem_perfectClosureIn l M p z.2)⟩

/-- Blueprint 6.1: `l^i` is relatively algebraically closed in `L^i` if `l` is relatively
algebraically closed in `L`. -/
theorem perfectClosureIn_isRelAlgClosed [PerfectRing M p] [IsPerfectClosure (algebraMap L M) p]
    (hl : ∀ x : L, IsAlgebraic l x → x ∈ l) :
    ∀ y : M, IsAlgebraic (perfectClosureIn l M p) y → y ∈ perfectClosureIn l M p := by
  intro y hy
  have hy' : IsAlgebraic (l.map (algebraMap L M)) y := hy.restrictScalars _
  obtain ⟨n, x, hx⟩ := IsPRadical.pow_mem (algebraMap L M) p y
  have hxalg : IsAlgebraic l x := by
    refine IsAlgebraic.of_ringHom_of_comp_eq (toMapSubfield l M) (algebraMap L M) ?_
      (toMapSubfield_surjective l M) (algebraMap L M).injective
      (algebraMap_comp_toMapSubfield l M)
    rw [hx]
    exact hy'.pow _
  exact ⟨n, hx ▸ Subfield.mem_map.2 ⟨x, hl x hxalg, rfl⟩⟩

end perfectClosureIn

namespace V

variable (l : Subfield L) (M : Type*) [Field M] [Algebra L M] (p : ℕ) [ExpChar M p]

attribute [local instance] algebraPerfectClosureIn

/-- Blueprint 1.1 / 6.1: the comparison map `V_{L|l} → V_{L^i|l^i}`, `[a] ↦ [a]`, where
`l^i = perfectClosureIn l M p`. It is bijective when `M` is a perfect closure of `L`
(`V.toPerfectClosure_bijective`). -/
noncomputable def toPerfectClosure : V l L →ₗ[ℚ] V (perfectClosureIn l M p) M :=
  VOf.mapRingHom (algebraMap L M) (constUnits_le_comap_perfectClosureIn l M p)

@[simp]
theorem toPerfectClosure_cls (a : Lˣ) :
    toPerfectClosure l M p (cls (constUnits l L) (.ofMul a)) =
      cls (constUnits (perfectClosureIn l M p) M)
        (.ofMul (Units.map (algebraMap L M : L →* M) a)) :=
  mapRingHom_cls _ _ a

/-- Blueprint 1.1 / 6.1: `V_{L|l} = V_{L^i|l^i}`: if `M` is a perfect closure of `L`, the
comparison map `V l L → V l^i M` is bijective. -/
theorem toPerfectClosure_bijective [PerfectRing M p] [IsPerfectClosure (algebraMap L M) p] :
    Function.Bijective (toPerfectClosure l M p) := by
  constructor
  · refine (injective_iff_map_eq_zero _).2 fun v hv ↦ ?_
    obtain ⟨n, a, hn, ha⟩ := exists_nsmul_eq_cls v
    have h0 : toPerfectClosure l M p (n • v) = 0 := by rw [map_nsmul, hv, smul_zero]
    rw [ha, toPerfectClosure_cls, VOf.cls_eq_zero_iff] at h0
    obtain ⟨k, hk, hmem⟩ := h0
    rw [mem_constUnits_subfield, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_ofClass,
      ← map_pow] at hmem
    obtain ⟨m, hm⟩ := hmem
    rw [← map_pow] at hm
    obtain ⟨c, hc, hca⟩ := Subfield.mem_map.1 hm
    have hc' : c = (a : L) ^ (k * p ^ m) := by rw [pow_mul]; exact (algebraMap L M).injective hca
    have hcls : cls (constUnits l L) (.ofMul a) = 0 := by
      refine (VOf.cls_eq_zero_iff a).2 ⟨k * p ^ m, Nat.mul_pos hk (expChar_pow_pos M p m), ?_⟩
      rw [mem_constUnits_subfield, Units.val_pow_eq_pow_val, ← hc']
      exact hc
    rw [hcls, ← smul_zero n] at ha
    exact nsmul_left_cancel hn.ne' ha
  · intro w
    obtain ⟨n, b, hn, hb⟩ := exists_nsmul_eq_cls w
    obtain ⟨m, x, hx⟩ := IsPRadical.pow_mem (algebraMap L M) p (b : M)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hx
      exact pow_ne_zero _ b.ne_zero hx.symm
    have hu : Units.map (algebraMap L M : L →* M) (Units.mk0 x hx0) = b ^ (p ^ m) :=
      Units.ext (by simp [hx])
    have hne : ((p ^ m * n : ℕ) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.mul_ne_zero (pow_ne_zero _ (expChar_ne_zero M p)) hn.ne')
    refine ⟨((p ^ m * n : ℕ) : ℚ)⁻¹ • cls (constUnits l L) (.ofMul (Units.mk0 x hx0)), ?_⟩
    rw [map_smul, toPerfectClosure_cls, hu, cls_pow, ← hb, smul_smul,
      ← Nat.cast_smul_eq_nsmul ℚ, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- The comparison map preserves and reflects algebraic independence. -/
theorem vAlgIndep_toPerfectClosure_iff {ι : Type*} (v : ι → V l L) :
    VAlgIndep (perfectClosureIn l M p) (fun i ↦ toPerfectClosure l M p (v i)) ↔
      VAlgIndep l v := by
  have hN i := repNat_pos (v i)
  have hrep' i : repNat (v i) • toPerfectClosure l M p (v i) =
      cls (constUnits (perfectClosureIn l M p) M)
        (.ofMul (Units.map (algebraMap L M : L →* M) (repUnit (v i)))) := by
    rw [← map_nsmul, repNat_nsmul, toPerfectClosure_cls]
  rw [VAlgIndep.iff_of_nsmul_eq_cls hN hrep',
    VAlgIndep.iff_of_nsmul_eq_cls hN fun i ↦ repNat_nsmul (v i)]
  have hx : (fun i ↦ ((Units.map (algebraMap L M : L →* M) (repUnit (v i)) : Mˣ) : M)) =
      algebraMap L M ∘ fun i ↦ ((repUnit (v i) : Lˣ) : L) := by
    ext i
    simp
  rw [hx, ← Algebra.IsAlgebraic.algebraicIndependent_iff (l.map (algebraMap L M))]
  exact ⟨fun H ↦ H.of_ringHom_of_comp_eq (toMapSubfield l M) (algebraMap L M)
      (toMapSubfield_injective l M) (algebraMap_comp_toMapSubfield l M),
    fun H ↦ H.ringHom_of_comp_eq (toMapSubfield l M) (algebraMap L M)
      (toMapSubfield_surjective l M) (algebraMap L M).injective
      (algebraMap_comp_toMapSubfield l M)⟩

end V

section Frobenius

/-- The Frobenius twist on classes: `[Frob^j y] = p ^ j • [y]`, where `p` is the characteristic
exponent of the perfect field `L`. -/
theorem cls_frobeniusEquiv_zpow [PerfectField L] (H : Subgroup Lˣ) (j : ℤ) (y : Lˣ) :
    cls H (.ofMul (Units.map
        (((frobeniusEquiv L (ringExpChar L) ^ j : L ≃+* L) : L →+* L) : L →* L) y)) =
      ((ringExpChar L : ℚ) ^ j) • cls H (.ofMul y) := by
  set p := ringExpChar L
  set σ := frobeniusEquiv L p
  have hnat : ∀ (n : ℕ) (z : Lˣ),
      Units.map (((σ ^ n : L ≃+* L) : L →+* L) : L →* L) z = z ^ p ^ n := by
    intro n z
    ext
    rw [Units.coe_map, Units.val_pow_eq_pow_val, ← iterateFrobeniusEquiv_eq_pow]
    rfl
  have hp : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (expChar_ne_zero L p)
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg j
  · rw [zpow_natCast, hnat, cls_pow, zpow_natCast, ← Nat.cast_smul_eq_nsmul ℚ, Nat.cast_pow]
  · set z := Units.map (((σ ^ (-(n : ℤ)) : L ≃+* L) : L →+* L) : L →* L) y
    have hz : Units.map (((σ ^ n : L ≃+* L) : L →+* L) : L →* L) z = y := by
      ext
      simp [z, zpow_neg]
    conv_rhs => rw [← hz, hnat, cls_pow]
    rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, zpow_neg, zpow_natCast, Nat.cast_pow,
      inv_mul_cancel₀ (pow_ne_zero _ hp), one_smul]

end Frobenius

end MilnorAlgDep
