module

public import MilnorAlgDep.Foundations.V
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure

/-!
# The prime field and its relative algebraic closure

Auxiliary material for Sections 7.3 and 7.4 of the blueprint (Theorems C and D), where `k₀` and
`l₀` are the algebraic closures of the prime fields in `K` and `L`.

## Main definitions

* `MilnorAlgDep.primeAlgClosure L : Subfield L`: the elements of `L` algebraic over the prime field
  `⊥ : Subfield L`.
* `MilnorAlgDep.botEquiv τ : (⊥ : Subfield K) ≃+* (⊥ : Subfield L)`: the isomorphism of prime fields
  induced by a field embedding `τ : K →+* L`.

## Main statements

* `isAlgebraic_bot_map_iff`, `algebraicIndependent_bot_map_iff`: a field embedding preserves and
  reflects algebraicity and algebraic independence over the prime field ("An element of `K` is
  algebraic over the prime field if and only if its image under `τ` is", blueprint 7.3).
* `isRelAlgClosed_of_forall_mem_iff`: the algebraic closure of the prime field is relatively
  algebraically closed.
* `exists_pow_eq_one_of_isAlgebraic_bot`: in positive characteristic, a non-zero element algebraic
  over the prime field is a root of unity (used for case (ii) of Lemma 7.3 and for `C_L = 0`).
* `ringChar_eq_of_ringHom`: fields related by an embedding have the same characteristic.
-/

@[expose] public section

namespace MilnorAlgDep

variable {K L : Type*} [Field K] [Field L]

/-- Fields related by a ring homomorphism have the same characteristic. -/
theorem ringChar_eq_of_ringHom (τ : K →+* L) : ringChar K = ringChar L :=
  (ringChar.eq L (ringChar K) (C := charP_of_injective_ringHom τ.injective _)).symm

section botEquiv

/-- The homomorphism of prime fields induced by a field embedding `τ : K →+* L`. -/
def botHom (τ : K →+* L) : (⊥ : Subfield K) →+* (⊥ : Subfield L) :=
  τ.restrict ⊥ ⊥ fun x hx ↦ by
    have : (⊥ : Subfield K) ≤ (⊥ : Subfield L).comap τ := bot_le
    exact this hx

theorem botHom_surjective (τ : K →+* L) : Function.Surjective (botHom τ) := by
  rintro ⟨y, hy⟩
  rw [← Subfield.map_bot τ] at hy
  obtain ⟨x, hx, rfl⟩ := Subfield.mem_map.1 hy
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The isomorphism of prime fields induced by a field embedding `τ : K →+* L`. -/
noncomputable def botEquiv (τ : K →+* L) : (⊥ : Subfield K) ≃+* (⊥ : Subfield L) :=
  RingEquiv.ofBijective (botHom τ) ⟨(botHom τ).injective, botHom_surjective τ⟩

theorem algebraMap_comp_botEquiv (τ : K →+* L) :
    (algebraMap (⊥ : Subfield L) L).comp (botEquiv τ : (⊥ : Subfield K) →+* (⊥ : Subfield L)) =
      τ.comp (algebraMap (⊥ : Subfield K) K) :=
  rfl

/-- A field embedding preserves and reflects algebraicity over the prime field. -/
theorem isAlgebraic_bot_map_iff (τ : K →+* L) {x : K} :
    IsAlgebraic (⊥ : Subfield L) (τ x) ↔ IsAlgebraic (⊥ : Subfield K) x :=
  isAlgebraic_ringHom_iff_of_comp_eq (botEquiv τ) τ τ.injective (algebraMap_comp_botEquiv τ)

/-- A field embedding preserves and reflects transcendence over the prime field. -/
theorem transcendental_bot_map_iff (τ : K →+* L) {x : K} :
    Transcendental (⊥ : Subfield L) (τ x) ↔ Transcendental (⊥ : Subfield K) x :=
  not_congr (isAlgebraic_bot_map_iff τ)

/-- A field embedding preserves and reflects algebraic independence over the prime field. -/
theorem algebraicIndependent_bot_map_iff (τ : K →+* L) {ι : Type*} {x : ι → K} :
    AlgebraicIndependent (⊥ : Subfield L) (τ ∘ x) ↔ AlgebraicIndependent (⊥ : Subfield K) x :=
  algebraicIndependent_ringHom_iff_of_comp_eq (botEquiv τ) τ τ.injective
    (algebraMap_comp_botEquiv τ)

end botEquiv

section primeAlgClosure

variable (L) in
/-- The algebraic closure `l₀` of the prime field in `L`: the elements algebraic over the prime
field `⊥ : Subfield L`. -/
def primeAlgClosure : Subfield L :=
  (algebraicClosure (⊥ : Subfield L) L).toSubfield

theorem mem_primeAlgClosure {x : L} :
    x ∈ primeAlgClosure L ↔ IsAlgebraic (⊥ : Subfield L) x :=
  mem_algebraicClosure_iff

variable (l₀ : Subfield L) in
/-- The inclusion of the prime field into a subfield `l₀`, as an algebra (auxiliary; not an
instance). -/
noncomputable abbrev algebraBot : Algebra (⊥ : Subfield L) l₀ :=
  (Subfield.inclusion (bot_le : (⊥ : Subfield L) ≤ l₀)).toAlgebra

variable (l₀ : Subfield L) in
theorem isScalarTower_bot :
    letI := algebraBot l₀
    IsScalarTower (⊥ : Subfield L) l₀ L :=
  letI := algebraBot l₀
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

variable {l₀ : Subfield L} (hl₀ : ∀ x : L, x ∈ l₀ ↔ IsAlgebraic (⊥ : Subfield L) x)
include hl₀

theorem isAlgebraic_bot_of_forall_mem_iff :
    letI := algebraBot l₀
    Algebra.IsAlgebraic (⊥ : Subfield L) l₀ := by
  let := algebraBot l₀
  have := isScalarTower_bot l₀
  exact ⟨fun z ↦ (isAlgebraic_algebraMap_iff (algebraMap l₀ L).injective).1 ((hl₀ z).1 z.2)⟩

/-- An element algebraic over `l₀` is algebraic over the prime field. -/
theorem isAlgebraic_bot_of_isAlgebraic {x : L} (hx : IsAlgebraic l₀ x) :
    IsAlgebraic (⊥ : Subfield L) x := by
  let := algebraBot l₀
  have := isScalarTower_bot l₀
  have := isAlgebraic_bot_of_forall_mem_iff hl₀
  exact hx.restrictScalars_of_isIntegral _

/-- `l₀` is relatively algebraically closed in `L`. -/
theorem isRelAlgClosed_of_forall_mem_iff : ∀ x : L, IsAlgebraic l₀ x → x ∈ l₀ :=
  fun x hx ↦ (hl₀ x).2 (isAlgebraic_bot_of_isAlgebraic hl₀ hx)

/-- Algebraic independence over the prime field is algebraic independence over `l₀`. -/
theorem algebraicIndependent_bot_iff {ι : Type*} {y : ι → L} :
    AlgebraicIndependent (⊥ : Subfield L) y ↔ AlgebraicIndependent l₀ y := by
  let := algebraBot l₀
  have := isScalarTower_bot l₀
  have := isAlgebraic_bot_of_forall_mem_iff hl₀
  have : FaithfulSMul (⊥ : Subfield L) l₀ :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.injective _)
  exact Algebra.IsAlgebraic.algebraicIndependent_iff _ _

/-- Transcendence over the prime field is transcendence over `l₀`. -/
theorem transcendental_bot_iff {y : L} :
    Transcendental (⊥ : Subfield L) y ↔ Transcendental l₀ y := by
  let := algebraBot l₀
  have := isScalarTower_bot l₀
  exact ⟨fun h h' ↦ h (isAlgebraic_bot_of_isAlgebraic hl₀ h'),
    fun h h' ↦ h (h'.extendScalars (algebraMap (⊥ : Subfield L) l₀).injective)⟩

end primeAlgClosure

theorem isRelAlgClosed_primeAlgClosure :
    ∀ x : L, IsAlgebraic (primeAlgClosure L) x → x ∈ primeAlgClosure L :=
  isRelAlgClosed_of_forall_mem_iff fun _ ↦ mem_primeAlgClosure

section rootsOfUnity

theorem isAlgebraic_bot_of_pow_eq_one {x : K} {n : ℕ} (hn : 0 < n) (h : x ^ n = 1) :
    IsAlgebraic (⊥ : Subfield K) x :=
  IsAlgebraic.of_pow hn (h ▸ isAlgebraic_one)

/-- In characteristic `p > 0` the prime field is finite. -/
theorem finite_bot_of_ringChar_ne_zero (hK : ringChar K ≠ 0) : Finite (⊥ : Subfield K) := by
  have : Fact (ringChar K).Prime :=
    ⟨(CharP.char_is_prime_or_zero K (ringChar K)).resolve_right hK⟩
  have hle : (⊥ : Subfield K) ≤ (ZMod.castHom (dvd_refl (ringChar K)) K).fieldRange := bot_le
  have hfin : (Set.range (ZMod.castHom (dvd_refl (ringChar K)) K)).Finite := Set.finite_range _
  exact (hfin.subset fun x hx ↦ (RingHom.mem_fieldRange).1 (hle hx)).to_subtype

/-- In characteristic `p > 0`, a non-zero element algebraic over the prime field is a root of
unity. -/
theorem exists_pow_eq_one_of_isAlgebraic_bot (hK : ringChar K ≠ 0) {y : K} (hy0 : y ≠ 0)
    (hy : IsAlgebraic (⊥ : Subfield K) y) : ∃ n : ℕ, 0 < n ∧ y ^ n = 1 := by
  have := finite_bot_of_ringChar_ne_zero hK
  let E := IntermediateField.adjoin (⊥ : Subfield K) {y}
  have : FiniteDimensional (⊥ : Subfield K) E :=
    IntermediateField.adjoin.finiteDimensional hy.isIntegral
  have : Finite E := Module.finite_of_finite (⊥ : Subfield K)
  have hyE : (⟨y, IntermediateField.mem_adjoin_simple_self _ y⟩ : E) ≠ 0 :=
    fun h ↦ hy0 (congrArg Subtype.val h)
  obtain ⟨n, hn, h⟩ := (isOfFinOrder_of_finite (Units.mk0 _ hyE)).exists_pow_eq_one
  refine ⟨n, hn, ?_⟩
  have := congrArg (fun u : Eˣ ↦ ((u : E) : K)) h
  simpa using this

end rootsOfUnity

end MilnorAlgDep
