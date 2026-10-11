/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.IdealLocalization
import Mathlib.FieldTheory.Galois.Infinite
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ResidueExactSequence

/-!
# Residue fields under localization at a normalization prime

This file compares the decomposition group and residue action attached to a
prime of a normalization with the corresponding objects for the localized
valuation subring.  The comparison is canonical and retains the base-prime
residue field.
-/

noncomputable section


universe uA uB uK uL

namespace TameAbhyankar.SGA1

open scoped Pointwise
open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

attribute [local instance] Ideal.Quotient.field

section DecompositionLocalization

variable {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL}
variable [CommRing A] [CommRing B] [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra B L] [IsFractionRing B L]
variable [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsIntegralClosure B A L]
variable [Algebra.IsAlgebraic K L]
variable [IsDedekindDomain B]

variable (P : Ideal B) [P.IsMaximal]
variable (hP : P ≠ ⊥)

omit [IsDedekindDomain B] in
/-- The normalization action fixes the base ring. -/
theorem normalizationGaloisSMulCommClass :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    SMulCommClass Gal(L/K) A B := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  constructor
  intro sigma a b
  apply (IsFractionRing.injective B L)
  simp only [Algebra.smul_def, map_mul,
    algebraMap_normalization_smul (A := A)]
  have ha : (sigma : Gal(L/K)) (algebraMap A L a) =
      algebraMap A L a := by
    calc
      (sigma : Gal(L/K)) (algebraMap A L a) =
          (sigma : Gal(L/K))
            (algebraMap K L (algebraMap A K a)) := by
        rw [← IsScalarTower.algebraMap_apply A K L]
      _ = algebraMap K L (algebraMap A K a) :=
        (sigma : Gal(L/K)).commutes (algebraMap A K a)
      _ = algebraMap A L a :=
        (IsScalarTower.algebraMap_apply A K L a).symm
  have haB : (sigma : Gal(L/K))
        (algebraMap B L (algebraMap A B a)) =
      algebraMap B L (algebraMap A B a) := by
    calc
      (sigma : Gal(L/K))
          (algebraMap B L (algebraMap A B a)) =
        (sigma : Gal(L/K)) (algebraMap A L a) := by
          rw [IsScalarTower.algebraMap_apply A B L]
      _ = algebraMap A L a := ha
      _ = algebraMap B L (algebraMap A B a) :=
        IsScalarTower.algebraMap_apply A B L a
  rw [haB]

/-- The canonical map from a normalization ring to the valuation ring
obtained by localizing at `P`. -/
def idealLocalizationRingHom :
    B →+* idealLocalizationValuationSubring B L P hP :=
  (idealLocalizationEquiv B L P hP).toRingHom.comp
    (algebraMap B (idealLocalizationSubalgebra B L P))

@[simp] theorem idealLocalizationRingHom_apply_coe (b : B) :
    ((idealLocalizationRingHom (B := B) (L := L) P hP b :
      idealLocalizationValuationSubring B L P hP) : L) =
      algebraMap B L b :=
  rfl

/-- Membership in `P` is detected by the maximal ideal after localization. -/
theorem idealLocalizationRingHom_mem_maximalIdeal_iff (b : B) :
    idealLocalizationRingHom (B := B) (L := L) P hP b ∈
        IsLocalRing.maximalIdeal
          (idealLocalizationValuationSubring B L P hP) ↔
      b ∈ P := by
  let S := idealLocalizationSubalgebra B L P
  let bS : S := algebraMap B S b
  have he := idealLocalizationEquiv_mem_maximalIdeal_iff B L P hP bS
  have hb := IsLocalization.AtPrime.to_map_mem_maximal_iff S P b
  exact he.trans hb

@[simp] theorem idealLocalizationResidueEquiv_mk (b : B) :
    idealLocalizationResidueEquiv B L P hP
        (Ideal.Quotient.mk P b) =
      IsLocalRing.residue
        (idealLocalizationValuationSubring B L P hP)
        (idealLocalizationRingHom (B := B) (L := L) P hP b) := by
  rfl

private theorem globalDecomposition_maps_localization :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    ∀ (sigma : HilbertRamification.Dedekind.decompositionGroup P Gal(L/K))
      {x : L},
      x ∈ idealLocalizationValuationSubring B L P hP →
      ((sigma : Gal(L/K)) : L ≃ₐ[K] L) x ∈
        idealLocalizationValuationSubring B L P hP := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  intro sigma x hx
  change x ∈ idealLocalizationSubalgebra B L P at hx
  change ((sigma : Gal(L/K)) : L ≃ₐ[K] L) x ∈
    idealLocalizationSubalgebra B L P
  rcases hx with ⟨a, s, hs, rfl⟩
  have hsigma : (sigma : Gal(L/K)) • s ∈ P.primeCompl := by
    intro hsigmaP
    have hsmul : (sigma : Gal(L/K))⁻¹ • ((sigma : Gal(L/K)) • s) ∈
        (sigma : Gal(L/K))⁻¹ • P :=
      Ideal.smul_mem_pointwise_smul
        (M := Gal(L/K)) (sigma : Gal(L/K))⁻¹
        ((sigma : Gal(L/K)) • s) P hsigmaP
    have hinvP : (sigma : Gal(L/K))⁻¹ • P = P := by
      calc
        (sigma : Gal(L/K))⁻¹ • P =
            (sigma : Gal(L/K))⁻¹ • ((sigma : Gal(L/K)) • P) :=
          congrArg ((sigma : Gal(L/K))⁻¹ • ·) sigma.property.symm
        _ = P := by simp
    have hsP : s ∈ P := by
      simpa [hinvP] using hsmul
    exact hs hsP
  refine ⟨(sigma : Gal(L/K)) • a, (sigma : Gal(L/K)) • s,
    hsigma, ?_⟩
  simp only [map_mul, map_inv₀,
    algebraMap_normalization_smul (A := A)]

private theorem globalDecomposition_maps_localization_iff :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    ∀ (sigma : HilbertRamification.Dedekind.decompositionGroup P Gal(L/K))
      (x : L),
      ((sigma : Gal(L/K)) : L ≃ₐ[K] L) x ∈
          idealLocalizationValuationSubring B L P hP ↔
        x ∈ idealLocalizationValuationSubring B L P hP := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  intro sigma x
  constructor
  · intro hx
    let sigmaInv : HilbertRamification.Dedekind.decompositionGroup P Gal(L/K) :=
      sigma⁻¹
    have hinv := globalDecomposition_maps_localization
      (A := A) (P := P) (hP := hP) sigmaInv hx
    simpa [sigmaInv] using hinv
  · exact globalDecomposition_maps_localization
      (A := A) (P := P) (hP := hP) sigma

/-- Stabilizing a normalization prime is equivalent to stabilizing its
localized valuation subring, in the forward direction. -/
def globalIdealDecompositionToLocalDecomposition :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    HilbertRamification.Dedekind.decompositionGroup P Gal(L/K) →*
      decompositionGroup K (idealLocalizationValuationSubring B L P hP) := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  refine
    { toFun := fun sigma ↦ ⟨(sigma : Gal(L/K)), ?_⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  apply _root_.ValuationSubring.toSubring_injective
  ext x
  change x ∈ (sigma : Gal(L/K)) •
      idealLocalizationValuationSubring B L P hP ↔
    x ∈ idealLocalizationValuationSubring B L P hP
  rw [_root_.ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact globalDecomposition_maps_localization_iff
    (A := A) (P := P) (hP := hP) sigma⁻¹ x

/-- A decomposition automorphism of the localized valuation ring stabilizes
the original normalization prime. -/
def localDecompositionToGlobalIdealDecomposition :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    decompositionGroup K (idealLocalizationValuationSubring B L P hP) →*
      HilbertRamification.Dedekind.decompositionGroup P Gal(L/K) := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  let V := idealLocalizationValuationSubring B L P hP
  refine
    { toFun := fun tau ↦ ⟨(tau : Gal(L/K)), ?_⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  apply Ideal.ext
  intro b
  rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem]
  have hmap :
      idealLocalizationRingHom (B := B) (L := L) P hP
          ((tau : Gal(L/K))⁻¹ • b) =
        (tau⁻¹ : decompositionGroup K V) •
          idealLocalizationRingHom (B := B) (L := L) P hP b := by
    apply Subtype.ext
    exact algebraMap_normalization_smul (A := A)
      ((tau : Gal(L/K))⁻¹) b
  rw [← idealLocalizationRingHom_mem_maximalIdeal_iff (B := B) (L := L) P hP,
    hmap, ← idealLocalizationRingHom_mem_maximalIdeal_iff (B := B) (L := L) P hP]
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal]
  exact not_congr
    (MulEquiv.isUnit_map
      (MulSemiringAction.toRingAut
        (decompositionGroup K V) V tau⁻¹))

/-- The ideal decomposition group is canonically the decomposition group of
the localized valuation subring. -/
def idealDecompositionLocalizationMulEquiv :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    HilbertRamification.Dedekind.decompositionGroup P Gal(L/K) ≃*
      decompositionGroup K (idealLocalizationValuationSubring B L P hP) := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  refine
    { toFun := globalIdealDecompositionToLocalDecomposition
        (A := A) (P := P) (hP := hP)
      invFun := localDecompositionToGlobalIdealDecomposition
        (A := A) (P := P) (hP := hP)
      left_inv := ?_
      right_inv := ?_
      map_mul' := fun _ _ ↦ rfl }
  · intro sigma
    apply Subtype.ext
    change (sigma : Gal(L/K)) = (sigma : Gal(L/K))
    rfl
  · intro tau
    apply Subtype.ext
    change (tau : Gal(L/K)) = (tau : Gal(L/K))
    rfl

/-- Reduction commutes with the canonical comparison from ideal
decomposition to valuation-subring decomposition. -/
theorem idealLocalizationResidueEquiv_residueAction
    [IsGalois K L] :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    letI := normalizationGaloisSMulCommClass
      (A := A) (B := B) (K := K) (L := L)
    ∀ (sigma : HilbertRamification.Dedekind.decompositionGroup P Gal(L/K))
      (x : B ⧸ P),
    let p := P.comap (algebraMap A B)
    letI : P.LiesOver p := ⟨rfl⟩
    idealLocalizationResidueEquiv B L P hP
        (HilbertRamification.Dedekind.residueStabilizerHom
          p P Gal(L/K) sigma x) =
      RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroupResidueAction
          K
          (idealLocalizationValuationSubring B L P hP)
          (globalIdealDecompositionToLocalDecomposition
            (A := A) (P := P) (hP := hP) sigma)
          (idealLocalizationResidueEquiv B L P hP x) := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  let := normalizationGaloisSMulCommClass
    (A := A) (B := B) (K := K) (L := L)
  intro sigma x
  let p := P.comap (algebraMap A B)
  let : P.LiesOver p := ⟨rfl⟩
  dsimp only
  refine Quotient.inductionOn x ?_
  intro b
  change
    idealLocalizationResidueEquiv B L P hP
        (HilbertRamification.Dedekind.residueStabilizerHom
          (P.comap (algebraMap A B)) P Gal(L/K) sigma
          (Ideal.Quotient.mk P b)) =
      RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroupResidueAction
          K (idealLocalizationValuationSubring B L P hP)
          (globalIdealDecompositionToLocalDecomposition
            (A := A) (P := P) (hP := hP) sigma)
          (idealLocalizationResidueEquiv B L P hP
            (Ideal.Quotient.mk P b))
  rw [HilbertRamification.Dedekind.residueStabilizerHom_apply,
    idealLocalizationResidueEquiv_mk,
    idealLocalizationResidueEquiv_mk,
    RamificationTheory.HilbertRamification.ValuationSubring.decompositionGroupResidueAction_residue]
  congr 1
  apply Subtype.ext
  exact algebraMap_normalization_smul (A := A) (sigma : Gal(L/K)) b

section BaseResidueField

variable [IsGalois K L]

/-- The prime of the base ring below a normalization prime. -/
abbrev normalizationIdealBasePrime : Ideal A :=
  P.comap (algebraMap A B)

include L
omit [IsFractionRing B L] [IsDedekindDomain B] in
theorem normalizationIdealBasePrime_isMaximal :
    (normalizationIdealBasePrime (A := A) P).IsMaximal := by
  let : Algebra.IsIntegral A B :=
    ⟨fun b ↦ IsIntegralClosure.isIntegral A L b⟩
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap A B)
    (fun x ↦ Algebra.IsIntegral.isIntegral x) P

omit [IsFractionRing A K] [IsIntegralClosure B A L]
  [Algebra.IsAlgebraic K L] [IsGalois K L] in
theorem localDecomposition_fixes_normalizationBase
    (sigma : decompositionGroup K
      (idealLocalizationValuationSubring B L P hP))
    (a : A) :
    sigma • idealLocalizationRingHom (B := B) (L := L) P hP
        (algebraMap A B a) =
      idealLocalizationRingHom (B := B) (L := L) P hP
        (algebraMap A B a) := by
  apply Subtype.ext
  change ((sigma : Gal(L/K)) : L ≃ₐ[K] L)
      (algebraMap B L (algebraMap A B a)) =
    algebraMap B L (algebraMap A B a)
  calc
    ((sigma : Gal(L/K)) : L ≃ₐ[K] L)
        (algebraMap B L (algebraMap A B a)) =
      ((sigma : Gal(L/K)) : L ≃ₐ[K] L) (algebraMap A L a) := by
        rw [IsScalarTower.algebraMap_apply A B L]
    _ = ((sigma : Gal(L/K)) : L ≃ₐ[K] L)
        (algebraMap K L (algebraMap A K a)) := by
          rw [← IsScalarTower.algebraMap_apply A K L]
    _ = algebraMap K L (algebraMap A K a) :=
      (sigma : Gal(L/K)).commutes (algebraMap A K a)
    _ = algebraMap A L a :=
      (IsScalarTower.algebraMap_apply A K L a).symm
    _ = algebraMap B L (algebraMap A B a) :=
      IsScalarTower.algebraMap_apply A B L a

/-- The base ring maps canonically to the fixed valuation subring defining
the intrinsic decomposition residue field. -/
def normalizationBaseToDecompositionFixedSubring :
    A →+* decompositionFixedSubring K
      (idealLocalizationValuationSubring B L P hP) := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  let V := idealLocalizationValuationSubring B L P hP
  exact RingHom.codRestrict
    ((idealLocalizationRingHom (B := B) (L := L) P hP).comp
      (algebraMap A B))
    (decompositionFixedSubring K V)
    (fun a sigma ↦ localDecomposition_fixes_normalizationBase
      (A := A) (B := B) (K := K) (L := L)
      (P := P) (hP := hP) sigma a)

/-- The canonical map from the base-prime residue field to the intrinsic
decomposition residue field. -/
def normalizationBaseResidueToDecompositionResidueField :
    A ⧸ normalizationIdealBasePrime (A := A) P →+*
      decompositionResidueField K
        (idealLocalizationValuationSubring B L P hP) := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  let V := idealLocalizationValuationSubring B L P hP
  let f := normalizationBaseToDecompositionFixedSubring
    (A := A) (B := B) (K := K) (L := L) (P := P) (hP := hP)
  apply Ideal.Quotient.lift (normalizationIdealBasePrime (A := A) P)
    ((Ideal.Quotient.mk (decompositionFixedMaximalIdeal K V)).comp f)
  intro a ha
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  change idealLocalizationRingHom (B := B) (L := L) P hP
      (algebraMap A B a) ∈ IsLocalRing.maximalIdeal V
  exact (idealLocalizationRingHom_mem_maximalIdeal_iff
    (B := B) (L := L) P hP (algebraMap A B a)).mpr ha

omit [IsFractionRing A K] [IsIntegralClosure B A L]
  [Algebra.IsAlgebraic K L] [IsGalois K L] in
@[simp] theorem normalizationBaseResidueToDecompositionResidueField_mk
    (a : A) :
    normalizationBaseResidueToDecompositionResidueField
        (A := A) (P := P) (hP := hP)
        (Ideal.Quotient.mk (normalizationIdealBasePrime (A := A) P) a) =
      Ideal.Quotient.mk
        (decompositionFixedMaximalIdeal K
          (idealLocalizationValuationSubring B L P hP))
        (normalizationBaseToDecompositionFixedSubring
          (A := A) (B := B) (K := K) (L := L)
          (P := P) (hP := hP) a) := by
  simp [normalizationBaseResidueToDecompositionResidueField]

omit [Algebra.IsAlgebraic K L] [IsGalois K L] in
@[simp] theorem decompositionResidueField_algebraMap_mk
    (r : decompositionFixedSubring K
      (idealLocalizationValuationSubring B L P hP)) :
    algebraMap
        (decompositionResidueField K
          (idealLocalizationValuationSubring B L P hP))
        (selectedResidueField
          (idealLocalizationValuationSubring B L P hP))
        (Ideal.Quotient.mk
          (decompositionFixedMaximalIdeal K
            (idealLocalizationValuationSubring B L P hP)) r) =
      IsLocalRing.residue
        (idealLocalizationValuationSubring B L P hP) r := by
  rfl

omit [IsFractionRing A K] [IsIntegralClosure B A L]
  [Algebra.IsAlgebraic K L] [IsGalois K L] in
/-- The canonical base-residue map agrees with the usual normalization
residue map after localization. -/
theorem normalizationBaseResidue_decompositionResidueField_commutes
    (x : A ⧸ normalizationIdealBasePrime (A := A) P) :
    letI : P.LiesOver (normalizationIdealBasePrime (A := A) P) := ⟨rfl⟩
    algebraMap
        (decompositionResidueField K
          (idealLocalizationValuationSubring B L P hP))
        (selectedResidueField
          (idealLocalizationValuationSubring B L P hP))
        (normalizationBaseResidueToDecompositionResidueField
          (A := A) (P := P) (hP := hP) x) =
      idealLocalizationResidueEquiv B L P hP
        (algebraMap
          (A ⧸ normalizationIdealBasePrime (A := A) P) (B ⧸ P) x) := by
  let : P.LiesOver (normalizationIdealBasePrime (A := A) P) := ⟨rfl⟩
  refine Quotient.inductionOn x ?_
  intro a
  change
    algebraMap
        (decompositionResidueField K
          (idealLocalizationValuationSubring B L P hP))
        (selectedResidueField
          (idealLocalizationValuationSubring B L P hP))
        (normalizationBaseResidueToDecompositionResidueField
          (A := A) (P := P) (hP := hP)
          (Ideal.Quotient.mk
            (normalizationIdealBasePrime (A := A) P) a)) =
      idealLocalizationResidueEquiv B L P hP
        (Ideal.Quotient.mk P (algebraMap A B a))
  rw [normalizationBaseResidueToDecompositionResidueField_mk,
    decompositionResidueField_algebraMap_mk,
    idealLocalizationResidueEquiv_mk]
  rfl

/-- In residue characteristic zero, the canonical base-residue map onto the
intrinsic decomposition residue field is surjective.  The proof uses the
normal residue extension and the naturality of the two residue actions. -/
theorem normalizationBaseResidueToDecompositionResidueField_surjective
    [FiniteDimensional K L]
    [IsIntegrallyClosed A]
    [CharZero (A ⧸ normalizationIdealBasePrime (A := A) P)] :
    Function.Surjective
      (normalizationBaseResidueToDecompositionResidueField
        (A := A) (B := B) (K := K) (L := L)
        (P := P) (hP := hP)) := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  let := normalizationGaloisSMulCommClass
    (A := A) (B := B) (K := K) (L := L)
  let p := normalizationIdealBasePrime (A := A) P
  let V := idealLocalizationValuationSubring B L P hP
  let F := decompositionResidueField K V
  let E := selectedResidueField V
  let E₀ := B ⧸ P
  let e : E₀ ≃+* E := idealLocalizationResidueEquiv B L P hP
  let : p.IsMaximal := normalizationIdealBasePrime_isMaximal
    (A := A) (B := B) (L := L) P
  let : P.LiesOver p := ⟨rfl⟩
  let : Finite Gal(L/K) := IsGaloisGroup.finite Gal(L/K) K L
  let : Algebra.IsInvariant A B Gal(L/K) :=
    Algebra.isInvariant_of_isGalois A K L B
  let : Normal (A ⧸ p) E₀ :=
    HilbertRamification.Dedekind.dedekindRamification_residueExtension_normal
      p P Gal(L/K)
  let : Algebra.IsSeparable (A ⧸ p) E₀ := inferInstance
  let : IsGalois (A ⧸ p) E₀ :=
    HilbertRamification.Dedekind.dedekindRamification_residueExtension_isGalois
      p P Gal(L/K)
  intro x
  let y₀ : E₀ := e.symm (algebraMap F E x)
  have hfixed : ∀ tau : Gal(E₀/(A ⧸ p)), tau y₀ = y₀ := by
    intro tau
    obtain ⟨sigma, hsigma⟩ :=
      HilbertRamification.Dedekind.dedekindRamification_residueAction_surjective
        p P Gal(L/K) tau
    have hlocal :
        decompositionGroupResidueAction K V
            (globalIdealDecompositionToLocalDecomposition
              (A := A) (P := P) (hP := hP) sigma)
            (algebraMap F E x) =
          algebraMap F E x :=
      (decompositionGroupResidueAction K V
        (globalIdealDecompositionToLocalDecomposition
          (A := A) (P := P) (hP := hP) sigma)).commutes x
    apply e.injective
    rw [← hsigma,
      idealLocalizationResidueEquiv_residueAction
        (A := A) (P := P) (hP := hP) sigma y₀]
    change decompositionGroupResidueAction K V
        (globalIdealDecompositionToLocalDecomposition
          (A := A) (P := P) (hP := hP) sigma)
        (e y₀) = e y₀
    rw [show e y₀ = algebraMap F E x from e.apply_symm_apply _, hlocal]
  obtain ⟨z, hz⟩ :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed y₀).mpr hfixed
  refine ⟨z, ?_⟩
  apply (algebraMap F E).injective
  rw [normalizationBaseResidue_decompositionResidueField_commutes
    (A := A) (P := P) (hP := hP) z, hz]
  exact e.apply_symm_apply (algebraMap F E x)

/-- In residue characteristic zero, the residue field of the base prime is
canonically the intrinsic decomposition residue field of the localized
normalization. -/
def normalizationBaseResidueEquivDecompositionResidueField
    [FiniteDimensional K L]
    [IsIntegrallyClosed A]
    [CharZero (A ⧸ normalizationIdealBasePrime (A := A) P)] :
    A ⧸ normalizationIdealBasePrime (A := A) P ≃+*
      decompositionResidueField K
        (idealLocalizationValuationSubring B L P hP) := by
  letI : (normalizationIdealBasePrime (A := A) P).IsMaximal :=
    normalizationIdealBasePrime_isMaximal (A := A) (B := B) (L := L) P
  apply RingEquiv.ofBijective
    (normalizationBaseResidueToDecompositionResidueField
      (A := A) (B := B) (K := K) (L := L)
      (P := P) (hP := hP))
  exact ⟨RingHom.injective _,
    normalizationBaseResidueToDecompositionResidueField_surjective
      (A := A) (B := B) (K := K) (L := L)
      (P := P) (hP := hP)⟩

end BaseResidueField

end DecompositionLocalization

end TameAbhyankar.SGA1

end
