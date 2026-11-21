/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicCompletionComparison
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicFinitePlace
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormalization

/-!
# Frobenius normalization away from the rational cyclotomic level
-/

@[expose] public section

open scoped NNReal NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp
open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension

attribute [local instance]
  rationalFinitePlaceCompletionRatAlgebra
  rationalCyclotomicPrimeFact
  rationalCyclotomicLevelNeZero
  KummerTheory.rationalCyclotomicLevelFiniteDimensional
  KummerTheory.rationalCyclotomicLevelIsAbelianGalois
  rationalFinitePlaceBaseNontriviallyNormedField
  rationalFinitePlaceBaseLocallyCompactSpace
  rationalFinitePlaceBaseIsUltrametricDist
  rationalFinitePlaceBaseValuativeRel
  rationalFinitePlaceBaseValuationIsNontrivial
  rationalFinitePlaceBaseValuationCompatible
  rationalFinitePlaceBaseValuativeRelIsNontrivial
  rationalFinitePlaceBaseIsValuativeTopology
  rationalFinitePlaceBaseIsNonarchimedeanLocalField
  rationalCyclotomicArtinExtensionAlgebra
  rationalCyclotomicArtinExtensionSMul
  rationalCyclotomicArtinCompletionAlgebra
  rationalCyclotomicArtinLocalizedAlgebra
  rationalCyclotomicArtinLocalizedGlobalAlgebra
  rationalCyclotomicArtinLocalizedGlobalSMul
  rationalCyclotomicArtinLocalizedScalarTower
  rationalCyclotomicArtinLocalizedFiniteDimensional
  rationalCyclotomicArtinLocalizedIsAbelianGalois
  rationalCyclotomicArtinLocalizedIsSeparable
  rationalCyclotomicArtinLocalizedIsCyclotomic
  rationalCyclotomicArtinExtensionFiniteDimensional
  rationalCyclotomicArtinExtensionContinuousSMul
  rationalCyclotomicArtinExtensionLocallyCompact
  rationalCyclotomicArtinLocalizedLocallyCompact
  rationalCyclotomicArtinLocalizedIsUltrametricDist
  rationalCyclotomicArtinLocalizedValued
  rationalCyclotomicArtinLocalizedValuativeRel
  rationalCyclotomicArtinLocalizedValuationCompatible
  rationalCyclotomicArtinLocalizedValuationHasExtension
  rationalCyclotomicArtinLocalizedValuationIsNontrivial
  rationalCyclotomicArtinLocalizedValuativeRelIsNontrivial
  rationalCyclotomicArtinLocalizedIsValuativeTopology
  rationalCyclotomicArtinLocalizedIsNonarchimedeanLocalField
  rationalCyclotomicArtinLocalizedIntegerAlgebra
  rationalCyclotomicArtinLocalizedIsIntegralClosure
  rationalCyclotomicArtinLocalizedIntegerModuleFinite

/-- The localized cyclotomic extension is unramified away from its level. -/
theorem rationalCyclotomicArtinUnramified
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      (rationalCyclotomicArtinBaseAbv q).Completion
      (rationalCyclotomicArtinLocalizedField m q) := by
  exact rationalCyclotomicLevel_chosenFinitePlaceIsUnramified m q hq

/-- Arithmetic Frobenius for a chosen proof of unramifiedness. -/
noncomputable def rationalCyclotomicArtinLocalFrobeniusOf
    (m : ℕ+) (q : Nat.Primes)
    (hUnramified :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        (rationalCyclotomicArtinBaseAbv q).Completion
        (rationalCyclotomicArtinLocalizedField m q)) :
    rationalCyclotomicArtinLocalizedField m q ≃ₐ[
      (rationalCyclotomicArtinBaseAbv q).Completion]
      rationalCyclotomicArtinLocalizedField m q := by
  letI := hUnramified
  let : IsIntegralClosure 𝒪[rationalCyclotomicArtinLocalizedField m q]
      𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      (rationalCyclotomicArtinLocalizedField m q) :=
    rationalCyclotomicArtinLocalizedIsIntegralClosure m q
  let : Module.Finite 𝒪[(rationalCyclotomicArtinBaseAbv q).Completion]
      𝒪[rationalCyclotomicArtinLocalizedField m q] :=
    rationalCyclotomicArtinLocalizedIntegerModuleFinite m q
  exact arithmeticFrobeniusOfUnramifiedValuation
    (rationalCyclotomicArtinBaseAbv q).Completion
    (rationalCyclotomicArtinLocalizedField m q)

/-- Arithmetic Frobenius in the chosen unramified cyclotomic localization. -/
noncomputable def rationalCyclotomicArtinLocalFrobenius
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    rationalCyclotomicArtinLocalizedField m q ≃ₐ[
      (rationalCyclotomicArtinBaseAbv q).Completion]
      rationalCyclotomicArtinLocalizedField m q :=
  rationalCyclotomicArtinLocalFrobeniusOf m q
    (rationalCyclotomicArtinUnramified m q hq)

/-- The decomposition-group equivalence for the chosen cyclotomic localization. -/
noncomputable def rationalCyclotomicArtinDecompositionEquiv
    (m : ℕ+) (q : Nat.Primes) :
    absoluteValueDecompositionGroup ℚ
        (rationalCyclotomicArtinExtension m q).1 ≃*
      (rationalCyclotomicArtinLocalizedField m q ≃ₐ[
        (rationalCyclotomicArtinBaseAbv q).Completion]
        rationalCyclotomicArtinLocalizedField m q) :=
  decompositionGroupEquivAlgebraicLocalizationAut
    (rationalCyclotomicArtinBaseAbv q)
    (RayClass.adicAbv_isNontrivial
      (rationalCyclotomicArtinPlace q))
    (rationalCyclotomicArtinExtension m q)

/-- The local-to-global homomorphism for the chosen cyclotomic place. -/
noncomputable def rationalCyclotomicArtinLocalToGlobalMonoidHom
    (m : ℕ+) (q : Nat.Primes) :
    (rationalCyclotomicArtinLocalizedField m q ≃ₐ[
      (rationalCyclotomicArtinBaseAbv q).Completion]
      rationalCyclotomicArtinLocalizedField m q) →*
        (rationalCyclotomicArtinLevel m ≃ₐ[ℚ]
          rationalCyclotomicArtinLevel m) :=
  finitePlaceLocalToGlobalMonoidHom
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q)

/-- The normalized local Artin homomorphism in the cyclotomic localization. -/
noncomputable abbrev rationalCyclotomicArtinLocalArtin
    (m : ℕ+) (q : Nat.Primes)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    rationalCyclotomicArtinLocalizedField m q ≃ₐ[
      (rationalCyclotomicArtinBaseAbv q).Completion]
      rationalCyclotomicArtinLocalizedField m q :=
  finitePlaceLocalArtinMonoidHom
    (K := ℚ) (L := rationalCyclotomicArtinLevel m)
    (rationalCyclotomicArtinPlace q)
    (rationalCyclotomicArtinExtension m q) x

/-- The decomposition-group lift of a specified local arithmetic Frobenius. -/
noncomputable def rationalCyclotomicArtinGlobalFrobeniusOf
    (m : ℕ+) (q : Nat.Primes)
    (hUnramified :
      IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
        (rationalCyclotomicArtinBaseAbv q).Completion
        (rationalCyclotomicArtinLocalizedField m q)) :
    rationalCyclotomicArtinLevel m ≃ₐ[ℚ]
      rationalCyclotomicArtinLevel m :=
  rationalCyclotomicArtinLocalToGlobalMonoidHom m q
    (rationalCyclotomicArtinLocalFrobeniusOf
      m q hUnramified)

/-- The global decomposition-group lift of arithmetic Frobenius at the
chosen place above `q`.  Keeping the local construction opaque prevents its
many completion instances from leaking into later theorem statements. -/
noncomputable def rationalCyclotomicChosenArithmeticFrobenius
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
      KummerTheory.rationalCyclotomicLevel m ≃ₐ[ℚ]
      KummerTheory.rationalCyclotomicLevel m := by
  exact
    rationalCyclotomicArtinGlobalFrobeniusOf m q
      (rationalCyclotomicArtinUnramified m q hq)

/-- The completion input of the chosen finite-place Artin homomorphism. -/
noncomputable abbrev rationalCyclotomicArtinLocalInput
    (q : Nat.Primes)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    (rationalCyclotomicArtinBaseAbv q).Completionˣ :=
  finitePlaceLocalArtinInput
    (K := ℚ) (rationalCyclotomicArtinPlace q) x

/-- The normalized valuation of the canonical completion input used by the
rational finite-place Artin map.  This named endpoint keeps the completion
instances out of downstream theorem statements. -/
noncomputable def rationalCyclotomicArtinLocalExponent
    (q : Nat.Primes)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) : ℤ :=
  IsNonarchimedeanLocalField.valuationMap
    (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion
    (Additive.ofMul
      (finitePlaceLocalArtinInput (K := ℚ) (RayClass.rationalPrime q) x))

/-- The chosen finite-place Artin value in a rational cyclotomic level, with
the completion and Galois instance arguments frozen at the provider boundary. -/
noncomputable def rationalCyclotomicChosenFinitePlaceArtinValue
    (m : ℕ+) (q : Nat.Primes)
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    Gal(KummerTheory.rationalCyclotomicLevel m / ℚ) :=
  chosenFinitePlaceArtinMonoidHom
    (K := ℚ)
    (L := KummerTheory.rationalCyclotomicLevel m)
    (RayClass.rationalPrime q) x

private theorem rationalCyclotomicChosenArithmeticFrobenius_eq_lift
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    rationalCyclotomicChosenArithmeticFrobenius m q hq =
      (absoluteValueDecompositionGroup ℚ
        (rationalCyclotomicArtinExtension m q).1).subtype
        ((rationalCyclotomicArtinDecompositionEquiv m q).symm
          (rationalCyclotomicArtinLocalFrobenius m q hq)) := by
  rfl

private theorem map_eq_zpow_of_eq
    {A B : Type} [Group A] [Group B] (f : A →* B)
    {x y : A} {n : ℤ} (h : x = y ^ n) : f x = f y ^ n :=
  (congrArg f h).trans (map_zpow f y n)

/-- The chosen local Artin symbol is the chosen global Frobenius lift raised
to the normalized local valuation. -/
private theorem
    chosenFinitePlaceArtin_eq_chosenArithmeticFrobenius_zpow
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    chosenFinitePlaceArtinMonoidHom
        (K := ℚ) (L := rationalCyclotomicArtinLevel m)
        (rationalCyclotomicArtinPlace q) x =
      (rationalCyclotomicChosenArithmeticFrobenius m q hq) ^
        rationalCyclotomicArtinLocalExponent q x := by
  let v := rationalCyclotomicArtinPlace q
  let w := rationalCyclotomicArtinExtension m q
  have hFactor := chosenFinitePlaceArtinMonoidHom_apply_factor_of_extension_eq
    (K := ℚ) (L := rationalCyclotomicArtinLevel m) v w rfl x
  have hLocal := finitePlaceLocalArtinMonoidHom_apply_normalized
    (K := ℚ) (L := rationalCyclotomicArtinLevel m) v w x
  let transport := finitePlaceLocalToGlobalMonoidHom
    (K := ℚ) (L := rationalCyclotomicArtinLevel m) v w
  let vK := HeightOneSpectrum.adicAbv ℚ v
  let F : Type := vK.Completion
  let E : Type := LocalizedCompletion vK w
  let baseField : Field F := inferInstance
  let baseValuativeRel := finitePlaceLocalArtinCompletionValuativeRel v
  -- Use the metric completion topology of the finite-place Artin construction.
  let baseTopology : TopologicalSpace F :=
    (inferInstance : PseudoMetricSpace F).toUniformSpace.toTopologicalSpace
  let baseLocalField := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let extensionField : Field E := inferInstance
  let placeIsNonarchimedean := HeightOneSpectrum.isNonarchimedean_adicAbv ℚ v
  let extensionValuativeRel :=
    localizedCompletionFinitePlaceValuativeRel vK w placeIsNonarchimedean
  let extensionUniformity : UniformSpace E := inferInstance
  let extensionLocalField := rationalCyclotomicArtinLocalizedIsNonarchimedeanLocalField m q
  let localAlgebra := finitePlaceLocalArtinLocalizedAlgebra v w
  let localFiniteDimensional := finitePlaceLocalArtinFiniteDimensional v w
  let localAbelianGalois := finitePlaceLocalArtinIsAbelianGalois v w
    (KummerTheory.rationalCyclotomicLevelFiniteDimensional m)
  let valuationExtends := localizedCompletionValuationHasExtension vK w placeIsNonarchimedean
  let unramified := rationalCyclotomicArtinUnramified m q hq
  have hFormulaLocal := @abelianLocalArtinMonoidHom_eq_frobenius_zpow
    F E baseField baseValuativeRel baseTopology
  have hFormulaLocal := @hFormulaLocal baseLocalField
  have hFormulaLocal := @hFormulaLocal extensionField
  have hFormulaLocal := @hFormulaLocal extensionValuativeRel
  have hFormulaLocal := @hFormulaLocal extensionUniformity
  have hFormulaLocal := @hFormulaLocal extensionLocalField
  have hFormulaLocal := @hFormulaLocal localAlgebra localFiniteDimensional localAbelianGalois
  have hFormulaLocal := @hFormulaLocal valuationExtends
  have hFormulaLocal := @hFormulaLocal unramified
  have hFrobeniusLocal := hFormulaLocal (finitePlaceLocalArtinInput v x)
  dsimp (config := { instances := true, zetaDelta := true }) only [inferInstance]
    at hLocal hFrobeniusLocal
  have hSymbol := hLocal.trans hFrobeniusLocal
  have hFormula := map_eq_zpow_of_eq transport hSymbol
  rw [hFactor]
  dsimp only [rationalCyclotomicChosenArithmeticFrobenius,
    rationalCyclotomicArtinGlobalFrobeniusOf, rationalCyclotomicArtinLocalFrobeniusOf,
    rationalCyclotomicArtinLocalExponent]
  dsimp (config := { instances := true, zetaDelta := true }) only [inferInstance]
    at hFormula ⊢
  exact hFormula

private theorem rationalCyclotomicArtinResidueFieldCard
    (q : Nat.Primes) :
    Nat.card 𝓀[(rationalCyclotomicArtinBaseAbv q).Completion] = q.1 := by
  exact
    (rationalFinitePlaceCompletion_residueField_card
      (rationalCyclotomicArtinPlace q)).trans
      (congrArg Subtype.val
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).apply_symm_apply q))

private theorem rationalCyclotomicArtinLocalizedPrimitiveRoot_forField
    (m : ℕ+) (q : Nat.Primes) :
    let E : Type := rationalCyclotomicArtinLocalizedField m q
    let hE : Field E := inferInstance
    @IsPrimitiveRoot E hE.toCommRing.toCommMonoid
      (rationalCyclotomicLocalizedPrimitiveRoot m (rationalCyclotomicArtinPlace q)) (m : ℕ) := by
  intro E hE
  have h := rationalCyclotomicLocalizedPrimitiveRoot_isPrimitiveRoot
    m (rationalCyclotomicArtinPlace q)
  exact ⟨h.pow_eq_one, h.dvd_of_pow_eq_one⟩

private theorem rationalCyclotomicArtinLocalFrobenius_apply_root
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    rationalCyclotomicArtinLocalFrobenius m q hq
        (rationalCyclotomicLocalizedPrimitiveRoot
          m (rationalCyclotomicArtinPlace q)) =
      (rationalCyclotomicLocalizedPrimitiveRoot
        m (rationalCyclotomicArtinPlace q)) ^ q.1 := by
  let := rationalCyclotomicArtinUnramified m q hq
  let := rationalCyclotomicArtinLocalizedIsIntegralClosure m q
  let := rationalCyclotomicArtinLocalizedIntegerModuleFinite m q
  have hRoot := rationalCyclotomicArtinLocalizedPrimitiveRoot_forField m q
  have hCoprime :
      (Nat.card
        𝓀[(rationalCyclotomicArtinBaseAbv q).Completion]).Coprime
          (m : ℕ) := by
    rw [rationalCyclotomicArtinResidueFieldCard q]
    exact q.2.coprime_iff_not_dvd.mpr hq
  let F : Type := (rationalCyclotomicArtinBaseAbv q).Completion
  let E : Type := rationalCyclotomicArtinLocalizedField m q
  let := (rationalCyclotomicArtinLocalizedIsAbelianGalois m q).toIsGalois
  let := rationalCyclotomicArtinLocalizedValuationHasExtension m q
  let ζ : E := rationalCyclotomicLocalizedPrimitiveRoot
    m (rationalCyclotomicArtinPlace q)
  have hAct := arithmeticFrobeniusOfUnramifiedValuation_apply_primitiveRoot
    F E (n := (m : ℕ)) (ζ := ζ)
  have hFrobenius := hAct hRoot hCoprime
  have hPower := congrArg (fun n : ℕ => ζ ^ n) (rationalCyclotomicArtinResidueFieldCard q)
  dsimp only [rationalCyclotomicArtinLocalFrobenius, rationalCyclotomicArtinLocalFrobeniusOf]
  exact hFrobenius.trans hPower

private theorem rationalCyclotomicArtinFrobeniusLift_localization
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (((absoluteValueDecompositionGroup ℚ
          (rationalCyclotomicArtinExtension m q).1).subtype
          ((rationalCyclotomicArtinDecompositionEquiv m q).symm
            (rationalCyclotomicArtinLocalFrobenius m q hq)))
          (rationalCyclotomicLevelPrimitiveRoot m)) =
      rationalCyclotomicArtinLocalFrobenius m q hq
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) := by
  calc
    AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (((absoluteValueDecompositionGroup ℚ
          (rationalCyclotomicArtinExtension m q).1).subtype
          ((rationalCyclotomicArtinDecompositionEquiv m q).symm
            (rationalCyclotomicArtinLocalFrobenius m q hq)))
          (rationalCyclotomicLevelPrimitiveRoot m)) =
      rationalCyclotomicArtinDecompositionEquiv m q
          ((rationalCyclotomicArtinDecompositionEquiv m q).symm
            (rationalCyclotomicArtinLocalFrobenius m q hq))
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) :=
      (localizationRamificationGroups_decompositionGroupEquiv_toLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (RayClass.adicAbv_isNontrivial
          (rationalCyclotomicArtinPlace q))
        (rationalCyclotomicArtinExtension m q)
        ((rationalCyclotomicArtinDecompositionEquiv m q).symm
          (rationalCyclotomicArtinLocalFrobenius m q hq))
        (rationalCyclotomicLevelPrimitiveRoot m)).symm
    _ = rationalCyclotomicArtinLocalFrobenius m q hq
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) :=
      congrArg
        (fun σ : rationalCyclotomicArtinLocalizedField m q ≃ₐ[
          (rationalCyclotomicArtinBaseAbv q).Completion]
          rationalCyclotomicArtinLocalizedField m q =>
            σ (AbsoluteValue.toAlgebraicLocalization
              (rationalCyclotomicArtinBaseAbv q)
              (rationalCyclotomicArtinExtension m q).1
              (rationalCyclotomicArtinExtension m q).2
              (rationalCyclotomicLevelPrimitiveRoot m)))
        ((rationalCyclotomicArtinDecompositionEquiv m q).apply_symm_apply
          (rationalCyclotomicArtinLocalFrobenius m q hq))

private theorem rationalCyclotomicChosenArithmeticFrobenius_localization
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (rationalCyclotomicChosenArithmeticFrobenius m q hq
          (rationalCyclotomicLevelPrimitiveRoot m)) =
      rationalCyclotomicArtinLocalFrobenius m q hq
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) := by
  calc
    AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (rationalCyclotomicChosenArithmeticFrobenius m q hq
          (rationalCyclotomicLevelPrimitiveRoot m)) =
      AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (((absoluteValueDecompositionGroup ℚ
          (rationalCyclotomicArtinExtension m q).1).subtype
          ((rationalCyclotomicArtinDecompositionEquiv m q).symm
            (rationalCyclotomicArtinLocalFrobenius m q hq)))
          (rationalCyclotomicLevelPrimitiveRoot m)) :=
      congrArg
        (fun σ : rationalCyclotomicArtinLevel m ≃ₐ[ℚ]
          rationalCyclotomicArtinLevel m =>
            AbsoluteValue.toAlgebraicLocalization
              (rationalCyclotomicArtinBaseAbv q)
              (rationalCyclotomicArtinExtension m q).1
              (rationalCyclotomicArtinExtension m q).2
              (σ (rationalCyclotomicLevelPrimitiveRoot m)))
        (rationalCyclotomicChosenArithmeticFrobenius_eq_lift m q hq)
    _ = rationalCyclotomicArtinLocalFrobenius m q hq
        (AbsoluteValue.toAlgebraicLocalization
          (rationalCyclotomicArtinBaseAbv q)
          (rationalCyclotomicArtinExtension m q).1
          (rationalCyclotomicArtinExtension m q).2
          (rationalCyclotomicLevelPrimitiveRoot m)) :=
      rationalCyclotomicArtinFrobeniusLift_localization m q hq

private theorem rationalCyclotomicArtinPrimitiveRoot_localization
    (m : ℕ+) (q : Nat.Primes) :
    AbsoluteValue.toAlgebraicLocalization
        (rationalCyclotomicArtinBaseAbv q)
        (rationalCyclotomicArtinExtension m q).1
        (rationalCyclotomicArtinExtension m q).2
        (rationalCyclotomicLevelPrimitiveRoot m) =
      rationalCyclotomicLocalizedPrimitiveRoot
        m (rationalCyclotomicArtinPlace q) := by
  rfl

private theorem rationalCyclotomicArtinLocalizedRoot_pow
    (m : ℕ+) (q : Nat.Primes) :
    (rationalCyclotomicLocalizedPrimitiveRoot
        m (rationalCyclotomicArtinPlace q)) ^ q.1 =
      rationalCyclotomicGlobalToLocalizedAlgHom
        m (rationalCyclotomicArtinPlace q)
        (rationalCyclotomicLevelPrimitiveRoot m ^ q.1) := by
  calc
    (rationalCyclotomicLocalizedPrimitiveRoot
        m (rationalCyclotomicArtinPlace q)) ^ q.1 =
      (rationalCyclotomicGlobalToLocalizedAlgHom
        m (rationalCyclotomicArtinPlace q)
        (rationalCyclotomicLevelPrimitiveRoot m)) ^ q.1 :=
      congrArg (fun z => z ^ q.1)
        (rationalCyclotomicGlobalToLocalizedAlgHom_primitiveRoot m
          (rationalCyclotomicArtinPlace q)).symm
    _ = rationalCyclotomicGlobalToLocalizedAlgHom
        m (rationalCyclotomicArtinPlace q)
        (rationalCyclotomicLevelPrimitiveRoot m ^ q.1) :=
      (map_pow
        (rationalCyclotomicGlobalToLocalizedAlgHom
          m (rationalCyclotomicArtinPlace q))
        (rationalCyclotomicLevelPrimitiveRoot m) q.1).symm

private theorem rationalCyclotomicChosenArithmeticFrobenius_apply_root
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    rationalCyclotomicChosenArithmeticFrobenius m q hq
        (rationalCyclotomicLevelPrimitiveRoot m) =
      rationalCyclotomicLevelPrimitiveRoot m ^ q.1 := by
  apply
    (AbsoluteValue.toAlgebraicLocalization
      (rationalCyclotomicArtinBaseAbv q)
      (rationalCyclotomicArtinExtension m q).1
      (rationalCyclotomicArtinExtension m q).2).injective
  have hLocalization := rationalCyclotomicChosenArithmeticFrobenius_localization m q hq
  have hPrimitiveRoot := congrArg (rationalCyclotomicArtinLocalFrobenius m q hq)
    (rationalCyclotomicArtinPrimitiveRoot_localization m q)
  have hLocalFrobenius := rationalCyclotomicArtinLocalFrobenius_apply_root m q hq
  have hPower := rationalCyclotomicArtinLocalizedRoot_pow m q
  have hAlgebraicLocalization := rationalCyclotomicGlobalToLocalizedAlgHom_apply
    m (rationalCyclotomicArtinPlace q) (rationalCyclotomicLevelPrimitiveRoot m ^ q.1)
  exact hLocalization.trans (hPrimitiveRoot.trans
    (hLocalFrobenius.trans (hPower.trans hAlgebraicLocalization)))

/-- The cyclotomic character sends the chosen arithmetic Frobenius lift to
the residue prime. -/
private theorem galEquivZMod_chosenArithmeticFrobenius
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)
        (rationalCyclotomicChosenArithmeticFrobenius m q hq) =
      ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq) := by
  exact
    rationalCyclotomicLevel_galEquivZMod_eq_unitOfCoprime
      m q hq (rationalCyclotomicChosenArithmeticFrobenius m q hq)
      (rationalCyclotomicChosenArithmeticFrobenius_apply_root m q hq)

/-- At a rational prime not dividing the level, the cyclotomic character
of the chosen finite-place Artin symbol is the residue prime raised to the
normalized local valuation. -/
theorem galEquivZMod_chosenFinitePlaceArtinMonoidHom_of_not_dvd
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ) :
    let v : HeightOneSpectrum (𝓞 ℚ) :=
      RayClass.rationalPrime q
    let L := KummerTheory.rationalCyclotomicLevel m
    let vQ := HeightOneSpectrum.adicAbv ℚ v
    let localInput :=
      (finitePlaceCompletionUnitsContinuousMulEquiv v).symm x
    let localExponent :=
      LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
        vQ.Completion (Additive.ofMul localInput)
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ) L
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := L) v x) =
      (ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq)) ^ localExponent := by
  dsimp only
  rw [chosenFinitePlaceArtin_eq_chosenArithmeticFrobenius_zpow
      m q hq x, map_zpow,
    galEquivZMod_chosenArithmeticFrobenius m q hq]
  rfl

/-- Away from the cyclotomic level, a finite-place input of normalized
valuation zero has trivial cyclotomic character. -/
theorem
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_eq_one_of_not_dvd_of_localExponent_eq_zero
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hzero : rationalCyclotomicArtinLocalExponent q x = 0) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel m)
          (RayClass.rationalPrime q) x) =
      1 := by
  rw [chosenFinitePlaceArtin_eq_chosenArithmeticFrobenius_zpow
      m q hq x,
    map_zpow, galEquivZMod_chosenArithmeticFrobenius m q hq,
    hzero, zpow_zero]

/-- Away from the cyclotomic level, valuation zero makes the chosen
finite-place Artin symbol itself trivial.  Returning the Galois element,
rather than an equality between cyclotomic characters with frozen instance
arguments, lets downstream restriction arguments apply their own canonical
character without a dependent instance transport. -/
theorem
    chosenFinitePlaceArtinMonoidHom_eq_one_of_not_dvd_of_localExponent_eq_zero
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (x : ((RayClass.rationalPrime q).adicCompletion ℚ)ˣ)
    (hzero : rationalCyclotomicArtinLocalExponent q x = 0) :
    chosenFinitePlaceArtinMonoidHom
        (K := ℚ)
        (L := KummerTheory.rationalCyclotomicLevel m)
        (RayClass.rationalPrime q) x =
      1 := by
  apply
    (IsCyclotomicExtension.Rat.galEquivZMod
      (m : ℕ) (KummerTheory.rationalCyclotomicLevel m)).injective
  simpa only [map_one] using
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_eq_one_of_not_dvd_of_localExponent_eq_zero
      m q hq x hzero

/-- For a rational principal idele, the unramified finite-place
cyclotomic Artin symbol at `q` is `q` raised to the negative usual
`q`-adic exponent. -/
theorem
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_principal_of_not_dvd
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ)) (x : ℚˣ) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ)
        (KummerTheory.rationalCyclotomicLevel m)
        (chosenFinitePlaceArtinMonoidHom
          (K := ℚ)
          (L := KummerTheory.rationalCyclotomicLevel m)
          (RayClass.rationalPrime q)
          (IdeleGroup.finiteComponent
            (RayClass.rationalPrime q)
            (IdeleGroup.principalIdele ℚ x))) =
      (ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq)) ^
          (-padicValRat q.1 (x : ℚ)) := by
  rw [
    galEquivZMod_chosenFinitePlaceArtinMonoidHom_of_not_dvd
      m q hq,
    rationalPrincipalFiniteComponent_valuationMap]

end Reciprocity
end GlobalClassFieldTheory
