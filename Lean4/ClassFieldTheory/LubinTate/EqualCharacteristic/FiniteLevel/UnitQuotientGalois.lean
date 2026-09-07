import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedLevel
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedCompletedPrimitiveAction
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedPolynomialEvaluation
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizer
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ChangedUniformizerNormalization
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusBaseEquiv
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusContinuity
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedField
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldAlgebra
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldCoefficientDescent
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldDegree
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldGeneration
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPowerBasis
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedFieldPrimitive
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusLift
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedFrobeniusFixedNorm
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedLevel
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveAction
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.CompletedPrimitiveIrreducible
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectBracketAtCompletedLevel
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracket
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectLubinTateBracketRecursion
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectTargetLevelEmbedding
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaAtCompletedLevel
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFirstIdentity
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaFrobeniusFixed
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaIteration
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.DirectThetaSeries
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaAtCompletedLevel
import ClassFieldTheory.LubinTate.EqualCharacteristic.CompletedLevel.ThetaLocalInverse
import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentLocalField
import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentModel
import ClassFieldTheory.LubinTate.EqualCharacteristic.Existence.LaurentUniformizerNormalization
import ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.AmbientBracketAction
import ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.DivisionModuleEndomorphisms
import ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateAction
import ClassFieldTheory.LubinTate.EqualCharacteristic.FormalModule.LubinTateEndomorphism
import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CoefficientFrobenius
import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.CompletedUnramifiedField
import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.ContractingEquation
import ClassFieldTheory.LubinTate.EqualCharacteristic.Frobenius.LaurentSeriesFrobenius
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEmbedding
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldEquiv
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldMembership
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFixedFieldSurjective
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitFrobeniusFixed
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitLevelMapFixed
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnits
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.HigherUnitsNorm
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.LevelAlgebra
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.StandardSubgroupNorm
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UniformizerNorm
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitQuotientCard
import ClassFieldTheory.LubinTate.EqualCharacteristic.NormSubgroup.UnitTransport
import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaCoefficients
import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaEvaluation
import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaFirstIdentity
import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaSeries
import ClassFieldTheory.LubinTate.EqualCharacteristic.Theta.ThetaUniqueness
import ClassFieldTheory.LubinTate.EqualCharacteristic.RealIndexSteps
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.AmbientDivisionTorsion
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.DivisionPolynomial
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FiniteParameters
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.FreeRankOne
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAbelian
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelAutomorphisms
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelField
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.LevelFieldTower
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.NormUniformizer
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveAction
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveIrreducible
import ClassFieldTheory.LubinTate.EqualCharacteristic.FiniteLevel.PrimitiveTorsion

set_option autoImplicit false

/-!
# Equal-characteristic Lubin--Tate unit quotients and Galois groups

This file constructs the finite-level Galois action of a power-series unit
with the local-Artin orientation: `a` sends the chosen primitive generator
to `[a⁻¹]`.  Its kernel is the `(n + 1)`-st higher-unit subgroup, so the
action descends to a multiplicative equivalence from the finite unit
quotient to the Galois group.
-/

noncomputable section

open scoped LaurentSeries PowerSeries Polynomial

universe u v

namespace LubinTate

open LocalFieldTheory.DiscreteValuationField
open LubinTate.EqualCharacteristic

variable {K : Type u} [Field K]

/-- The finite-level root obtained from the Artin-oriented bracket `[a⁻¹]`. -/
noncomputable def equalCharacteristicLubinTateArtinUnitLevelRoot
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateLevelField F n :=
  equalCharacteristicLubinTateLevelBracket F n (n + 1)
    ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
    (equalCharacteristicLubinTateLevelPowerBasis F n).gen

/-- The Artin-oriented unit root annihilates the generator's minimal
polynomial. -/
theorem equalCharacteristicLubinTateArtinUnitLevelRoot_aeval_minpoly
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    Polynomial.aeval
        (equalCharacteristicLubinTateArtinUnitLevelRoot F n a)
        (minpoly F.residueField⸨X⸩
          (equalCharacteristicLubinTateLevelPowerBasis F n).gen) = 0 := by
  rw [equalCharacteristicLubinTateLevelPowerBasis_minpoly]
  let ι : equalCharacteristicLubinTateLevelField F n →ₐ[
      F.residueField⸨X⸩] SeparableClosure F.residueField⸨X⸩ :=
    (equalCharacteristicLubinTateLevelField F n).val
  apply ι.injective
  change ι (Polynomial.aeval
      (equalCharacteristicLubinTateArtinUnitLevelRoot F n a)
      (equalCharacteristicLubinTatePrimitivePolynomial F n)) = ι 0
  rw [← Polynomial.aeval_algHom_apply (f := ι), map_zero]
  rw [Polynomial.aeval_def,
    ← equalCharacteristicSeparableBaseHom_eq_algebraMap]
  change Polynomial.eval₂
      (equalCharacteristicSeparableBaseHom F)
      (equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n))
      (equalCharacteristicLubinTatePrimitivePolynomial F n) = 0
  simpa [Polynomial.IsRoot, Polynomial.eval_map] using
    (equalCharacteristicLubinTatePrimitivePolynomial_isRoot_bracket
      F n a⁻¹)

/-- The finite-level algebra endomorphism with Artin orientation. -/
noncomputable def equalCharacteristicLubinTateArtinUnitAlgHom
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateLevelField F n →ₐ[F.residueField⸨X⸩]
      equalCharacteristicLubinTateLevelField F n :=
  (equalCharacteristicLubinTateLevelPowerBasis F n).lift
    (equalCharacteristicLubinTateArtinUnitLevelRoot F n a)
    (equalCharacteristicLubinTateArtinUnitLevelRoot_aeval_minpoly F n a)

@[simp]
theorem equalCharacteristicLubinTateArtinUnitAlgHom_apply_gen
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitAlgHom F n a
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      equalCharacteristicLubinTateArtinUnitLevelRoot F n a :=
  (equalCharacteristicLubinTateLevelPowerBasis F n).lift_gen _ _

/-- The finite-level Galois automorphism whose generator action is
`[a⁻¹]`. -/
noncomputable def equalCharacteristicLubinTateArtinUnitAlgEquiv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateLevelField F n ≃ₐ[F.residueField⸨X⸩]
      equalCharacteristicLubinTateLevelField F n := by
  letI : FiniteDimensional F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n) :=
    equalCharacteristicLubinTateLevelField_finiteDimensional F n
  exact AlgEquiv.ofBijective
    (equalCharacteristicLubinTateArtinUnitAlgHom F n a)
    (AlgHom.bijective (equalCharacteristicLubinTateArtinUnitAlgHom F n a))

@[simp]
theorem equalCharacteristicLubinTateArtinUnitAlgEquiv_apply_gen
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitAlgEquiv F n a
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      equalCharacteristicLubinTateArtinUnitLevelRoot F n a := by
  rw [equalCharacteristicLubinTateArtinUnitAlgEquiv,
    AlgEquiv.ofBijective_apply,
    equalCharacteristicLubinTateArtinUnitAlgHom_apply_gen]

theorem equalCharacteristicLubinTateArtinUnitAlgEquiv_one
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    equalCharacteristicLubinTateArtinUnitAlgEquiv F n 1 = 1 := by
  apply MulSemiringAction.toAlgHom_injective F.residueField⸨X⸩
    (equalCharacteristicLubinTateLevelField F n)
  apply (equalCharacteristicLubinTateLevelPowerBasis F n).algHom_ext
  simp only [MulSemiringAction.toAlgHom_apply, one_smul,
    AlgEquiv.smul_def]
  rw [equalCharacteristicLubinTateArtinUnitAlgEquiv_apply_gen]
  apply Subtype.ext
  change
    equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        (((1 : F.residueField⟦X⟧ˣ)⁻¹ :
          F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
      chosenEqualCharacteristicLubinTatePrimitiveRoot F n
  simpa using
    (equalCharacteristicLubinTateAmbientBracket_one_apply_of_torsion F
      (equalCharacteristicSeparableCoefficientHom F)
      (equalCharacteristicSeparableUniformizer F) (n + 1)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
      (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n))

theorem equalCharacteristicLubinTateArtinUnitAlgEquiv_mul
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a b : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitAlgEquiv F n (a * b) =
      equalCharacteristicLubinTateArtinUnitAlgEquiv F n a *
        equalCharacteristicLubinTateArtinUnitAlgEquiv F n b := by
  apply MulSemiringAction.toAlgHom_injective F.residueField⸨X⸩
    (equalCharacteristicLubinTateLevelField F n)
  apply (equalCharacteristicLubinTateLevelPowerBasis F n).algHom_ext
  simp only [MulSemiringAction.toAlgHom_apply, mul_smul,
    AlgEquiv.smul_def]
  rw [equalCharacteristicLubinTateArtinUnitAlgEquiv_apply_gen,
    equalCharacteristicLubinTateArtinUnitAlgEquiv_apply_gen]
  unfold equalCharacteristicLubinTateArtinUnitLevelRoot
  have hmap :
      equalCharacteristicLubinTateArtinUnitAlgEquiv F n a
          (equalCharacteristicLubinTateLevelBracket F n (n + 1)
            ((b⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
            (equalCharacteristicLubinTateLevelPowerBasis F n).gen) =
        equalCharacteristicLubinTateLevelBracket F n (n + 1)
          ((b⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
          (equalCharacteristicLubinTateArtinUnitAlgEquiv F n a
            (equalCharacteristicLubinTateLevelPowerBasis F n).gen) := by
    simpa only [AlgEquiv.toAlgHom_apply] using
      (equalCharacteristicLubinTateLevelBracket_map F n (n + 1)
        ((b⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
        (equalCharacteristicLubinTateArtinUnitAlgEquiv F n a).toAlgHom
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen)
  rw [hmap, equalCharacteristicLubinTateArtinUnitAlgEquiv_apply_gen]
  apply Subtype.ext
  change
    equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        ((((a * b)⁻¹ : F.residueField⟦X⟧ˣ)) :
          F.residueField⟦X⟧)
        (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
      equalCharacteristicLubinTateAmbientBracket F
        (equalCharacteristicSeparableCoefficientHom F)
        (equalCharacteristicSeparableUniformizer F) (n + 1)
        ((b⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
        (equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1)
          ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n))
  rw [← equalCharacteristicLubinTateAmbientBracket_mul_apply_of_torsion
    F (equalCharacteristicSeparableCoefficientHom F)
    (equalCharacteristicSeparableUniformizer F) (n + 1)
    ((b⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
    ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
    (chosenEqualCharacteristicLubinTatePrimitiveRoot F n)
    (chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n)]
  congr 2

/-- Power-series units acting on the finite Lubin--Tate level with Artin
orientation. -/
noncomputable def equalCharacteristicLubinTateArtinUnitToGal
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    F.residueField⟦X⟧ˣ →*
      Gal((equalCharacteristicLubinTateLevelField F n) /
        F.residueField⸨X⸩) where
  toFun := equalCharacteristicLubinTateArtinUnitAlgEquiv F n
  map_one' := equalCharacteristicLubinTateArtinUnitAlgEquiv_one F n
  map_mul' := equalCharacteristicLubinTateArtinUnitAlgEquiv_mul F n

@[simp]
theorem equalCharacteristicLubinTateArtinUnitToGal_apply_gen
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitToGal F n a
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen =
      equalCharacteristicLubinTateArtinUnitLevelRoot F n a :=
  equalCharacteristicLubinTateArtinUnitAlgEquiv_apply_gen F n a

/-- The kernel of the Artin-oriented explicit unit action is the level
higher-unit subgroup. -/
theorem equalCharacteristicLubinTateArtinUnitToGal_ker
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    MonoidHom.ker (equalCharacteristicLubinTateArtinUnitToGal F n) =
      equalCharacteristicLubinTateHigherUnitSubgroup F n := by
  ext a
  rw [MonoidHom.mem_ker]
  constructor
  · intro ha
    have hgen := congrArg
      (fun σ : Gal((equalCharacteristicLubinTateLevelField F n) /
          F.residueField⸨X⸩) =>
        σ (equalCharacteristicLubinTateLevelPowerBasis F n).gen) ha
    rw [equalCharacteristicLubinTateArtinUnitToGal_apply_gen] at hgen
    simp only [AlgEquiv.one_apply] at hgen
    have hgen' := congrArg Subtype.val hgen
    change
      equalCharacteristicLubinTateAmbientBracket F
          (equalCharacteristicSeparableCoefficientHom F)
          (equalCharacteristicSeparableUniformizer F) (n + 1)
          ((a⁻¹ : F.residueField⟦X⟧ˣ) : F.residueField⟦X⟧)
          (chosenEqualCharacteristicLubinTatePrimitiveRoot F n) =
        chosenEqualCharacteristicLubinTatePrimitiveRoot F n at hgen'
    exact
      (equalCharacteristicLubinTateAmbientBracket_inv_primitiveRoot_eq_iff_mem_higherUnitSubgroup
        F n a).1 hgen'
  · intro ha
    apply MulSemiringAction.toAlgHom_injective F.residueField⸨X⸩
      (equalCharacteristicLubinTateLevelField F n)
    apply (equalCharacteristicLubinTateLevelPowerBasis F n).algHom_ext
    simp only [MulSemiringAction.toAlgHom_apply, one_smul,
      AlgEquiv.smul_def]
    rw [equalCharacteristicLubinTateArtinUnitToGal_apply_gen]
    apply Subtype.ext
    exact
      (equalCharacteristicLubinTateAmbientBracket_inv_primitiveRoot_eq_iff_mem_higherUnitSubgroup
        F n a).2 ha

/-- A visible finite parameter is obtained from the Artin-oriented unit
action by inverting its represented power-series unit. -/
theorem equalCharacteristicLubinTateArtinUnitToGal_parameterUnit_inv
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (p : equalCharacteristicLubinTateUnitParameter F n) :
    equalCharacteristicLubinTateArtinUnitToGal F n
        (equalCharacteristicLubinTateUnitParameterUnit F n p)⁻¹ =
      equalCharacteristicLubinTateUnitParameterAlgEquiv F n p := by
  apply MulSemiringAction.toAlgHom_injective F.residueField⸨X⸩
    (equalCharacteristicLubinTateLevelField F n)
  apply (equalCharacteristicLubinTateLevelPowerBasis F n).algHom_ext
  simp only [MulSemiringAction.toAlgHom_apply, AlgEquiv.smul_def]
  rw [equalCharacteristicLubinTateArtinUnitToGal_apply_gen,
    equalCharacteristicLubinTateUnitParameterAlgEquiv_apply_gen]
  apply Subtype.ext
  simp only [equalCharacteristicLubinTateArtinUnitLevelRoot,
    equalCharacteristicLubinTateLevelBracket_coe,
    equalCharacteristicLubinTateUnitParameterLevelRoot_coe,
    equalCharacteristicLubinTateUnitParameterRoot, inv_inv,
    equalCharacteristicLubinTateUnitParameterUnit_val,
    equalCharacteristicLubinTateLevelPowerBasis_gen_coe]

/-- Every finite-level Galois automorphism is induced by an Artin-oriented
power-series unit. -/
theorem equalCharacteristicLubinTateArtinUnitToGal_surjective
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    Function.Surjective
      (equalCharacteristicLubinTateArtinUnitToGal F n) := by
  intro σ
  obtain ⟨p, hp⟩ :=
    equalCharacteristicLubinTateLevelField_exists_unitParameter F n σ
  refine ⟨(equalCharacteristicLubinTateUnitParameterUnit F n p)⁻¹, ?_⟩
  exact (equalCharacteristicLubinTateArtinUnitToGal_parameterUnit_inv
    F n p).trans hp.symm

/-- The Artin-oriented explicit finite-level reciprocity equivalence from
the unit quotient. -/
noncomputable def equalCharacteristicLubinTateArtinUnitQuotientEquivGal
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) :
    F.residueField⟦X⟧ˣ ⧸
        equalCharacteristicLubinTateHigherUnitSubgroup F n ≃*
      Gal((equalCharacteristicLubinTateLevelField F n) /
        F.residueField⸨X⸩) :=
  (QuotientGroup.quotientMulEquivOfEq
      (equalCharacteristicLubinTateArtinUnitToGal_ker F n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (equalCharacteristicLubinTateArtinUnitToGal F n)
      (equalCharacteristicLubinTateArtinUnitToGal_surjective F n))

@[simp]
theorem equalCharacteristicLubinTateArtinUnitQuotientEquivGal_mk
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitQuotientEquivGal F n
        (QuotientGroup.mk a) =
      equalCharacteristicLubinTateArtinUnitToGal F n a := by
  simp only [equalCharacteristicLubinTateArtinUnitQuotientEquivGal,
    MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

/-- On a representative, the quotient-to-Galois equivalence is the inverse
orientation of the existing quotient action on the primitive torsion
point. -/
theorem
    equalCharacteristicLubinTateArtinUnitQuotientEquivGal_mk_apply_gen_coe
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    ((equalCharacteristicLubinTateArtinUnitQuotientEquivGal F n
          (QuotientGroup.mk a))
        (equalCharacteristicLubinTateLevelPowerBasis F n).gen :
      SeparableClosure F.residueField⸨X⸩) =
      (equalCharacteristicLubinTateUnitQuotientAutomorphismEquiv F n
        (QuotientGroup.mk a⁻¹)
        (⟨chosenEqualCharacteristicLubinTatePrimitiveRoot F n,
          chosenEqualCharacteristicLubinTatePrimitiveRoot_torsion F n⟩ :
          equalCharacteristicLubinTateAmbientTorsionAddSubgroup F
            (equalCharacteristicSeparableUniformizer F) (n + 1))).1 := by
  rw [equalCharacteristicLubinTateArtinUnitQuotientEquivGal_mk,
    equalCharacteristicLubinTateArtinUnitToGal_apply_gen]
  rw [equalCharacteristicLubinTateUnitQuotientAutomorphismEquiv_mk_apply]
  rfl

/-- Kernel membership in pointwise form. -/
theorem equalCharacteristicLubinTateArtinUnitToGal_eq_one_iff
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitToGal F n a = 1 ↔
      a ∈ equalCharacteristicLubinTateHigherUnitSubgroup F n := by
  rw [← MonoidHom.mem_ker,
    equalCharacteristicLubinTateArtinUnitToGal_ker]

/-- The explicit congruence criterion for trivial finite-level action. -/
theorem equalCharacteristicLubinTateArtinUnitToGal_eq_one_iff_sub_one_mem
    (F : LocalField.{u, v} K)
    [CharP K F.residueCharacteristic]
    (n : ℕ) (a : F.residueField⟦X⟧ˣ) :
    equalCharacteristicLubinTateArtinUnitToGal F n a = 1 ↔
      (a : F.residueField⟦X⟧) - 1 ∈
        Ideal.span
          ({PowerSeries.X ^ (n + 1)} : Set F.residueField⟦X⟧) :=
  (equalCharacteristicLubinTateArtinUnitToGal_eq_one_iff F n a).trans
    (mem_equalCharacteristicLubinTateHigherUnitSubgroup F n a)

end LubinTate
