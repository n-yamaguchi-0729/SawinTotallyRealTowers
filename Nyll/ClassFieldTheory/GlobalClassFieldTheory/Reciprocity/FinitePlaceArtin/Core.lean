/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceModel

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Ramification.Splitting.FinitePlace
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Conjugation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.TowerRestriction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.CrossLocalRestriction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.NormRestriction
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UniverseArtin
public import Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completion
public import Nyll.ValuedFieldTheory.Valuation.Completion.FiniteLocalization

/-!
# Image and kernel of finite-place Artin homomorphisms

This module identifies the image with the chosen decomposition group and the kernel with the chosen
local norm subgroup.
-/



@[expose] public section

open scoped IsMulCommutative NNReal NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory

universe uK uL

variable {K : Type uK} {L : Type uL}
    [Field K] [NumberField K]
    [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]

private theorem finitePlaceLocalArtinMonoidHom_surjective
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L) :
    Function.Surjective (finitePlaceLocalArtinMonoidHom v w) := by
  let vK := HeightOneSpectrum.adicAbv K v
  let E := LocalizedCompletion vK w
  let := finitePlaceLocalArtinLocalizedAlgebra v w
  let := finitePlaceLocalArtinFiniteDimensional v w
  let := finitePlaceLocalArtinIsAbelianGalois v w (inferInstance : FiniteDimensional K L)
  let := finitePlaceLocalArtinCompletionValuativeRel v
  let := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  dsimp only [finitePlaceLocalArtinMonoidHom, finitePlaceLocalArtinInputMonoidHom]
  rw [MonoidHom.coe_comp]
  apply Function.Surjective.comp
  · apply abelianLocalArtinMonoidHom_surjective
  · exact (finitePlaceCompletionUnitsContinuousMulEquiv v).symm.surjective

private theorem finitePlaceLocalArtinMonoidHom_ker
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension (HeightOneSpectrum.adicAbv K v) L) :
    let vK := HeightOneSpectrum.adicAbv K v
    let E := LocalizedCompletion vK w
    let : Algebra vK.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
    (finitePlaceLocalArtinMonoidHom v w).ker =
      (localNormSubgroup vK.Completion E).map
        (finitePlaceCompletionUnitsContinuousMulEquiv v).toMonoidHom := by
  intro vK E
  let := finitePlaceLocalArtinLocalizedAlgebra v w
  let := finitePlaceLocalArtinFiniteDimensional v w
  let := finitePlaceLocalArtinIsAbelianGalois v w (inferInstance : FiniteDimensional K L)
  let := finitePlaceLocalArtinCompletionValuativeRel v
  let := finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  dsimp only [finitePlaceLocalArtinMonoidHom, finitePlaceLocalArtinInputMonoidHom]
  rw [← MonoidHom.comap_ker, abelianLocalArtinMonoidHom_ker]
  exact Subgroup.comap_equiv_eq_map_symm'
    (finitePlaceCompletionUnitsContinuousMulEquiv v).symm.toMulEquiv _

/-- The image of the chosen finite-place Artin homomorphism is exactly
the chosen decomposition group. -/
theorem chosenFinitePlaceArtinMonoidHom_range
    (v : HeightOneSpectrum (𝓞 K)) :
    (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v).range =
      finitePlaceDecompositionGroup
        (K := K) (L := L) v := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let := finitePlaceLocalArtinLocalizedAlgebra v w
  let eD := decompositionGroupEquivAlgebraicLocalizationAut
    vK (RayClass.adicAbv_isNontrivial v) w
  have hLocal := finitePlaceLocalArtinMonoidHom_surjective v w
  rw [chosenFinitePlaceArtinMonoidHom, finitePlaceArtinMonoidHomOfExtension_factor,
    MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hLocal, ← MonoidHom.range_eq_map]
  dsimp only [finitePlaceLocalToGlobalMonoidHom, finitePlaceDecompositionGroup]
  rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eD.symm.surjective,
    ← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- The kernel of the concrete finite-place Artin homomorphism is
exactly the chosen local norm subgroup. -/
theorem chosenFinitePlaceArtinMonoidHom_ker
    (v : HeightOneSpectrum (𝓞 K)) :
    MonoidHom.ker
        (chosenFinitePlaceArtinMonoidHom
          (K := K) (L := L) v) =
      chosenFinitePlaceLocalNormSubgroup
        (K := K) (L := L) v := by
  let vK := HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let := finitePlaceLocalArtinLocalizedAlgebra v w
  let eD := decompositionGroupEquivAlgebraicLocalizationAut
    vK (RayClass.adicAbv_isNontrivial v) w
  have hGlobal : Function.Injective (finitePlaceLocalToGlobalMonoidHom v w) := by
    dsimp only [finitePlaceLocalToGlobalMonoidHom]
    exact Subtype.coe_injective.comp eD.symm.injective
  rw [chosenFinitePlaceArtinMonoidHom, finitePlaceArtinMonoidHomOfExtension_factor,
    MonoidHom.ker_comp_of_injective _ _ hGlobal]
  exact finitePlaceLocalArtinMonoidHom_ker v w

end Reciprocity
end GlobalClassFieldTheory
