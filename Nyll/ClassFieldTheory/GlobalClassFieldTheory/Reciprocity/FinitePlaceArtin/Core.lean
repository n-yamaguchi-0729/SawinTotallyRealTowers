/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

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

/-- The image of the chosen finite-place Artin homomorphism is exactly
the chosen decomposition group. -/
theorem chosenFinitePlaceArtinMonoidHom_range
    (v : HeightOneSpectrum (𝓞 K)) :
    (chosenFinitePlaceArtinMonoidHom
        (K := K) (L := L) v).range =
      finitePlaceDecompositionGroup
        (K := K) (L := L) v := by
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : Algebra vK.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
  let : FiniteDimensional vK.Completion E := finitePlaceLocalArtinFiniteDimensional v w
  let : IsAbelianGalois vK.Completion E := finitePlaceLocalArtinIsAbelianGalois v w
    (inferInstance : FiniteDimensional K L)
  let : ValuativeRel vK.Completion := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField vK.Completion :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let eD : absoluteValueDecompositionGroup K w.1 ≃* (E ≃ₐ[vK.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut vK (RayClass.adicAbv_isNontrivial v) w
  let eK : vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  have hLocal : Function.Surjective (finitePlaceLocalArtinMonoidHom v w) := by
    intro σ
    obtain ⟨u, hu⟩ :=
      LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_surjective vK.Completion E σ
    refine ⟨eK u, ?_⟩
    rw [finitePlaceLocalArtinMonoidHom_apply_universe]
    rw [eK.symm_apply_apply]
    with_reducible exact hu
  rw [chosenFinitePlaceArtinMonoidHom, finitePlaceArtinMonoidHomOfExtension_factor,
    MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hLocal, ← MonoidHom.range_eq_map]
  change ((absoluteValueDecompositionGroup K w.1).subtype.comp eD.symm.toMonoidHom).range =
    absoluteValueDecompositionGroup K w.1
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
  let vK := NumberField.HeightOneSpectrum.adicAbv K v
  let w := chosenFinitePlaceExtension (L := L) v
  let E := AlgebraicNumberTheory.Valuations.LocalizedCompletion vK w
  let : Algebra vK.Completion E := finitePlaceLocalArtinLocalizedAlgebra v w
  let : FiniteDimensional vK.Completion E := finitePlaceLocalArtinFiniteDimensional v w
  let : IsAbelianGalois vK.Completion E := finitePlaceLocalArtinIsAbelianGalois v w
    (inferInstance : FiniteDimensional K L)
  let : ValuativeRel vK.Completion := finitePlaceLocalArtinCompletionValuativeRel v
  let : IsNonarchimedeanLocalField vK.Completion :=
    finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField v
  let eD : absoluteValueDecompositionGroup K w.1 ≃* (E ≃ₐ[vK.Completion] E) :=
    decompositionGroupEquivAlgebraicLocalizationAut vK (RayClass.adicAbv_isNontrivial v) w
  let eK : vK.Completionˣ ≃* (v.adicCompletion K)ˣ :=
    finitePlaceCompletionUnitsContinuousMulEquiv v
  let localArtin := LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom vK.Completion E
  have hEval (x : (v.adicCompletion K)ˣ) :
      chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v x =
        (absoluteValueDecompositionGroup K w.1).subtype (eD.symm (localArtin (eK.symm x))) := by
    unfold chosenFinitePlaceArtinMonoidHom
    have h := finitePlaceArtinMonoidHomOfExtension_apply_universe v w x
    with_reducible exact h
  apply SetLike.ext
  intro x
  change chosenFinitePlaceArtinMonoidHom (K := K) (L := L) v x = 1 ↔
    x ∈ (localNormSubgroup vK.Completion E).map eK.toMonoidHom
  rw [hEval]
  constructor
  · intro hx
    change
      (absoluteValueDecompositionGroup K w.1).subtype
          (eD.symm (localArtin (eK.symm x))) = 1 at hx
    have hxSubgroup :
        eD.symm (localArtin (eK.symm x)) = 1 := by
      apply Subtype.coe_injective
      exact hx
    have hxLocal :
        localArtin (eK.symm x) = 1 := by
      apply eD.symm.injective
      simpa only [map_one] using hxSubgroup
    have hxKer :
        eK.symm x ∈ MonoidHom.ker localArtin :=
      hxLocal
    have hxNorm :
        eK.symm x ∈ localNormSubgroup vK.Completion E := by
      rw [
        LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_ker
      ] at hxKer
      exact hxKer
    exact
      ⟨eK.symm x, hxNorm, eK.apply_symm_apply x⟩
  · rintro ⟨y, hy, rfl⟩
    have hyKer :
        y ∈ MonoidHom.ker localArtin := by
      rw [
        LocalClassFieldTheory.Universe.abelianLocalArtinMonoidHom_ker
      ]
      exact hy
    have hyArtin : localArtin y = 1 := hyKer
    change
      (absoluteValueDecompositionGroup K w.1).subtype
          (eD.symm (localArtin (eK.symm (eK y)))) = 1
    simp only [eK.symm_apply_apply, hyArtin, map_one]

end Reciprocity
end GlobalClassFieldTheory
