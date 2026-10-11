/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CrowellExactSequence.Discrete.SequenceMaps

/-!
# Discrete Crowell exactness

Surjectivity and the kernel/image identities for the relative Fox derivative assemble into the
four-term discrete Crowell sequence. The free-group presentation theorem specializes this
criterion to the Blanchfield--Lyndon exact sequence.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential

open scoped BigOperators

namespace Morishita2024

variable {H : Type} [Group H]

/-- Discrete Crowell exact sequence for a surjective group homomorphism. -/
theorem crowellExactSequence_of_surjective
    {G : Type} [Group G]
    (psi : MonoidHom G H) (hpsi : Function.Surjective psi) :
    letI := kernelAbelianizationModuleOfSurjective psi hpsi
    Function.Injective
        (kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi) ∧
      Function.Exact
        (kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi)
        (toGroupRing psi) ∧
      Function.Exact (toGroupRing psi) (augmentation H) ∧
      Function.Surjective (augmentation H) := by
  let := kernelAbelianizationModuleOfSurjective psi hpsi
  refine ⟨?_, ?_, exact_toGroupRing_augmentation (H := H) psi hpsi,
    augmentation_surjective (H := H)⟩
  · exact FoxDifferential.kernelAbelianizationBoundaryLinearOfSurjective_injective
      (H := H) (ψ := psi) hpsi
  · exact exact_kernelAbelianizationBoundaryLinearOfSurjective_toGroupRing (H := H) psi hpsi

/-- The discrete Blanchfield--Lyndon exact sequence for a surjective finite free presentation. -/
theorem freeGroupPresentation_blanchfieldLyndonExactSequence
    (r : Nat) (psi : MonoidHom (FreeGroup (Fin r)) H) (hpsi : Function.Surjective psi) :
    letI := kernelAbelianizationModuleOfSurjective psi hpsi
    Function.Injective
        (FoxCalculus.freeGroupPresentationRelativeDerivativeHeadMap (H := H) r psi hpsi) ∧
      Function.Exact
        (FoxCalculus.freeGroupPresentationRelativeDerivativeHeadMap (H := H) r psi hpsi)
        (FoxCalculus.freeGroupPresentationBlanchfieldLyndonTailMap (H := H) r psi) ∧
      Function.Exact
        (FoxCalculus.freeGroupPresentationBlanchfieldLyndonTailMap (H := H) r psi)
        (augmentation H) ∧
      Function.Surjective (augmentation H) := by
  let := kernelAbelianizationModuleOfSurjective psi hpsi
  let e : DifferentialModule psi ≃ₗ[GroupRing H] (Fin r → GroupRing H) :=
    FoxCalculus.freeGroupPresentationMiddleCoordinateEquiv (H := H) r psi
  let generators : Fin r → GroupRing H :=
    FoxCalculus.freeGroupPresentationAugmentationGenerators (H := H) r psi
  change
    Function.Injective
        (e.toLinearMap.comp
          (kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi)) ∧
      Function.Exact
        (e.toLinearMap.comp
          (kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi))
        (blanchfieldLyndonFiniteFamilyMap (R := GroupRing H) generators) ∧
      Function.Exact
        (blanchfieldLyndonFiniteFamilyMap (R := GroupRing H) generators)
        (augmentation H) ∧
      Function.Surjective (augmentation H)
  have hfox :
      blanchfieldLyndonFiniteFamilyMap (R := GroupRing H) generators =
        (toGroupRing psi).comp e.symm.toLinearMap := by
    change
      FoxCalculus.freeGroupPresentationBlanchfieldLyndonTailMap (H := H) r psi =
        (toGroupRing psi).comp
          (FoxDifferential.FoxCalculus.relativeFreeFoxCoordinatesLinearMap
            (H := H) (Fin r) psi)
    rw [FoxDifferential.FoxCalculus.toGroupRing_comp_relativeFreeFoxCoordinatesLinearMap]
    apply LinearMap.ext
    intro a
    rw [FoxCalculus.freeGroupPresentationBlanchfieldLyndonTailMap_apply]
    simp only [augmentationGenerator_eq_groupRingBoundary, FoxCalculus.relativeFreeGroupFoxBoundary,
  LinearMap.coe_mk, AddHom.coe_mk]
  have htoAug_exact :
      Function.Exact
        (e.toLinearMap.comp
          (kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi))
        ((toAugmentationIdeal (H := H) psi).comp e.symm.toLinearMap) := by
    exact
      (LinearEquiv.conj_exact_iff_exact
        (f := kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi)
        (g := toAugmentationIdeal (H := H) psi) e).2
        (exact_kernelAbelianizationBoundaryLinearOfSurjective_toAugmentationIdeal
          (H := H) psi hpsi)
  have hfree_inj :
      Function.Injective
        (e.toLinearMap.comp
          (kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi)) := by
    intro x y hxy
    apply FoxDifferential.kernelAbelianizationBoundaryLinearOfSurjective_injective
      (H := H) (ψ := psi) hpsi
    exact e.injective hxy
  refine ⟨hfree_inj, ?_, ?_, augmentation_surjective (H := H)⟩
  · rw [hfox, ← subtype_comp_toAugmentationIdeal (H := H) psi]
    exact
      (Function.Injective.comp_exact_iff_exact
        (R := GroupRing H) ((augmentationIdeal H).subtype_injective)).2
        htoAug_exact
  · rw [hfox]
    intro z
    constructor
    · intro hz
      rcases (exact_toGroupRing_augmentation (H := H) psi hpsi z).1 hz with ⟨x, hx⟩
      rcases e.symm.surjective x with ⟨y, rfl⟩
      exact ⟨y, hx⟩
    · rintro ⟨y, rfl⟩
      exact augmentation_toGroupRing_eq_zero (H := H) psi (e.symm y)

end Morishita2024

end

end CrowellExactSequence
