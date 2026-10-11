/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CrowellExactSequence.Basic
import Nyll.ProCGroups.FoxDifferential.Discrete.KernelBoundary.Quotient
import Nyll.ProCGroups.FoxDifferential.Discrete.KernelBoundary.MagnusKernel
import Nyll.ProCGroups.FoxDifferential.Discrete.FoxCalculus.Coordinates

/-!
# Discrete Crowell sequence maps

This file constructs the maps in the discrete presentation sequence: the middle coordinate
equivalence, the augmentation-generator tail map, and the relative-derivative head map. It also
records their formulas on free generators.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential

namespace FoxCalculus

variable {H : Type} [Group H]

/--
For a finite free presentation \(\psi:F_r\to H\), the Crowell middle term is identified with
the explicit module of relative Fox coordinates.
-/
def freeGroupPresentationMiddleCoordinateEquiv
    (r : Nat) (ψ : FreeGroup (Fin r) →* H) :
    DifferentialModule ψ ≃ₗ[GroupRing H] (Fin r → GroupRing H) :=
  (FoxDifferential.FoxCalculus.relativeFreeFoxCoordinatesLinearEquivDifferential
    (H := H) (Fin r) ψ).symm

/-- The concrete BL tail generators \(\psi(x_i)-1\) for a finite free presentation. -/
def freeGroupPresentationAugmentationGenerators
    (r : Nat) (ψ : FreeGroup (Fin r) →* H) : Fin r → GroupRing H :=
  fun i => augmentationGenerator H (ψ (FreeGroup.of i))

/-- The concrete Blanchfield--Lyndon tail map in relative Fox coordinates. -/
def freeGroupPresentationBlanchfieldLyndonTailMap
    (r : Nat) (ψ : FreeGroup (Fin r) →* H) :
    (Fin r → GroupRing H) →ₗ[GroupRing H] GroupRing H :=
  blanchfieldLyndonFiniteFamilyMap
    (R := GroupRing H)
    (freeGroupPresentationAugmentationGenerators (H := H) r ψ)

/--
The discrete Blanchfield--Lyndon tail map is evaluated on the canonical generators and then
extended linearly to the coordinate module.
-/
theorem freeGroupPresentationBlanchfieldLyndonTailMap_apply
    (r : Nat) (ψ : FreeGroup (Fin r) →* H) (a : Fin r → GroupRing H) :
    freeGroupPresentationBlanchfieldLyndonTailMap (H := H) r ψ a =
      ∑ i : Fin r, a i * augmentationGenerator H (ψ (FreeGroup.of i)) := by
  rw [freeGroupPresentationBlanchfieldLyndonTailMap, blanchfieldLyndonFiniteFamilyMap_apply]
  simp only [freeGroupPresentationAugmentationGenerators,
    augmentationGenerator_eq_groupRingBoundary, smul_eq_mul]

/-- The concrete BL head map: the Crowell head map written in relative Fox coordinates. -/
def freeGroupPresentationRelativeDerivativeHeadMap
    (r : Nat) (ψ : FreeGroup (Fin r) →* H) (hψ : Function.Surjective ψ) :
    letI := kernelAbelianizationModuleOfSurjective ψ hψ
    KernelAbelianizationAdd ψ →ₗ[GroupRing H] (Fin r → GroupRing H) := by
  letI := kernelAbelianizationModuleOfSurjective ψ hψ
  exact
    (freeGroupPresentationMiddleCoordinateEquiv (H := H) r ψ).toLinearMap.comp
      (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ)

/-- On a kernel element, the concrete BL head map is the relative Fox derivative vector. -/
theorem freeGroupPresentationRelativeDerivativeHeadMap_of
    (r : Nat) (ψ : FreeGroup (Fin r) →* H) (hψ : Function.Surjective ψ)
    (n : ψ.ker) :
    letI := kernelAbelianizationModuleOfSurjective ψ hψ
    freeGroupPresentationRelativeDerivativeHeadMap (H := H) r ψ hψ
        (Additive.ofMul (Abelianization.of n)) =
      FoxDifferential.FoxCalculus.relativeFreeGroupFoxDerivative (H := H) (Fin r) ψ n.1 := by
  let := kernelAbelianizationModuleOfSurjective ψ hψ
  change
    (freeGroupPresentationMiddleCoordinateEquiv (H := H) r ψ).toLinearMap
        (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ
          (Additive.ofMul (Abelianization.of n))) =
      FoxDifferential.FoxCalculus.relativeFreeGroupFoxDerivative (H := H) (Fin r) ψ n.1
  rw [kernelAbelianizationBoundaryLinearOfSurjective_of]
  change
    FoxDifferential.FoxCalculus.relativeDifferentialToFreeFoxCoordinates
        (H := H) (Fin r) ψ (universalDifferential ψ n.1) =
      FoxDifferential.FoxCalculus.relativeFreeGroupFoxDerivative (H := H) (Fin r) ψ n.1
  exact FoxDifferential.FoxCalculus.relativeDifferentialToFreeFoxCoordinates_d
    (H := H) (Fin r) ψ n.1

end FoxCalculus

end

end CrowellExactSequence
