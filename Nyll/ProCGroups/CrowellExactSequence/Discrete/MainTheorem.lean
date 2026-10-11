/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.CrowellExactSequence.Discrete.Exactness

/-!
# Crowell Exact Sequence / Discrete / Main Theorem

This module develops the Crowell--Blanchfield--Lyndon exact sequence and its completed
coordinate forms.
-/

namespace CrowellExactSequence

noncomputable section

open FoxDifferential

variable {H : Type} [Group H]

/-- The discrete Crowell sequence for a surjective group homomorphism.  All three displayed
maps are bundled as `ℤ`-linear maps so that the source, group-ring, and augmentation terms live
in one canonical `FourTermLinearSequence`. -/
def discreteCrowellLinearSequence
    {G : Type} [Group G]
    (psi : MonoidHom G H) (hpsi : Function.Surjective psi) :
    letI := kernelAbelianizationModuleOfSurjective psi hpsi
    FourTermLinearSequence ℤ
      (KernelAbelianizationAdd psi) (DifferentialModule psi) (GroupRing H) ℤ := by
  letI := kernelAbelianizationModuleOfSurjective psi hpsi
  refine FourTermLinearSequence.ofExact
    ((kernelAbelianizationBoundaryLinearOfSurjective
      (H := H) psi hpsi).toAddMonoidHom.toIntLinearMap)
    ((toGroupRing psi).toAddMonoidHom.toIntLinearMap)
    ((augmentation H).toAddMonoidHom.toIntLinearMap) ?_
  rcases Morishita2024.crowellExactSequence_of_surjective (H := H) psi hpsi with
    ⟨hinj, hhead, hmiddle, hsurj⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    change kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi x =
      kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi y at hxy
    exact hinj hxy
  · intro y
    change toGroupRing psi y = 0 ↔
      ∃ x, kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi x = y
    exact hhead y
  · intro y
    change augmentation H y = 0 ↔ ∃ x, toGroupRing psi x = y
    exact hmiddle y
  · intro z
    rcases hsurj z with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change augmentation H y = z
    exact hy

/--
The discrete Crowell exact sequence for a surjective group homomorphism, packaged as the full
four-term exact sequence \((\ker \psi)^{\mathrm{ab}} \to A_{\psi} \to \mathbb{Z}[H] \to
\mathbb{Z}\).
-/
@[simp]
theorem discreteCrowellLinearSequence_isExact
    {G : Type} [Group G]
    (psi : MonoidHom G H) (hpsi : Function.Surjective psi) :
    letI := kernelAbelianizationModuleOfSurjective psi hpsi
    (discreteCrowellLinearSequence (H := H) psi hpsi).IsExact := by
  let := kernelAbelianizationModuleOfSurjective psi hpsi
  unfold FourTermLinearSequence.IsExact
  rcases Morishita2024.crowellExactSequence_of_surjective (H := H) psi hpsi with
    ⟨hinj, hhead, hmiddle, hsurj⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    change kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi x =
      kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi y at hxy
    exact hinj hxy
  · intro y
    change toGroupRing psi y = 0 ↔
      ∃ x, kernelAbelianizationBoundaryLinearOfSurjective (H := H) psi hpsi x = y
    exact hhead y
  · intro y
    change augmentation H y = 0 ↔ ∃ x, toGroupRing psi x = y
    exact hmiddle y
  · intro z
    rcases hsurj z with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change augmentation H y = z
    exact hy

/-- The discrete Blanchfield--Lyndon sequence in concrete `Fin r` coordinates. -/
def discreteBlanchfieldLyndonLinearSequence
    (r : Nat) (psi : MonoidHom (FreeGroup (Fin r)) H) (hpsi : Function.Surjective psi) :
    letI := kernelAbelianizationModuleOfSurjective psi hpsi
    FourTermLinearSequence ℤ
      (KernelAbelianizationAdd psi) (Fin r → GroupRing H) (GroupRing H) ℤ := by
  letI := kernelAbelianizationModuleOfSurjective psi hpsi
  refine FourTermLinearSequence.ofExact
    ((FoxCalculus.freeGroupPresentationRelativeDerivativeHeadMap
      (H := H) r psi hpsi).toAddMonoidHom.toIntLinearMap)
    ((FoxCalculus.freeGroupPresentationBlanchfieldLyndonTailMap
      (H := H) r psi).toAddMonoidHom.toIntLinearMap)
    ((augmentation H).toAddMonoidHom.toIntLinearMap) ?_
  rcases
      Morishita2024.freeGroupPresentation_blanchfieldLyndonExactSequence
        (H := H) r psi hpsi with
    ⟨hinj, hhead, hmiddle, hsurj⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    change
      FoxCalculus.freeGroupPresentationRelativeDerivativeHeadMap
          (H := H) r psi hpsi x =
        FoxCalculus.freeGroupPresentationRelativeDerivativeHeadMap
          (H := H) r psi hpsi y at hxy
    exact hinj hxy
  · intro y
    change
      FoxCalculus.freeGroupPresentationBlanchfieldLyndonTailMap
          (H := H) r psi y = 0 ↔
        ∃ x,
          FoxCalculus.freeGroupPresentationRelativeDerivativeHeadMap
            (H := H) r psi hpsi x = y
    exact hhead y
  · intro y
    change augmentation H y = 0 ↔
      ∃ x,
        FoxCalculus.freeGroupPresentationBlanchfieldLyndonTailMap
          (H := H) r psi x = y
    exact hmiddle y
  · intro z
    rcases hsurj z with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change augmentation H y = z
    exact hy

/--
The discrete Blanchfield--Lyndon coordinate exact sequence for a finite free presentation,
packaged as the full four-term exact sequence.
-/
@[simp]
theorem discreteBlanchfieldLyndonLinearSequence_isExact
    (r : Nat) (psi : MonoidHom (FreeGroup (Fin r)) H) (hpsi : Function.Surjective psi) :
    letI := kernelAbelianizationModuleOfSurjective psi hpsi
    (discreteBlanchfieldLyndonLinearSequence (H := H) r psi hpsi).IsExact := by
  let := kernelAbelianizationModuleOfSurjective psi hpsi
  unfold FourTermLinearSequence.IsExact
  rcases
      Morishita2024.freeGroupPresentation_blanchfieldLyndonExactSequence
        (H := H) r psi hpsi with
    ⟨hinj, hhead, hmiddle, hsurj⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y hxy
    change
      FoxCalculus.freeGroupPresentationRelativeDerivativeHeadMap
          (H := H) r psi hpsi x =
        FoxCalculus.freeGroupPresentationRelativeDerivativeHeadMap
          (H := H) r psi hpsi y at hxy
    exact hinj hxy
  · intro y
    change
      FoxCalculus.freeGroupPresentationBlanchfieldLyndonTailMap
          (H := H) r psi y = 0 ↔
        ∃ x,
          FoxCalculus.freeGroupPresentationRelativeDerivativeHeadMap
            (H := H) r psi hpsi x = y
    exact hhead y
  · intro y
    change augmentation H y = 0 ↔
      ∃ x,
        FoxCalculus.freeGroupPresentationBlanchfieldLyndonTailMap
          (H := H) r psi x = y
    exact hmiddle y
  · intro z
    rcases hsurj z with ⟨y, hy⟩
    refine ⟨y, ?_⟩
    change augmentation H y = z
    exact hy

end

end CrowellExactSequence
