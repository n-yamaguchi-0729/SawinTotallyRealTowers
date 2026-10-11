/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Descent.FinitePresentation
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Flat.Tensor
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Flat


/-!
# Étaleness descends through a faithfully flat étale source cover

For a tower R → A → B, faithful flatness of A → B reflects the ideal
injectivity criterion for flatness. The existing iterated-base-change
identity supplies the comparison, without any new tensor construction.

If both R → B and A → B are étale, the existing differential equivalence
reflects formal unramifiedness to R → A. Source-side finite-presentation
descent supplies the remaining finite-presentation condition, so R → A is
genuinely étale.
-/

open scoped TensorProduct

namespace SchemeTheory

universe u v w

variable (R : Type u) (A : Type v) (B : Type w)
  [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Flatness descends through a faithfully flat source extension. -/
theorem flat_of_faithfullyFlat_of_flat
    [Module.FaithfullyFlat A B] [Module.Flat R B] : Module.Flat R A := by
  apply (Module.Flat.iff_lTensor_injective').mpr
  intro I
  change Function.Injective (I.subtype.baseChange A)
  apply (Module.FaithfullyFlat.lTensor_injective_iff_injective A B (I.subtype.baseChange A)).mp
  change Function.Injective ((I.subtype.baseChange A).baseChange B)
  rw [LinearMap.baseChange_baseChange]
  have hB : Function.Injective (I.subtype.baseChange B) :=
    Module.Flat.lTensor_preserves_injective_linearMap I.subtype I.subtype_injective
  exact (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B R).symm.injective.comp
    (hB.comp (TensorProduct.AlgebraTensorModule.cancelBaseChange R A B B I).injective)

/-- A faithfully flat étale source cover detects genuine étaleness of the
original algebra. Both finite-presentation inputs come from the two given
étale maps and are descended by the existing source-side owner. -/
theorem etale_of_faithfullyFlat_of_etale
    [Module.FaithfullyFlat A B] [Algebra.Etale A B] [Algebra.Etale R B] :
    Algebra.Etale R A := by
  have : Module.Flat R A := flat_of_faithfullyFlat_of_flat R A B
  have : Subsingleton (B ⊗[A] Ω[A⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B).subsingleton
  have : Subsingleton Ω[A⁄R] :=
    Module.FaithfullyFlat.lTensor_reflects_triviality A B Ω[A⁄R]
  have : Algebra.FormallyUnramified R A := ⟨inferInstance⟩
  have : Algebra.FinitePresentation R A :=
    Algebra.FinitePresentation.of_faithfullyFlat_of_finitePresentation R A B
  exact Algebra.Etale.of_formallyUnramified_of_flat

end SchemeTheory
