/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.LocalProperties.Submodule
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Smooth.Fiber

/-!
# Étaleness of a finite-projective algebra from base localizations

The differentials vanish after every maximal localization of the base,
because the actual tensor algebra there is étale. Localization detects
vanishing, and finite projectivity supplies flatness and finite presentation.
-/

noncomputable section

open scoped TensorProduct

namespace Algebra

universe u v

/-- A finite-projective algebra is étale if its actual base changes to
all maximal localizations of the base ring are étale. -/
theorem etale_of_finite_projective_of_etale_localizations
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [Module.Finite R B] [Module.Projective R B]
    (hLocal : ∀ (p : Ideal R) [p.IsMaximal],
      Etale (Localization.AtPrime p) (Localization.AtPrime p ⊗[R] B)) :
    Etale R B := by
  have hDifferentials : Subsingleton Ω[B⁄R] := by
    apply Module.subsingleton_of_localization_maximal
      (fun (p : Ideal R) (_ : p.IsMaximal) => LocalizedModule p.primeCompl Ω[B⁄R])
      (fun (p : Ideal R) (_ : p.IsMaximal) =>
        LocalizedModule.mkLinearMap p.primeCompl Ω[B⁄R])
    intro p hp
    let : Algebra B (Localization.AtPrime p ⊗[R] B) := Algebra.TensorProduct.rightAlgebra
    have hEtale := hLocal p
    have hTensor : Subsingleton (Localization.AtPrime p ⊗[R] Ω[B⁄R]) :=
      (KaehlerDifferential.tensorKaehlerEquivBase R (Localization.AtPrime p) B
        (Localization.AtPrime p ⊗[R] B)).subsingleton
    exact (LocalizedModule.equivTensorProduct p.primeCompl Ω[B⁄R]).subsingleton
  have hUnramified : FormallyUnramified R B := ⟨hDifferentials⟩
  have hPresentation : Module.FinitePresentation R B :=
    Module.finitePresentation_of_projective R B
  exact Etale.of_formallyUnramified_of_flat

end Algebra
