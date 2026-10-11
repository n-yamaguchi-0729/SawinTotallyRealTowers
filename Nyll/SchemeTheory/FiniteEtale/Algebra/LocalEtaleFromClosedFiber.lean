/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Smooth.Fiber

/-!
# Étaleness of a finite projective algebra over a local ring

Étaleness on the closed fibre kills the residue-field extension of the
finite module of differentials. Nakayama kills the original differentials.
Finite projectivity supplies flatness and finite presentation.
-/

noncomputable section

open scoped TensorProduct

namespace Algebra

universe u v

/-- A finite projective algebra over a local ring is étale when its
actual closed-fibre algebra is étale. No Noetherian hypothesis is needed. -/
theorem etale_of_finite_projective_of_etale_closedFiber
    (R : Type u) (B : Type v) [CommRing R] [IsLocalRing R] [CommRing B]
    [Algebra R B] [Module.Finite R B] [Module.Projective R B]
    [Etale (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] B)] :
    Etale R B := by
  let : Algebra B (IsLocalRing.ResidueField R ⊗[R] B) :=
    Algebra.TensorProduct.rightAlgebra
  have hFiniteDifferentials : Module.Finite R Ω[B⁄R] :=
    Module.Finite.trans B Ω[B⁄R]
  have hTensorDifferentials : Subsingleton (IsLocalRing.ResidueField R ⊗[R] Ω[B⁄R]) :=
    (KaehlerDifferential.tensorKaehlerEquivBase R (IsLocalRing.ResidueField R) B
      (IsLocalRing.ResidueField R ⊗[R] B)).subsingleton
  have hDifferentials : Subsingleton Ω[B⁄R] :=
    (IsLocalRing.subsingleton_tensorProduct (R := R) (M := Ω[B⁄R])).mp hTensorDifferentials
  have hUnramified : FormallyUnramified R B := ⟨hDifferentials⟩
  have hPresentation : Module.FinitePresentation R B :=
    Module.finitePresentation_of_projective R B
  exact Etale.of_formallyUnramified_of_flat

end Algebra
