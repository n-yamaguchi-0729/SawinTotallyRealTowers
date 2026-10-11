/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.NormalizationAutomorphismSurjectivity
import Nyll.SchemeTheory.Normalization.AmbientNormalizationGroupMap

/-!
# Surjectivity of native normalization automorphisms

Every intrinsic coefficient automorphism is induced by an automorphism of
the finite fraction-field extension.
-/

noncomputable section

namespace SchemeTheory

universe u v w

/-- The prescribed native finite normalization group map is onto the
intrinsic coefficient automorphism group. The actual fraction-extension
producer constructs its preimages. -/
theorem normalizationGaloisGroupMap_surjective
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K F] [Algebra A F] [IsScalarTower A K F]
    [FiniteDimensional K F] :
    Function.Surjective (normalizationGaloisGroupMap A K F).hom := by
  change Function.Surjective
    (fun σ : F ≃ₐ[K] F => (σ.restrictScalars A).mapIntegralClosure)
  exact integralClosure_restrictScalars_surjective A K F

end SchemeTheory
