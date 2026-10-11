/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.NormalizationAutomorphismGroupMap
import Nyll.SchemeTheory.Normalization.ScalarRestrictionGroupMap
import Nyll.SchemeTheory.Normalization.NativeAutomorphismRingMaps

/-!
# Ambient field automorphisms on normalizations

Constructs the action of ambient field automorphisms on the normalization by restriction of
scalars and integral-closure functoriality. The induced ring maps commute with the inclusion
into the ambient field.
-/

noncomputable section

namespace SchemeTheory

open CategoryTheory

universe u v w

variable (A : Type u) (K : Type v) (L : Type w)
  [CommRing A] [Field K] [Field L] [Algebra A K]
  [Algebra K L] [Algebra A L] [IsScalarTower A K L]

/-- The original ambient field automorphisms act on its actual normalization. -/
def normalizationGaloisGroupMap :
    GrpCat.Hom (galoisGroupObject K L)
      (commAlgAutomorphismGroup A (normalizationCommAlgCat A L)) where
  hom' := (normalizationAutomorphismGroupMap A (CommAlgCat.of A L)).hom'.comp
    (scalarRestrictionGroupMap A K (CommAlgCat.of A L)).hom'

/-- The individual original normalization action as its actual ring map. -/
def normalizationGaloisRingHom (σ : Gal(L/K)) :
    (normalizationCommAlgCat A L).carrier →+* (normalizationCommAlgCat A L).carrier :=
  commAlgAutomorphismRingHom A (normalizationCommAlgCat A L)
    ((normalizationGaloisGroupMap A K L).hom'.toFun σ)

/-- Normalization functoriality gives the actual ambient coefficient square. -/
theorem normalizationGaloisRingHom_commutes (σ : Gal(L/K)) :
    (normalizationAmbientRingHom A (CommAlgCat.of A L)).comp (normalizationGaloisRingHom A K L σ) =
      (galoisAutomorphismRingHom K L σ).comp
        (normalizationAmbientRingHom A (CommAlgCat.of A L)) := rfl

end SchemeTheory

end
