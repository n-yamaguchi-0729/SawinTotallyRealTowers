/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.FlatBaseChangeAffinization
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Descent of an open affinization

The actual affinization square commutes with flat affine base change.
An open immersion after an affine fpqc base change therefore descends.
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
variable [IsAffine S] [IsAffine T] [QuasiCompact f] [QuasiSeparated f]
variable [Flat g] [Surjective g]

/-- The affine base-change map induced on global sections is fpqc. -/
theorem fpqc_SpecMap_pullback_fst_appTop :
    (show CategoryTheory.MorphismProperty Scheme.{u} from
      @Surjective ⊓ @Flat ⊓ @QuasiCompact) (Spec.map (pullback.fst f g).appTop) := by
  have hg : Flat (Spec.map g.appTop) ∧ Surjective (Spec.map g.appTop) :=
    (flat_and_surjective_SpecMap_iff g.appTop).mpr
      ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp
        ⟨inferInstance, inferInstance⟩)
  let : Flat (Spec.map g.appTop) := hg.1
  let : Surjective (Spec.map g.appTop) := hg.2
  have h := isPullback_SpecMap_of_isPushout f.appTop g.appTop
    (pullback.fst f g).appTop (pullback.snd f g).appTop
    (isPushout_appTop_of_flat f g)
  refine ⟨⟨?_, ?_⟩, inferInstance⟩
  · exact (show CategoryTheory.MorphismProperty Scheme.{u} from @Surjective).of_isPullback
      h.flip inferInstance
  · exact (show CategoryTheory.MorphismProperty Scheme.{u} from @Flat).of_isPullback
      h.flip inferInstance

/-- Being an open immersion for the canonical affinization is detected
after affine fpqc base change. -/
theorem isOpenImmersion_toSpecΓ_of_flat_baseChange
    [IsOpenImmersion (pullback f g).toSpecΓ] : IsOpenImmersion X.toSpecΓ := by
  exact CategoryTheory.MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsOpenImmersion) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
    (isPullback_toSpecΓ_of_flat f g) (fpqc_SpecMap_pullback_fst_appTop f g)
    inferInstance

end AlgebraicGeometry
