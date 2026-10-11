/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Affinization commutes with flat affine base change

The qcqs theorem on sections gives an actual pushout square of global
sections. Applying `Spec` and cancelling the affine base square proves
that the canonical affinization map commutes with the given base change.
-/


noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X S T : Scheme.{u}} (f : X ⟶ S) (g : T ⟶ S)
variable [IsAffine S] [IsAffine T] [QuasiCompact f] [QuasiSeparated f] [Flat g]

/-- The actual maps on global sections form a pushout after flat affine
base change of a qcqs morphism. -/
theorem isPushout_appTop_of_flat :
    IsPushout f.appTop g.appTop (pullback.fst f g).appTop
      (pullback.snd f g).appTop := by
  have hX : IsCompact (⊤ : X.Opens).1 :=
    f.isCompact_preimage (isAffineOpen_top S).isCompact
  have hX' : IsQuasiSeparated (⊤ : X.Opens).1 :=
    f.isQuasiSeparated_preimage (isAffineOpen_top S).isQuasiSeparated
  have hTop : (⊤ : (pullback f g).Opens) =
      pullback.fst f g ⁻¹ᵁ ⊤ ⊓ pullback.snd f g ⁻¹ᵁ ⊤ := by
    rw [Scheme.Hom.preimage_top, Scheme.Hom.preimage_top, inf_top_eq]
  have h := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback f g) (show (⊤ : T.Opens) ≤ g ⁻¹ᵁ ⊤ from le_top)
    (show (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ from le_top) hTop
    (isAffineOpen_top S) (isAffineOpen_top T) hX hX'
  have hp := (isIso_pushoutSection_iff (IsPullback.of_hasPullback f g)
    (show (⊤ : T.Opens) ≤ g ⁻¹ᵁ ⊤ from le_top)
    (show (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤ from le_top) hTop).mp h
  have hf : f.appTop = f.appLE ⊤ ⊤ le_top := f.app_eq_appLE
  have hg : g.appTop = g.appLE ⊤ ⊤ le_top := g.app_eq_appLE
  have hl : (pullback.fst f g).appTop =
      (pullback.fst f g).appLE ⊤ ⊤ le_top := (pullback.fst f g).app_eq_appLE
  have hr : (pullback.snd f g).appTop =
      (pullback.snd f g).appLE ⊤ ⊤ le_top := (pullback.snd f g).app_eq_appLE
  rw [hf, hg, hl, hr]
  exact hp

/-- The canonical affinization morphism is compatible with flat affine
base change, as an actual cartesian square. -/
theorem isPullback_toSpecΓ_of_flat :
    IsPullback (pullback f g).toSpecΓ (pullback.fst f g)
      (Spec.map (pullback.fst f g).appTop) X.toSpecΓ := by
  have hSpec := isPullback_SpecMap_of_isPushout f.appTop g.appTop
    (pullback.fst f g).appTop (pullback.snd f g).appTop
    (isPushout_appTop_of_flat f g)
  have hOuter : IsPullback
      ((pullback f g).toSpecΓ ≫ Spec.map (pullback.snd f g).appTop)
      (pullback.fst f g) (Spec.map g.appTop) (X.toSpecΓ ≫ Spec.map f.appTop) := by
    refine (IsPullback.of_hasPullback f g).flip.of_iso
      (Iso.refl _) T.isoSpec (Iso.refl _) S.isoSpec ?_ ?_ ?_ ?_
    · change pullback.snd f g ≫ T.toSpecΓ =
        𝟙 _ ≫ ((pullback f g).toSpecΓ ≫ Spec.map (pullback.snd f g).appTop)
      rw [Category.id_comp]
      exact Scheme.toSpecΓ_naturality (pullback.snd f g)
    · exact (Category.comp_id _).trans (Category.id_comp _).symm
    · exact Scheme.toSpecΓ_naturality g
    · change f ≫ S.toSpecΓ = 𝟙 _ ≫ (X.toSpecΓ ≫ Spec.map f.appTop)
      rw [Category.id_comp]
      exact Scheme.toSpecΓ_naturality f
  exact hOuter.of_right (Scheme.toSpecΓ_naturality (pullback.fst f g)).symm hSpec.flip

end AlgebraicGeometry
