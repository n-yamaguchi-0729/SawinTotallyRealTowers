/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.CategoryTheory.Limits.Cones

/-!
# Actual scheme-theoretic image diagrams

A map into the vertex of a scheme cone gives compatible scheme-theoretic
images at every stage. The image transition maps are constructed by the
closed-immersion kernel factorization, and preserve affine transitions.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AffineTransitionImage

universe u

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  {Z : Scheme.{u}} (j : Z ⟶ c.pt)

/-- The scheme-theoretic image at the specified ambient stage. -/
abbrev stage (i : I) : Scheme.{u} := (j ≫ c.π.app i).image

/-- The actual image inclusion into the ambient stage. -/
abbrev inclusion (i : I) : stage D c j i ⟶ D.obj i := (j ≫ c.π.app i).imageι

private lemma transition_kernel {i k : I} (f : i ⟶ k) :
    (inclusion D c j k).ker ≤ (inclusion D c j i ≫ D.map f).ker := by
  change (j ≫ c.π.app k).ker.subschemeι.ker ≤
    ((j ≫ c.π.app i).ker.subschemeι ≫ D.map f).ker
  rw [Scheme.Hom.ker_comp ((j ≫ c.π.app i).ker.subschemeι) (D.map f),
    Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.ker_subschemeι,
    ← Scheme.Hom.ker_comp (j ≫ c.π.app i) (D.map f), Category.assoc, c.w f]

/-- The transition morphism is the unique factorization through the next image. -/
def transition {i k : I} (f : i ⟶ k) : stage D c j i ⟶ stage D c j k :=
  IsClosedImmersion.lift (inclusion D c j k) (inclusion D c j i ≫ D.map f)
    (transition_kernel D c j f)

@[reassoc]
lemma transition_inclusion {i k : I} (f : i ⟶ k) :
    transition D c j f ≫ inclusion D c j k = inclusion D c j i ≫ D.map f :=
  IsClosedImmersion.lift_fac _ _ _

/-- The actual functor of scheme-theoretic images. -/
@[reducible]
def diagram : I ⥤ Scheme.{u} where
  obj i := stage D c j i
  map f := transition D c j f
  map_id i := by
    apply (cancel_mono (inclusion D c j i)).mp
    rw [transition_inclusion, D.map_id, Category.comp_id, Category.id_comp]
  map_comp f g := by
    apply (cancel_mono (inclusion D c j _)).mp
    rw [transition_inclusion, Category.assoc, transition_inclusion,
      ← Category.assoc, transition_inclusion, D.map_comp, Category.assoc]

/-- The image diagram has its actual closed inclusions into the ambient diagram. -/
def inclusions : diagram D c j ⟶ D where
  app i := inclusion D c j i
  naturality _ _ f := transition_inclusion D c j f

/-- The original source maps to every image through the canonical image factor. -/
@[reducible]
def cone : Cone (diagram D c j) where
  pt := Z
  π.app i := (j ≫ c.π.app i).toImage
  π.naturality i k f := by
    change 𝟙 Z ≫ (j ≫ c.π.app k).toImage =
      (j ≫ c.π.app i).toImage ≫ transition D c j f
    rw [Category.id_comp]
    apply (cancel_mono (inclusion D c j k)).mp
    rw [Category.assoc, transition_inclusion, ← Category.assoc,
      Scheme.Hom.toImage_imageι, Scheme.Hom.toImage_imageι, Category.assoc, c.w f]

@[reassoc]
lemma cone_projection_inclusion (i : I) :
    (cone D c j).π.app i ≫ inclusion D c j i = j ≫ c.π.app i :=
  Scheme.Hom.toImage_imageι _

/-- Affine ambient transitions induce affine transitions of the actual images. -/
instance {i k : I} (f : i ⟶ k) [IsAffineHom (D.map f)] :
    IsAffineHom ((diagram D c j).map f) := by
  change IsAffineHom (transition D c j f)
  have : IsAffineHom (transition D c j f ≫ inclusion D c j k) := by
    rw [transition_inclusion]
    infer_instance
  exact IsAffineHom.of_comp (transition D c j f) (inclusion D c j k)

end AlgebraicGeometry.AffineTransitionImage
