/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.IntegralFinitePresentationColimit
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.FinitePresentation


/-!
# Affine integral morphisms as limits of finite-FP schemes

Apply the native `Spec` limit-preservation theorem to the actual small
finite-FP ring-model colimit. The resulting scheme diagram has its genuine
maps to the original affine base, with finite and locally finitely presented
stage maps and the actual limit cone. Surjectivity of the original morphism
implies surjectivity of each stage map by the proved factorization.

The existing finitely generated subalgebra limit family uses inclusion maps
and does not supply arbitrary-base finite presentation. Here the finite-FP
model diagram is used directly; no global relative-Spec or gluing comparison
is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite Algebra

namespace AlgebraicGeometry.AffineIntegralLimit

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- The actual cofiltered affine scheme diagram dual to the small ring diagram. -/
def diagram : (FinitePresentationModel R B)ᵒᵖ ⥤ Scheme.{u} :=
  (FinitePresentationModel.ringDiagram R B).op ⋙ Scheme.Spec

/-- The actual cone with vertex `Spec B`. -/
def cone : Cone (diagram R B) :=
  Scheme.Spec.mapCone (FinitePresentationModel.ringCocone R B).op

/-- Native `Spec` preservation turns the proved ring colimit into a scheme limit. -/
def coneIsLimit [Algebra.IsIntegral R B] : IsLimit (cone R B) :=
  isLimitOfPreserves Scheme.Spec (FinitePresentationModel.ringCoconeIsColimit R B).op

/-- The algebra structure maps give the diagram's morphism to the original base. -/
def baseMap : diagram R B ⟶
    (Functor.const (FinitePresentationModel R B)ᵒᵖ).obj (Spec (CommRingCat.of R)) where
  app i := Spec.map (CommRingCat.ofHom (algebraMap R i.unop.stage))
  naturality i j f := by
    let α : j.unop.presentation.eval.obj →ₐ[R] i.unop.presentation.eval.obj :=
      f.unop.hom.left.hom
    change Spec.map (CommRingCat.ofHom α.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R j.unop.stage)) =
      Spec.map (CommRingCat.ofHom (algebraMap R i.unop.stage)) ≫ 𝟙 _
    rw [Category.comp_id, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    exact congrArg (fun ψ : R →+* i.unop.stage => Spec.map (CommRingCat.ofHom ψ))
      α.comp_algebraMap

/-- Each cone projection is an actual factorization of the original affine morphism. -/
theorem projection_comp_base (i : (FinitePresentationModel R B)ᵒᵖ) :
    (cone R B).π.app i ≫ (baseMap R B).app i =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  let η : i.unop.presentation.eval.obj →ₐ[R] B := i.unop.map
  change Spec.map (CommRingCat.ofHom η.toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R i.unop.stage)) =
    Spec.map (CommRingCat.ofHom (algebraMap R B))
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun ψ : R →+* B => Spec.map (CommRingCat.ofHom ψ)) η.comp_algebraMap

/-- The factorization holds for the complete cone morphism over the base. -/
theorem cone_π_comp_baseMap :
    (cone R B).π ≫ baseMap R B =
      (Functor.const (FinitePresentationModel R B)ᵒᵖ).map
        (Spec.map (CommRingCat.ofHom (algebraMap R B))) := by
  apply NatTrans.ext
  funext i
  exact projection_comp_base R B i

instance (i : (FinitePresentationModel R B)ᵒᵖ) : IsAffine ((diagram R B).obj i) :=
  inferInstanceAs (IsAffine (Spec _))

instance {i j : (FinitePresentationModel R B)ᵒᵖ} (f : i ⟶ j) :
    IsAffineHom ((diagram R B).map f) :=
  isAffineHom_of_isAffine _

/-- Every actual stage morphism is finite over the original base. -/
instance (i : (FinitePresentationModel R B)ᵒᵖ) : IsFinite ((baseMap R B).app i) := by
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R i.unop.stage)))
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr i.unop.finite)

/-- Every stage morphism is locally of finite presentation; together with
finiteness this gives a finite morphism of finite presentation. -/
instance (i : (FinitePresentationModel R B)ᵒᵖ) :
    LocallyOfFinitePresentation ((baseMap R B).app i) := by
  change LocallyOfFinitePresentation
    (Spec.map (CommRingCat.ofHom (algebraMap R i.unop.stage)))
  exact (LocallyOfFinitePresentation.SpecMap_iff _).mpr
    (RingHom.finitePresentation_algebraMap.mpr i.unop.finitePresentation)

/-- Surjectivity of the original affine morphism descends to every stage map. -/
instance [hSurj : Surjective (Spec.map (CommRingCat.ofHom (algebraMap R B)))]
    (i : (FinitePresentationModel R B)ᵒᵖ) : Surjective ((baseMap R B).app i) := by
  have : Surjective ((cone R B).π.app i ≫ (baseMap R B).app i) := by
    rw [projection_comp_base]
    exact hSurj
  exact Surjective.of_comp ((cone R B).π.app i) ((baseMap R B).app i)

end AlgebraicGeometry.AffineIntegralLimit
