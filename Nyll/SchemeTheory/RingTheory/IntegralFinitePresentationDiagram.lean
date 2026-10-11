/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.FinitePresentationCoequalizer
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.CommAlgCat.FiniteType
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.InducedCategory
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.TensorProduct.Maps


/-!
# A small filtered diagram of finite, finitely presented algebra models

The objects use the existing `FGAlgCatSkeleton`, whose presentation data
already lies in the base universe. Each object is an actual finite,
finitely presented algebra equipped with a map to the target algebra.
Morphisms and the diagram are inherited from the native over category.

Common stages use the existing tensor-product universal maps. Parallel
arrows are coequalized by the actual finite relation quotient. Thus the
index is filtered without assuming any colimit comparison. For an integral
target, proving that the displayed cocone is a colimit is the next step.
-/

noncomputable section

universe u

open CategoryTheory Limits
open scoped TensorProduct

namespace Algebra

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]

/-- Small presentation data for one finite-FP algebra model over `B`. -/
structure FinitePresentationModelData : Type u where
  /-- The finitely generated algebra presentation representing the model. -/
  presentation : FGAlgCatSkeleton R
  /-- The represented algebra is finite over the base ring. -/
  finite : Module.Finite R presentation.eval.obj
  /-- The represented algebra is finitely presented over the base ring. -/
  finitePresentation : Algebra.FinitePresentation R presentation.eval.obj
  /-- The base-algebra map from the represented model to the ambient algebra. -/
  map : presentation.eval.obj →ₐ[R] B

/-- The actual arrow represented by a small model. -/
def FinitePresentationModelData.toOver (M : FinitePresentationModelData R B) :
    Over (CommAlgCat.of R B) :=
  Over.mk (CommAlgCat.ofHom M.map)

/-- The model category has object type `Type u` and inherits its morphisms
from the ordinary over category. -/
abbrev FinitePresentationModel : Type u :=
  InducedCategory (Over (CommAlgCat.of R B))
    (FinitePresentationModelData.toOver R B)

namespace FinitePresentationModel

variable {R B}

/-- The represented finite-FP algebra. -/
abbrev stage (M : FinitePresentationModel R B) : CommAlgCat.{u} R :=
  M.presentation.eval.obj

/-- A model as its actual arrow to the target algebra. -/
abbrev toOver (M : FinitePresentationModel R B) : Over (CommAlgCat.of R B) :=
  FinitePresentationModelData.toOver R B M

/-- Every actual finite-FP stage has a representative in the small model category. -/
theorem exists_representation (A : CommAlgCat.{u} R)
    [Module.Finite R A] [Algebra.FinitePresentation R A] (φ : A →ₐ[R] B) :
    ∃ M : FinitePresentationModel R B,
      Nonempty (Over.mk (CommAlgCat.ofHom φ) ≅ M.toOver) := by
  obtain ⟨P, ⟨e⟩⟩ := Algebra.FiniteType.exists_fgAlgCatSkeleton R A
  have hfinite : Module.Finite R P.eval.obj := Module.Finite.equiv e.toLinearEquiv
  have hfp : Algebra.FinitePresentation R P.eval.obj := Algebra.FinitePresentation.equiv e
  let M : FinitePresentationModel R B := ⟨P, hfinite, hfp, φ.comp e.symm.toAlgHom⟩
  refine ⟨M, ⟨Over.isoMk (CommAlgCat.isoMk e) ?_⟩⟩
  apply CommAlgCat.hom_ext
  change (φ.comp e.symm.toAlgHom).comp e.toAlgHom = φ
  apply AlgHom.ext
  intro a
  exact congrArg φ (e.symm_apply_apply a)

private theorem common_stage (M N : FinitePresentationModel R B) :
    ∃ (K : FinitePresentationModel R B) (_ : M ⟶ K) (_ : N ⟶ K), True := by
  have : Module.Finite R M.stage := M.finite
  have : Module.Finite R N.stage := N.finite
  have : Algebra.FinitePresentation R M.stage := M.finitePresentation
  have : Algebra.FinitePresentation R N.stage := N.finitePresentation
  let T := M.stage ⊗[R] N.stage
  have : Module.Finite R T := inferInstance
  have : Algebra.FinitePresentation M.stage T := inferInstance
  have : Algebra.FinitePresentation R T := Algebra.FinitePresentation.trans R M.stage T
  let hcomm : ∀ x y, Commute (M.map x) (N.map y) := fun x y => Commute.all _ _
  let φ : T →ₐ[R] B := Algebra.TensorProduct.lift M.map N.map hcomm
  obtain ⟨K, ⟨e⟩⟩ := exists_representation (CommAlgCat.of R T) φ
  let i : M.toOver ⟶ Over.mk (CommAlgCat.ofHom φ) :=
    Over.homMk (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeLeft : M.stage →ₐ[R] T)) (by
        apply CommAlgCat.hom_ext
        exact Algebra.TensorProduct.lift_comp_includeLeft M.map N.map hcomm)
  let j : N.toOver ⟶ Over.mk (CommAlgCat.ofHom φ) :=
    Over.homMk (CommAlgCat.ofHom
      (Algebra.TensorProduct.includeRight : N.stage →ₐ[R] T)) (by
        apply CommAlgCat.hom_ext
        exact Algebra.TensorProduct.lift_comp_includeRight' M.map N.map hcomm)
  exact ⟨K, InducedCategory.homMk (i ≫ e.hom),
    InducedCategory.homMk (j ≫ e.hom), trivial⟩

private theorem coequalize {M N : FinitePresentationModel R B} (f g : M ⟶ N) :
    ∃ (K : FinitePresentationModel R B) (h : N ⟶ K), f ≫ h = g ≫ h := by
  have : Module.Finite R M.stage := M.finite
  have : Module.Finite R N.stage := N.finite
  have : Algebra.FinitePresentation R N.stage := N.finitePresentation
  let α : M.presentation.eval.obj →ₐ[R] N.presentation.eval.obj := f.hom.left.hom
  let β : M.presentation.eval.obj →ₐ[R] N.presentation.eval.obj := g.hom.left.hom
  let η : N.presentation.eval.obj →ₐ[R] B := N.map
  have hf : η.comp α = M.map := congrArg CommAlgCat.Hom.hom (Over.w f.hom)
  have hg : η.comp β = M.map := congrArg CommAlgCat.Hom.hom (Over.w g.hom)
  obtain ⟨Q, hfinite, hfp, q, ψ, _, hψ, hq⟩ :=
    AlgHom.exists_finitePresentation_coequalizer.{u, u, u} R
      (M.presentation.eval.obj : Type u) (N.presentation.eval.obj : Type u) B
      α β η (hf.trans hg.symm)
  have : Module.Finite R Q := hfinite
  have : Algebra.FinitePresentation R Q := hfp
  obtain ⟨K, ⟨e⟩⟩ := exists_representation Q ψ
  let a : N.toOver ⟶ Over.mk (CommAlgCat.ofHom ψ) :=
    Over.homMk (CommAlgCat.ofHom q) (by
      apply CommAlgCat.hom_ext
      exact hψ)
  have hfg : f.hom ≫ a = g.hom ≫ a := by
    apply Over.OverMorphism.ext
    apply CommAlgCat.hom_ext
    exact hq
  refine ⟨K, InducedCategory.homMk (a ≫ e.hom), ?_⟩
  apply InducedCategory.hom_ext
  change f.hom ≫ (a ≫ e.hom) = g.hom ≫ (a ≫ e.hom)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ e.hom) hfg).trans (Category.assoc _ _ _))

instance : IsFiltered (FinitePresentationModel R B) where
  cocone_objs := common_stage
  cocone_maps := fun {_ _} f g => coequalize f g
  nonempty := by
    obtain ⟨M, _⟩ := exists_representation (CommAlgCat.of R R) (Algebra.ofId R B)
    exact ⟨M⟩

variable (R B)

/-- The actual small filtered algebra diagram. -/
def diagram : FinitePresentationModel R B ⥤ CommAlgCat.{u} R :=
  inducedFunctor (FinitePresentationModelData.toOver R B) ⋙
    Over.forget (CommAlgCat.of R B)

/-- The canonical cocone given by the model maps to `B`. -/
def cocone : Cocone (diagram R B) where
  pt := CommAlgCat.of R B
  ι :=
    { app := fun M => CommAlgCat.ofHom M.map
      naturality := fun _ _ f =>
        (Over.w f.hom).trans (Category.comp_id _).symm }

end FinitePresentationModel

end Algebra
