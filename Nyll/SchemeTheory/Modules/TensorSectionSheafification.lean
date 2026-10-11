/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_sheafify_mu_app_tensorSections.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.PresheafInternalHom
import Nyll.SchemeTheory.Modules.SheafificationMonoidal
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.TensorSections

/-!
# Sheafification comparisons on tensor sections

The monoidal sheafification comparison carries the tensor of two unit images to the
unit image of their presheaf tensor.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_sheafify_mu_app_tensorSections

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

local instance presheafSectionsModule {X : Scheme.{u}}
    (P : X.PresheafOfModules) (U : X.Opens) :
    Module Γ(X, U) (P.obj (Opposite.op U)) :=
  (P.obj (Opposite.op U)).isModule

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace Scheme
open _root_.AlgebraicGeometry.Scheme
namespace Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme.Modules
open _root_.AlgebraicGeometry.Scheme
open _root_.AlgebraicGeometry

namespace SheafifyMu

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.Opposite
open _root_.TensorProduct

variable {X : Scheme.{u}}

/-- The functor taking a module sheaf on a scheme to its underlying module presheaf. -/
abbrev ι (X : Scheme.{u}) : X.Modules ⥤ X.PresheafOfModules :=
  SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

/-- The adjunction between module presheaf sheafification and passage to underlying presheaves. -/
abbrev adj (X : Scheme.{u}) : Modules.sheafify X ⊣ ι X :=
  SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

variable (L M : X.Modules)

/-- The comparison isomorphism from the sheafified tensor of underlying presheaves to the tensor of
  module sheaves. -/
def sheafifyTensorIso : (Modules.sheafify X).obj ((ι X).obj L ⊗ (ι X).obj M) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (Modules.sheafify X) ((ι X).obj L) ((ι X).obj M)).symm ≪≫
    (SheafOfModules.sheafifyCounitIso X.sheaf.obj X.ringCatSheaf.property L ⊗ᵢ
        SheafOfModules.sheafifyCounitIso X.sheaf.obj X.ringCatSheaf.property M)

variable {L M}

lemma tensorSections_eq {U : X.Opens} (s : Γ(L, U)) (t : Γ(M, U)) :
    Modules.tensorSections s t = (sheafifyTensorIso L M).hom.val.app (op U)
      (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
        ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))) := rfl

lemma sheafify_map_val_app_unit {P P' : X.PresheafOfModules} (g : P ⟶ P') (V : (X.Opens)ᵒᵖ) (z :
  P.obj V) :
    (((Modules.sheafify X).map g).val.app V) (((adj X).unit.app P).app V z) =
      ((adj X).unit.app P').app V (g.app V z) := by
  have h := (adj X).unit.naturality g
  exact (congr($(h.symm).app V z) :)

lemma map_tensorHom_unit_comp (P Q : X.PresheafOfModules) :
    (Modules.sheafify X).map ((adj X).unit.app P ⊗ₘ (adj X).unit.app Q) ≫
      (sheafifyTensorIso ((Modules.sheafify X).obj P) ((Modules.sheafify X).obj Q)).hom ≫
        Functor.LaxMonoidal.μ (Modules.sheafify X) P Q = 𝟙 _ := by
  have hP : (Modules.sheafify X).map ((adj X).unit.app P) ≫ (adj X).counit.app ((Modules.sheafify
      X).obj P) =
      𝟙 _ := (adj X).left_triangle_components P
  have hQ : (Modules.sheafify X).map ((adj X).unit.app Q) ≫ (adj X).counit.app ((Modules.sheafify
      X).obj Q) =
      𝟙 _ := (adj X).left_triangle_components Q
  let F : X.PresheafOfModules ⥤ X.Modules := Modules.sheafify X
  change F.map ((adj X).unit.app P ⊗ₘ (adj X).unit.app Q) ≫
    (Functor.OplaxMonoidal.δ F ((ι X).obj (F.obj P)) ((ι X).obj (F.obj Q)) ≫
      ((adj X).counit.app (F.obj P) ⊗ₘ (adj X).counit.app (F.obj Q))) ≫
        Functor.LaxMonoidal.μ F P Q = 𝟙 (F.obj (P ⊗ Q))
  simp only [← Category.assoc]
  erw [← Functor.OplaxMonoidal.δ_natural (Modules.sheafify X) ((adj X).unit.app P) ((adj X).unit.app
      Q)]
  rw [Category.assoc (Functor.OplaxMonoidal.δ (Modules.sheafify X) _ _)]
  erw [MonoidalCategory.tensorHom_comp_tensorHom, hP, hQ]
  erw [MonoidalCategory.id_tensorHom_id, Category.comp_id]
  exact Functor.Monoidal.δ_μ _ _ _

theorem sheafify_μ_app_tensorSections (P Q : X.PresheafOfModules) {U : X.Opens}
    (x : P.obj (op U)) (y : Q.obj (op U)) :
    (Functor.LaxMonoidal.μ (Modules.sheafify X) P Q).app U
      (Modules.tensorSections (L := (Modules.sheafify X).obj P) (M := (Modules.sheafify X).obj Q)
        (((adj X).unit.app P).app (op U) x) (((adj X).unit.app Q).app (op U) y)) =
    ((adj X).unit.app (P ⊗ Q)).app (op U) (x ⊗ₜ[Γ(X, U)] y) := by
  have H := congr($(map_tensorHom_unit_comp P Q).val.app (op U)
    (((adj X).unit.app (P ⊗ Q)).app (op U) (x ⊗ₜ[Γ(X, U)] y)))
  have h1 := (sheafify_map_val_app_unit ((adj X).unit.app P ⊗ₘ (adj X).unit.app Q) (op U)
      (x ⊗ₜ[Γ(X, U)] y)).trans
    (congrArg (((adj X).unit.app ((ι X).obj ((Modules.sheafify X).obj P) ⊗
        (ι X).obj ((Modules.sheafify X).obj Q))).app (op U))
      (ModuleCat.MonoidalCategory.tensorHom_tmul (R := Γ(X, U)) (((adj X).unit.app P).app (op U))
        (((adj X).unit.app Q).app (op U)) x y))
  exact (congrArg (fun z => (Functor.LaxMonoidal.μ (Modules.sheafify X) P Q).val.app (op U)
    ((sheafifyTensorIso ((Modules.sheafify X).obj P) ((Modules.sheafify X).obj Q)).hom.val.app (op
        U) z))
      h1).symm.trans H

end SheafifyMu

end AlgebraicGeometry.Scheme.Modules

end

open CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
    AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules
    TensorProduct in
theorem _root_.AlgebraicGeometry.Scheme.Modules.sheafify_mu_app_tensorSections {X :
  AlgebraicGeometry.Scheme.{u}} (P Q : X.PresheafOfModules) {U : X.Opens}
    (x : P.obj (Opposite.op U)) (y : Q.obj (Opposite.op U)) :
    (Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.sheafify X) P Q).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections
        (L := (AlgebraicGeometry.Scheme.Modules.sheafify X).obj P)
        (M := (AlgebraicGeometry.Scheme.Modules.sheafify X).obj Q)
        (((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app P).app
            (Opposite.op U) x)
        (((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app Q).app
            (Opposite.op U) y)) =
    ((SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property).unit.app (P ⊗ Q)).app
        (Opposite.op U)
      (x ⊗ₜ[Γ(X, U)] y) :=
  SheafifyMu.sheafify_μ_app_tensorSections P Q x y
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_sheafify_mu_app_tensorSections
end ProofImplementation
