/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_rightUnitor_hom_app_tensorSections.lean
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
# Scheme Modules right Unitor hom app tensor Sections
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_rightUnitor_hom_app_tensorSections

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry

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

namespace UnitorSections

open Opposite TensorProduct

variable {X : Scheme.{u}}

/-- The forgetful functor from scheme modules to their underlying presheaves of modules. -/
abbrev ι (X : Scheme.{u}) : X.Modules ⥤ X.PresheafOfModules :=
  SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

/-- The sheafification adjunction for modules over the scheme structure sheaf. -/
abbrev adj (X : Scheme.{u}) : Modules.sheafify X ⊣ ι X :=
  SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

lemma sheafify_map_val_app_unit {P P' : X.PresheafOfModules} (g : P ⟶ P') (V : (X.Opens)ᵒᵖ) (z :
  P.obj V) :
    (((Modules.sheafify X).map g).val.app V) (((adj X).unit.app P).app V z) =
      ((adj X).unit.app P').app V (g.app V z) := by
  have h := (adj X).unit.naturality g
  exact (congr($(h.symm).app V z) :)

lemma counit_val_app_unit (N : X.Modules) (V : (X.Opens)ᵒᵖ) (y : N.val.obj V) :
    (((adj X).counit.app N).val.app V) (((adj X).unit.app ((ι X).obj N)).app V y) = y := by
  have h := (adj X).right_triangle_components N
  exact (congr($(h).app V y) :)

variable (N : X.Modules)

/-- Compare sheafification of a module tensor the presheaf unit with the sheaf tensor unit. -/
def tensorUnitIso : (Modules.sheafify X).obj ((ι X).obj N ⊗ 𝟙_ X.PresheafOfModules) ≅ N ⊗ 𝟙_
  X.Modules :=
  (Functor.Monoidal.μIso (Modules.sheafify X) ((ι X).obj N) (𝟙_ X.PresheafOfModules)).symm ≪≫
    (SheafOfModules.sheafifyCounitIso X.sheaf.obj X.ringCatSheaf.property N ⊗ᵢ
      (Functor.Monoidal.εIso (Modules.sheafify X)).symm)

lemma tensorUnitIso_hom_comp_rightUnitor_hom :
    (tensorUnitIso N).hom ≫ (ρ_ N).hom =
      (Modules.sheafify X).map (ρ_ ((ι X).obj N)).hom ≫ (adj X).counit.app N := by
  let F : X.PresheafOfModules ⥤ X.Modules := Modules.sheafify X
  change (Functor.OplaxMonoidal.δ F ((ι X).obj N) (𝟙_ X.PresheafOfModules) ≫
      ((adj X).counit.app N ⊗ₘ Functor.OplaxMonoidal.η F)) ≫ (ρ_ N).hom =
    F.map (ρ_ ((ι X).obj N)).hom ≫ (adj X).counit.app N
  rw [Functor.Monoidal.map_rightUnitor F, MonoidalCategory.tensorHom_def']
  simp only [Category.assoc]
  erw [← MonoidalCategory.rightUnitor_naturality ((adj X).counit.app N)]
  all_goals rfl

theorem rightUnitor_hom_app_tensorSections {U : X.Opens} (n : Γ(N, U)) (g : Γ(X, U)) :
    (ρ_ N).hom.app U (Modules.tensorSections (L := N) (M := 𝟙_ X.Modules) n g) = g • n := by
  let : CommRing ((X.ringCatSheaf.obj).obj (op U)) := inferInstanceAs (CommRing Γ(X, U))
  have h := congr($(tensorUnitIso_hom_comp_rightUnitor_hom N).val.app (op U)
    (((adj X).unit.app ((ι X).obj N ⊗ 𝟙_ X.PresheafOfModules)).app (op U)
      ((n : N.val.obj (op U)) ⊗ₜ[(X.ringCatSheaf.obj).obj (op U)] (g : (𝟙_ X.PresheafOfModules).obj
        (op U)))))
  have h' : (ρ_ N).hom.val.app (op U) ((tensorUnitIso N).hom.val.app (op U)
      (((adj X).unit.app ((ι X).obj N ⊗ 𝟙_ X.PresheafOfModules)).app (op U)
        ((n : N.val.obj (op U)) ⊗ₜ[(X.ringCatSheaf.obj).obj (op U)] (g : (𝟙_
          X.PresheafOfModules).obj (op U))))) =
      ((adj X).counit.app N).val.app (op U) (((Modules.sheafify X).map (ρ_ ((ι X).obj
        N)).hom).val.app (op U)
        (((adj X).unit.app ((ι X).obj N ⊗ 𝟙_ X.PresheafOfModules)).app (op U)
          ((n : N.val.obj (op U)) ⊗ₜ[(X.ringCatSheaf.obj).obj (op U)] (g : (𝟙_
            X.PresheafOfModules).obj (op U))))) := h
  change (ρ_ N).hom.val.app (op U) ((tensorUnitIso N).hom.val.app (op U)
      (((adj X).unit.app ((ι X).obj N ⊗ 𝟙_ X.PresheafOfModules)).app (op U)
        ((n : N.val.obj (op U)) ⊗ₜ[(X.ringCatSheaf.obj).obj (op U)] (g : (𝟙_
          X.PresheafOfModules).obj (op U))))) = g • n
  rw [h']
  exact (congrArg (((adj X).counit.app N).val.app (op U))
      (sheafify_map_val_app_unit (ρ_ ((ι X).obj N)).hom (op U) _)).trans
    ((counit_val_app_unit N (op U) _).trans (ModuleCat.MonoidalCategory.rightUnitor_hom_apply _ _))

end UnitorSections

end AlgebraicGeometry.Scheme.Modules

end

open CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.AlgebraicGeometry
  AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.rightUnitor_hom_app_tensorSections {X :
  AlgebraicGeometry.Scheme.{u}} {N : X.Modules} {U : X.Opens} (n : Γ(N, U)) (g : Γ(X, U)) :
    (ρ_ N).hom.app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (L := N) (M := 𝟙_ X.Modules) n g) = g • n :=
  UnitorSections.rightUnitor_hom_app_tensorSections N n g
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_rightUnitor_hom_app_tensorSections
end ProofImplementation
