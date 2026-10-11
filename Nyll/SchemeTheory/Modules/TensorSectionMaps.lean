/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_tensorHom_app_tensorSections.lean
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
# Tensor morphisms on local tensor sections

The components of a tensor product of module morphisms act separately on the two
factors of a local tensor section.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_tensorHom_app_tensorSections

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

namespace TensorHomSections

open Opposite TensorProduct

variable {X : Scheme.{u}} {L L' M M' : X.Modules}

/-- The underlying presheaf functor in the native module category of the scheme. -/
abbrev ι (X : Scheme.{u}) : X.Modules ⥤ X.PresheafOfModules :=
  SheafOfModules.toPMod X.sheaf.obj X.ringCatSheaf.property

/-- The canonical adjunction between sheafification and the underlying presheaf functor. -/
abbrev adj (X : Scheme.{u}) : Modules.sheafify X ⊣ ι X :=
  SheafOfModules.sheafifyAdj X.sheaf.obj X.ringCatSheaf.property

variable (L M)

/-- The canonical comparison from the sheafified presheaf tensor product to the sheaf tensor
  product. -/
def sheafifyTensorIso : (Modules.sheafify X).obj ((ι X).obj L ⊗ (ι X).obj M) ≅ L ⊗ M :=
  (Functor.Monoidal.μIso (Modules.sheafify X) ((ι X).obj L) ((ι X).obj M)).symm ≪≫
    (SheafOfModules.sheafifyCounitIso X.sheaf.obj X.ringCatSheaf.property L ⊗ᵢ
        SheafOfModules.sheafifyCounitIso X.sheaf.obj X.ringCatSheaf.property M)

variable {L M}

lemma sheafifyTensorIso_hom_naturality (f : L ⟶ L') (g : M ⟶ M') :
    (Modules.sheafify X).map ((ι X).map f ⊗ₘ (ι X).map g) ≫ (sheafifyTensorIso L' M').hom =
      (sheafifyTensorIso L M).hom ≫ (f ⊗ₘ g) := by
  let F : X.PresheafOfModules ⥤ X.Modules := Modules.sheafify X
  change F.map ((ι X).map f ⊗ₘ (ι X).map g) ≫
      Functor.OplaxMonoidal.δ F ((ι X).obj L') ((ι X).obj M') ≫
        ((adj X).counit.app L' ⊗ₘ (adj X).counit.app M') =
    (Functor.OplaxMonoidal.δ F ((ι X).obj L) ((ι X).obj M) ≫
      ((adj X).counit.app L ⊗ₘ (adj X).counit.app M)) ≫ (f ⊗ₘ g)
  rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural F ((ι X).map f) ((ι X).map g),
    Category.assoc, Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom]
  erw [(adj X).counit.naturality f, (adj X).counit.naturality g]
  rfl

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

theorem tensorHom_app_tensorSections (φ : L ⟶ L') (ψ : M ⟶ M') {U : X.Opens} (s : Γ(L, U)) (t : Γ(M,
  U)) :
    (φ ⊗ₘ ψ).app U (Modules.tensorSections s t) = Modules.tensorSections (φ.app U s) (ψ.app U t) :=
        by
  have h := congr($(sheafifyTensorIso_hom_naturality φ ψ).val.app (op U)
    (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
      ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U)))))
  have h' : (sheafifyTensorIso L' M').hom.val.app (op U)
      (((Modules.sheafify X).map ((ι X).map φ ⊗ₘ (ι X).map ψ)).val.app (op U)
        (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
          ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))))) =
      (φ ⊗ₘ ψ).val.app (op U) ((sheafifyTensorIso L M).hom.val.app (op U)
        (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
          ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))))) := h
  rw [tensorSections_eq, tensorSections_eq]
  change (φ ⊗ₘ ψ).val.app (op U) ((sheafifyTensorIso L M).hom.val.app (op U)
    (((adj X).unit.app ((ι X).obj L ⊗ (ι X).obj M)).app (op U)
      ((s : L.val.obj (op U)) ⊗ₜ[Γ(X, U)] (t : M.val.obj (op U))))) = _
  rw [← h']
  erw [sheafify_map_val_app_unit ((ι X).map φ ⊗ₘ (ι X).map ψ) (op U)]
  congr 1

end TensorHomSections

end AlgebraicGeometry.Scheme.Modules

end

open _root_.AlgebraicGeometry AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules
    AlgebraicGeometry.Scheme.Modules in
theorem _root_.AlgebraicGeometry.Scheme.Modules.tensorHom_app_tensorSections {X :
  AlgebraicGeometry.Scheme.{u}} {L L' M M' : X.Modules} (φ : L ⟶ L') (ψ : M ⟶ M') {U : X.Opens}
    (s : Γ(L, U)) (t : Γ(M, U)) :
    (φ ⊗ₘ ψ).app U (AlgebraicGeometry.Scheme.Modules.tensorSections s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (φ.app U s) (ψ.app U t) :=
  TensorHomSections.tensorHom_app_tensorSections φ ψ s t
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_tensorHom_app_tensorSections
end ProofImplementation
