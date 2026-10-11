/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.SubmoduleRestrictionComparison
import Nyll.SchemeTheory.Modules.SubmoduleOverEquality
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Whole submodules and restrictions on which they generate

The module of the top submodule is canonically the ambient module. If an
actual native submodule equals the whole module on a slice, the geometric
restriction of its inclusion is an isomorphism: each actual section map
is the bijective inclusion of the full section submodule.
-/

noncomputable section

universe u v v₁ u₁

open CategoryTheory Opposite

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}

/-- The top sheaf submodule has the full section submodule on every object. -/
theorem top_obj (M : SheafOfModules.{v} R) (U : Cᵒᵖ) :
    (⊤ : M.Submodule).toSubmodule.obj U = ⊤ := by
  let Q : M.Submodule :=
    { toSubmodule := ⊤
      isSheaf := by
        intro V s hs
        exact _root_.Submodule.mem_top }
  have hQ : Q = ⊤ := top_unique (by
    intro V s hs
    exact _root_.Submodule.mem_top)
  rw [← hQ]
  rfl

private def topSectionEquiv (M : SheafOfModules.{v} R) (U : Cᵒᵖ) :
    (⊤ : M.Submodule).toSubmodule.obj U ≃ₗ[R.obj.obj U] M.val.obj U where
  toFun := Subtype.val
  invFun s := ⟨s, by rw [top_obj]; exact _root_.Submodule.mem_top⟩
  left_inv s := Subtype.ext rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The module of the actual top submodule is the ambient module. -/
def topIso (M : SheafOfModules.{v} R) :
    (⊤ : M.Submodule).toSheafOfModules ≅ M :=
  (SheafOfModules.fullyFaithfulForget R).preimageIso
    (PresheafOfModules.isoMk
      (fun U => (topSectionEquiv M U).toModuleIso)
      (fun {_ _} _ => rfl))

/-- The top-submodule comparison is its actual inclusion. -/
theorem topIso_hom (M : SheafOfModules.{v} R) :
    (topIso M).hom = (⊤ : M.Submodule).ι := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  rfl

end SheafOfModules.Submodule

namespace AlgebraicGeometry.Scheme.Modules

/-- Equality with the whole native module on an open makes the actual
geometrically restricted inclusion an isomorphism. -/
theorem isIso_restrictSubmoduleInclusion_of_over_eq_top
    {X : Scheme.{u}} {F : SheafOfModules.{u} X.ringCatSheaf}
    (N : F.Submodule) (U : X.Opens)
    (hN : N.over U = (⊤ : F.Submodule).over U) :
    IsIso ((restrictFunctor U.ι).map
      (submoduleAsModuleInclusion (F := (sheafOfModulesEquivalence X).inverse.obj F) N)) := by
  let f := (restrictFunctor U.ι).map
    (submoduleAsModuleInclusion (F := (sheafOfModulesEquivalence X).inverse.obj F) N)
  let G := toPresheafOfModules U.toScheme
  have hm : Mono (G.map f) := PresheafOfModules.mono_of_injective (by
    intro W a b hab
    apply Subtype.ext
    exact hab)
  have he : Epi (G.map f) := PresheafOfModules.epi_of_surjective (by
    intro W s
    let s' : F.val.obj (op (U.ι ''ᵁ W.unop)) := s
    have hs : s' ∈ N.toSubmodule.obj (op (U.ι ''ᵁ W.unop)) := by
      rw [SheafOfModules.Submodule.obj_eq_of_over_eq hN
        (U.ι ''ᵁ W.unop) (homOfLE (U.ι_image_le W.unop)),
        SheafOfModules.Submodule.top_obj]
      exact _root_.Submodule.mem_top
    exact ⟨⟨s', hs⟩, rfl⟩)
  have hi : IsIso (G.map f) := isIso_of_mono_of_epi (G.map f)
  exact (fullyFaithfulToPresheafOfModules (X := U.toScheme)).isIso_of_isIso_map f

end AlgebraicGeometry.Scheme.Modules
