/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteSectionSubmodule
import Nyll.SchemeTheory.Modules.QuasicoherentLocal
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Finite section families on an actual open subscheme

The original sections on an open are transported to the top of that open
subscheme by the native restriction comparison. The finite free image
construction produces an actual quasicoherent finite-type local submodule,
and each specified original section has an actual lift through its inclusion.
This is the local input for extending finite affine generators globally.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Actual sections on the top of an open subscheme are the original
sections on that open. -/
def openTopSectionsIso {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) :
    Γ(F.restrict U.ι, ⊤) ≅ Γ(F, U) :=
  F.restrictAppIso U.ι ⊤ ≪≫
    eqToIso (congrArg (fun W : X.Opens => Γ(F, W))
      (U.ι.image_top_eq_opensRange.trans U.opensRange_ι))

/-- Finitely many actual sections on an open lift through a finite-type
quasicoherent submodule on the open subscheme. -/
theorem exists_finiteType_restriction_submodule_lifting_sections
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens)
    {I : Type u} [Finite I] (s : I → F.val.obj (op U)) :
    ∃ N : ((sheafOfModulesEquivalence U.toScheme).functor.obj
        (F.restrict U.ι)).Submodule,
      N.toSheafOfModules.IsQuasicoherent ∧ N.toSheafOfModules.IsFiniteType ∧
        ∀ i : I, ∃ t : N.toSheafOfModules.val.obj (op ⊤),
          (openTopSectionsIso F U).hom ((N.ι.val.app (op ⊤)).hom t) = s i := by
  let A : SheafOfModules.{u} U.toScheme.ringCatSheaf :=
    (sheafOfModulesEquivalence U.toScheme).functor.obj (F.restrict U.ι)
  have : A.IsQuasicoherent := inferInstanceAs (F.restrict U.ι).IsQuasicoherent
  let e := openTopSectionsIso F U
  let a : I → A.sections := fun i => A.topSection (e.inv (s i))
  let N : A.Submodule := A.sectionFamilySubmodule a
  refine ⟨N, A.isQuasicoherent_sectionFamilySubmodule a,
    A.isFiniteType_sectionFamilySubmodule a, ?_⟩
  intro i
  have hi : e.inv (s i) ∈ N.toSubmodule.obj (op ⊤) :=
    (A.topSection_top (e.inv (s i))) ▸ A.mem_sectionFamilySubmodule a i ⊤
  refine ⟨⟨e.inv (s i), hi⟩, ?_⟩
  exact congrArg (fun f : Γ(F, U) ⟶ Γ(F, U) => f (s i)) e.inv_hom_id

end AlgebraicGeometry.Scheme.Modules
