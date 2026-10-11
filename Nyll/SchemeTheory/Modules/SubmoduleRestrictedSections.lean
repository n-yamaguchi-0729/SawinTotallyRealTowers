/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteOpenSectionSubmodule
import Nyll.SchemeTheory.Modules.SubmoduleRestrictionComparison

/-!
# Actual membership from a lifted section on an open subscheme

The top-section restriction comparison is natural in the actual module.
A lift through the restricted inclusion therefore gives an element of the
original native section submodule. This supplies the containment step after
the geometric kernel extension has recovered its prescribed local module.
-/

noncomputable section

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual top-section comparison respects module morphisms. -/
theorem openTopSectionsIso_hom_naturality
    {X : Scheme.{u}} {F G : X.Modules} (φ : F ⟶ G) (U : X.Opens) :
    (openTopSectionsIso F U).hom ≫ φ.app U =
      ((restrictFunctor U.ι).map φ).app ⊤ ≫ (openTopSectionsIso G U).hom := by
  have h (V W : X.Opens) (hVW : V = W) :
      eqToHom (congrArg (fun Z => Γ(F, Z)) hVW) ≫ φ.app W =
        φ.app V ≫ eqToHom (congrArg (fun Z => Γ(G, Z)) hVW) := by
    cases hVW
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact h (U.ι ''ᵁ ⊤) U (U.ι.image_top_eq_opensRange.trans U.opensRange_ι)

/-- An actual lift on the open subscheme proves membership in the original
native section submodule. -/
theorem mem_submodule_of_restrict_lift
    {X : Scheme.{u}} {F : X.Modules} (H : F.Submodule) (U : X.Opens)
    (x : F.val.obj (op U))
    (t : Γ((submoduleAsModule H).restrict U.ι, ⊤))
    (ht : (openTopSectionsIso F U).hom
      (((restrictFunctor U.ι).map (submoduleAsModuleInclusion H)).app ⊤ t) = x) :
    x ∈ H.toSubmodule.obj (op U) := by
  let y : H.toSheafOfModules.val.obj (op U) :=
    (openTopSectionsIso (submoduleAsModule H) U).hom t
  have hn := openTopSectionsIso_hom_naturality (submoduleAsModuleInclusion H) U
  have hy : y.val = x := (congrArg (fun g => g t) hn).trans ht
  exact hy ▸ y.property

end AlgebraicGeometry.Scheme.Modules
