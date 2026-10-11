/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.AffineModuleEpi
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.CategoryTheory.Functor.EpiMono

/-!
# Epimorphisms over actual affine opens

Surjectivity on an affine open gives an epimorphism on its native slice
site when the target is quasicoherent. The proof first uses the actual
canonical spectrum of the affine open, then transports through restriction
and the equivalence with the slice site.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- Surjectivity on an affine open implies that the actual restriction to
its slice site is epimorphic, provided the target is quasicoherent. -/
theorem epi_over_of_surjective_app {X : Scheme.{u}} {M N : X.Modules}
    [N.IsQuasicoherent] (φ : M ⟶ N) (U : X.Opens) (hU : IsAffineOpen U)
    (hφ : Function.Surjective (φ.app U)) : Epi (SheafOfModules.Hom.over φ U) := by
  let f : Spec Γ(X, U) ⟶ X := hU.fromSpec
  have himage : f ''ᵁ ⊤ = U :=
    f.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  have hφ' : Function.Surjective (φ.app (f ''ᵁ ⊤)) := by
    rw [himage]
    exact hφ
  have hsurj : Function.Surjective (((restrictFunctor f).map φ).app ⊤) := by
    intro y
    obtain ⟨x, hx⟩ := hφ' ((N.restrictAppIso f ⊤).hom y)
    refine ⟨(M.restrictAppIso f ⊤).inv x, ?_⟩
    apply (ConcreteCategory.bijective_of_isIso (N.restrictAppIso f ⊤).hom).injective
    change φ.app (f ''ᵁ ⊤) x = (N.restrictAppIso f ⊤).hom y
    exact hx
  have : Epi ((restrictFunctor f).map φ) :=
    epi_of_surjective_moduleSpecΓ ((restrictFunctor f).map φ) hsurj
  let e : restrictFunctor f ⋙ restrictFunctor hU.isoSpec.hom ≅ restrictFunctor U.ι :=
    (restrictFunctorComp hU.isoSpec.hom f).symm ≪≫
      restrictFunctorCongr hU.isoSpec_hom_fromSpec
  have : Epi ((restrictFunctor hU.isoSpec.hom).map ((restrictFunctor f).map φ)) :=
    inferInstance
  have hRestrict : Epi ((restrictFunctor U.ι).map φ) := by
    have heq : (restrictFunctor hU.isoSpec.hom).map ((restrictFunctor f).map φ) ≫
        (e.app N).hom = (e.app M).hom ≫ (restrictFunctor U.ι).map φ :=
      e.hom.naturality φ
    have hComp : Epi (C := U.toScheme.Modules)
        ((restrictFunctor hU.isoSpec.hom).map ((restrictFunctor f).map φ) ≫ (e.app N).hom) :=
      epi_comp _ _
    have : Epi (C := U.toScheme.Modules) ((e.app M).hom ≫ (restrictFunctor U.ι).map φ) :=
      Eq.mp (congrArg (fun g => Epi (C := U.toScheme.Modules) g) heq) hComp
    exact epi_of_epi (C := U.toScheme.Modules) (e.app M).hom ((restrictFunctor U.ι).map φ)
  have hOver : Epi ((overEquiv U).functor.map (SheafOfModules.Hom.over φ U)) := by
    have heq : (overEquiv U).functor.map (SheafOfModules.Hom.over φ U) ≫
        ((overFunctorEquiv U).app N).hom =
        ((overFunctorEquiv U).app M).hom ≫ (restrictFunctor U.ι).map φ :=
      (overFunctorEquiv U).hom.naturality φ
    have hComp : Epi (C := U.toScheme.Modules)
        (((overFunctorEquiv U).app M).hom ≫ (restrictFunctor U.ι).map φ) :=
      epi_comp _ _
    have hComp' : Epi (C := U.toScheme.Modules)
        ((overEquiv U).functor.map (SheafOfModules.Hom.over φ U) ≫
          ((overFunctorEquiv U).app N).hom) :=
      Eq.mp (congrArg (fun g => Epi (C := U.toScheme.Modules) g) heq.symm) hComp
    exact (epi_comp_iff_of_isIso (C := U.toScheme.Modules)
      ((overEquiv U).functor.map (SheafOfModules.Hom.over φ U))
      ((overFunctorEquiv U).app N).hom).mp hComp'
  exact (overEquiv U).functor.epi_of_epi_map hOver

end AlgebraicGeometry.Scheme.Modules
