/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.QuasicoherentLocal
import Nyll.SchemeTheory.Modules.SubmoduleGluingQuasicoherent
import Nyll.SchemeTheory.Modules.SubmoduleEmbeddedIso
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Comparing native submodule restrictions with open-subscheme modules

The comparison is built from the actual sectionwise restriction of the
submodule and the canonical slice-to-open equivalence. Its inclusion
identity lets geometric restriction isomorphisms give literal equality
of the native restricted submodules.
-/

noncomputable section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual module of a native submodule, regarded in the scheme-module category. -/
def submoduleAsModule {X : Scheme.{u}} {F : X.Modules} (N : F.Submodule) : X.Modules :=
  (sheafOfModulesEquivalence X).inverse.obj N.toSheafOfModules

/-- The native inclusion in the scheme-module category. The identity-action
equivalence preserves the actual ambient module and the actual section maps. -/
def submoduleAsModuleInclusion {X : Scheme.{u}} {F : X.Modules} (N : F.Submodule) :
    submoduleAsModule N ⟶ F :=
  (sheafOfModulesEquivalence X).inverse.map N.ι

/-- The actual native restriction, viewed on the open subscheme, is the
geometric restriction of the submodule's module. -/
def submoduleOverRestrictIso
    {X : Scheme.{u}} {F : X.Modules} (N : F.Submodule) (U : X.Opens) :
    (overEquiv U).functor.obj (N.over U).toSheafOfModules ≅
      (submoduleAsModule N).restrict U.ι :=
  (overEquiv U).functor.mapIso (SheafOfModules.Submodule.overSheafIso N U) ≪≫
    (overFunctorEquiv U).app (submoduleAsModule N)

/-- The native and geometric restriction comparisons preserve the actual inclusions. -/
theorem submoduleOverRestrictIso_hom_ι
    {X : Scheme.{u}} {F : X.Modules} (N : F.Submodule) (U : X.Opens) :
    (submoduleOverRestrictIso N U).hom ≫
        (restrictFunctor U.ι).map (submoduleAsModuleInclusion N) =
      (overEquiv U).functor.map (N.over U).ι ≫ ((overFunctorEquiv U).app F).hom := by
  let S := (overEquiv U).functor
  let o := SheafOfModules.Submodule.overSheafIso N U
  let e := (overFunctorEquiv U).app (submoduleAsModule N)
  let eF := (overFunctorEquiv U).app F
  have hn : e.hom ≫ (restrictFunctor U.ι).map (submoduleAsModuleInclusion N) =
      S.map (N.ι.over U) ≫ eF.hom :=
    ((overFunctorEquiv U).hom.naturality (submoduleAsModuleInclusion N)).symm
  have hm : S.map o.hom ≫ S.map (N.ι.over U) = S.map (N.over U).ι :=
    (S.map_comp o.hom (N.ι.over U)).symm.trans
      (congrArg S.map (SheafOfModules.Submodule.overSheafIso_hom_ι N U))
  exact (Category.assoc (S.map o.hom) e.hom _).trans
    ((congrArg (fun t => S.map o.hom ≫ t) hn).trans
      ((Category.assoc (S.map o.hom) (S.map (N.ι.over U)) eF.hom).symm.trans
        (congrArg (fun t => t ≫ eF.hom) hm)))

/-- An actual isomorphism between geometric restrictions, preserving the
inclusions, gives equality of the actual native submodules on the slice. -/
theorem submodule_over_eq_of_restrictIso
    {X : Scheme.{u}} {F : X.Modules} (N P : F.Submodule) (U : X.Opens)
    (e : (submoduleAsModule N).restrict U.ι ≅ (submoduleAsModule P).restrict U.ι)
    (he : e.hom ≫ (restrictFunctor U.ι).map (submoduleAsModuleInclusion P) =
      (restrictFunctor U.ι).map (submoduleAsModuleInclusion N)) :
    N.over U = P.over U := by
  let S := (overEquiv U).functor
  let eN := submoduleOverRestrictIso N U
  let eP := submoduleOverRestrictIso P U
  let eF := (overFunctorEquiv U).app F
  let eMapped := eN ≪≫ e ≪≫ eP.symm
  let eSlice := (overEquiv U).fullyFaithfulFunctor.preimageIso eMapped
  apply SheafOfModules.Submodule.eq_of_iso_ι _ _ eSlice
  apply S.map_injective
  have hpre : S.map eSlice.hom = eMapped.hom :=
    (overEquiv U).fullyFaithfulFunctor.map_preimage eMapped.hom
  have hP : eP.inv ≫ (S.map (P.over U).ι ≫ eF.hom) =
      (restrictFunctor U.ι).map (submoduleAsModuleInclusion P) :=
    (Iso.inv_comp_eq eP).2 (submoduleOverRestrictIso_hom_ι P U).symm
  have hN := submoduleOverRestrictIso_hom_ι N U
  have hm : eMapped.hom ≫ (S.map (P.over U).ι ≫ eF.hom) =
      S.map (N.over U).ι ≫ eF.hom := by
    exact (Category.assoc eN.hom (e.hom ≫ eP.inv) _).trans
      ((congrArg (fun t => eN.hom ≫ t) (Category.assoc e.hom eP.inv _)).trans
        ((congrArg (fun t => eN.hom ≫ e.hom ≫ t) hP).trans
          ((congrArg (fun t => eN.hom ≫ t) he).trans hN)))
  have : IsIso (C := U.toScheme.Modules) eF.hom := inferInstance
  apply (cancel_mono eF.hom).mp
  exact (congrArg (fun t => t ≫ eF.hom)
      ((S.map_comp eSlice.hom (P.over U).ι).trans
        (congrArg (fun t => t ≫ S.map (P.over U).ι) hpre))).trans
    ((Category.assoc eMapped.hom (S.map (P.over U).ι) eF.hom).trans hm)

end AlgebraicGeometry.Scheme.Modules
