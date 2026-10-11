/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.KernelSubmoduleScheme
import Nyll.SchemeTheory.Modules.SubmoduleRestrictionComparison
import Nyll.SchemeTheory.Modules.QuasicoherentExtension

/-!
# Restricting the actual kernel subsheaf extension

The native kernel submodule and the geometric kernel have the same actual
inclusion. Transporting that comparison along open restriction gives the
embedded geometric restriction isomorphism needed for affine extraction
and for preservation of prescribed local generators.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual kernel submodule, regarded as a scheme module, is the
categorical kernel. -/
def kernelSubmoduleAsModuleIso
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) :
    submoduleAsModule (kernelSubmodule φ) ≅ kernel φ :=
  (sheafOfModulesEquivalence X).inverse.mapIso (kernelSubmoduleIso φ)

/-- The actual native and categorical kernel inclusions agree under the comparison. -/
theorem kernelSubmoduleAsModuleIso_hom_ι
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) :
    (kernelSubmoduleAsModuleIso φ).hom ≫ kernel.ι φ =
      submoduleAsModuleInclusion (kernelSubmodule φ) := by
  let E := sheafOfModulesEquivalence X
  let κ := kernelSubmoduleIso φ
  let k := E.functor.map (kernel.ι φ)
  exact (E.inverse.map_comp κ.hom k).symm.trans
    (congrArg E.inverse.map (kernelSubmoduleIso_hom_ι φ))

/-- Restriction of the actual native kernel extension recovers the source
of the original monomorphism on the open subscheme. -/
def kernelSubmoduleExtensionRestrictIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) {G : U.Modules} (φ : G ⟶ F.restrict j) [Mono φ] :
    (submoduleAsModule (kernelSubmodule (submoduleExtensionMap j F φ))).restrict j ≅ G :=
  (restrictFunctor j).mapIso (kernelSubmoduleAsModuleIso (submoduleExtensionMap j F φ)) ≪≫
    submoduleExtensionRestrictIso j F φ

/-- The recovered source has its original inclusion in the restricted ambient module. -/
theorem kernelSubmoduleExtensionRestrictIso_hom_ι
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) {G : U.Modules} (φ : G ⟶ F.restrict j) [Mono φ] :
    (kernelSubmoduleExtensionRestrictIso j F φ).hom ≫ φ =
      (restrictFunctor j).map
        (submoduleAsModuleInclusion (kernelSubmodule (submoduleExtensionMap j F φ))) := by
  let L := restrictFunctor j
  let ψ := submoduleExtensionMap j F φ
  let e := kernelSubmoduleAsModuleIso ψ
  let d := submoduleExtensionRestrictIso j F φ
  exact (Category.assoc (L.map e.hom) d.hom φ).trans
    ((congrArg (fun t => L.map e.hom ≫ t)
      (submoduleExtensionRestrictIso_hom_ι j F φ)).trans
      ((L.map_comp e.hom (kernel.ι ψ)).symm.trans
        (congrArg L.map (kernelSubmoduleAsModuleIso_hom_ι ψ))))

end AlgebraicGeometry.Scheme.Modules
