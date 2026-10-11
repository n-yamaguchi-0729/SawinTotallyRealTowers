/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.QuasicoherentExtension
import Nyll.SchemeTheory.Modules.KernelSubmoduleScheme
import Nyll.SchemeTheory.Modules.SubmoduleGluingQuasicoherent
import Nyll.SchemeTheory.Modules.SubmoduleEmbeddedIso
import Nyll.SchemeTheory.Modules.QuasicoherentLocal
import Mathlib.Topology.Sheaves.Module
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.Over

/-!
# Literal extension of quasicoherent subsheaves on an open subscheme

The input and restriction use the actual sectionwise submodules on the
slice site. The kernel of the map to the direct image of the quotient
extends the input, and the embedded restriction isomorphism gives equality
of the native submodules. This is the submodule assertion of Stacks 01PE(2).
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

private theorem isQuasicoherent_sheafOfModulesEquivOver
    {X : TopCat.{u}} (V : TopologicalSpace.Opens X) (R : X.Sheaf RingCat.{u})
    (M : SheafOfModules.{u} (R.over V)) [M.IsQuasicoherent] :
    ((V.sheafOfModulesEquivOver R).functor.obj M).IsQuasicoherent := by
  let α : V.sheafRestrict.obj R ⟶
      (V.overEquivalence.inverse.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology V)
        ((Opens.grothendieckTopology X).over V)).obj
          (R.over V) :=
    (V.overPullbackSheafEquivOver.app R).inv
  have : IsIso α := (V.overPullbackSheafEquivOver.app R).isIso_inv
  have : ∀ W : TopologicalSpace.Opens V,
      (Over.post (X := W) V.overEquivalence.inverse).IsContinuous
        ((Opens.grothendieckTopology V).over W)
        (((Opens.grothendieckTopology X).over V).over
          (V.overEquivalence.inverse.obj W)) := by
    intro W
    exact Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ (Over.post (X := W) V.overEquivalence.inverse))
      (CoverPreserving.overPost W (Functor.IsDenseSubsite.coverPreserving
        (Opens.grothendieckTopology V) ((Opens.grothendieckTopology X).over V)
        V.overEquivalence.inverse))
  exact SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
    V.overEquivalence.inverse α (V.sheafOfModulesEquivOverUnit R)
    (M := M)

private def submoduleOverInclusion
    {X : Scheme.{u}} (F : X.Modules) (V : X.Opens) (N : (F.over V).Submodule) :
    (overEquiv V).functor.obj N.toSheafOfModules ⟶ F.restrict V.ι :=
  (overEquiv V).functor.map N.ι ≫ ((overFunctorEquiv V).app F).hom

private instance submoduleOverInclusion_mono
    {X : Scheme.{u}} (F : X.Modules) (V : X.Opens) (N : (F.over V).Submodule) :
    Mono (submoduleOverInclusion F V N) := by
  have hN : Mono (C := SheafOfModules.{u} (X.ringCatSheaf.over V)) N.ι :=
    (SheafOfModules.forget (X.ringCatSheaf.over V)).mono_of_mono_map
      (PresheafOfModules.mono_of_injective (fun _ => Subtype.val_injective))
  have hm : Mono (C := V.toScheme.Modules) ((overEquiv V).functor.map N.ι) :=
    Functor.map_mono _ _
  have he : IsIso (C := V.toScheme.Modules) ((overFunctorEquiv V).app F).hom :=
    inferInstance
  change Mono (C := V.toScheme.Modules)
    ((overEquiv V).functor.map N.ι ≫ ((overFunctorEquiv V).app F).hom)
  exact mono_comp _ _

/-- The actual global subsheaf obtained from the quotient of the prescribed
subsheaf on the open subscheme. -/
def extendQuasicoherentSubmoduleOver
    {X : Scheme.{u}} (F : X.Modules) (V : X.Opens) (N : (F.over V).Submodule) :
    F.Submodule :=
  kernelSubmodule (submoduleExtensionMap V.ι F (submoduleOverInclusion F V N))

private def submoduleOverKernelIso
    {X : Scheme.{u}} (F : X.Modules) (V : X.Opens) (N : (F.over V).Submodule) :
    ((extendQuasicoherentSubmoduleOver F V N).over V).toSheafOfModules ≅
      ((sheafOfModulesEquivalence X).functor.obj
        (kernel (submoduleExtensionMap V.ι F (submoduleOverInclusion F V N)))).over V :=
  SheafOfModules.Submodule.overSheafIso (extendQuasicoherentSubmoduleOver F V N) V ≪≫
    (SheafOfModules.overFunctor X.ringCatSheaf V).mapIso
      (kernelSubmoduleIso (submoduleExtensionMap V.ι F (submoduleOverInclusion F V N)))

private theorem submoduleOverKernelIso_hom_ι
    {X : Scheme.{u}} (F : X.Modules) (V : X.Opens) (N : (F.over V).Submodule) :
    (submoduleOverKernelIso F V N).hom ≫
      ((sheafOfModulesEquivalence X).functor.map
        (kernel.ι (submoduleExtensionMap V.ι F (submoduleOverInclusion F V N)))).over V =
      ((extendQuasicoherentSubmoduleOver F V N).over V).ι := by
  let ψ := submoduleExtensionMap V.ι F (submoduleOverInclusion F V N)
  let T := SheafOfModules.overFunctor X.ringCatSheaf V
  let κ := kernelSubmoduleIso ψ
  let k := (sheafOfModulesEquivalence X).functor.map (kernel.ι ψ)
  let o := SheafOfModules.Submodule.overSheafIso
    (extendQuasicoherentSubmoduleOver F V N) V
  have hk : T.map κ.hom ≫ T.map k = T.map (kernelSubmodule ψ).ι :=
    (T.map_comp κ.hom k).symm.trans
      (congrArg T.map (kernelSubmoduleIso_hom_ι ψ))
  exact (Category.assoc o.hom (T.map κ.hom) (T.map k)).trans
    ((congrArg (fun t => o.hom ≫ t) hk).trans
      (SheafOfModules.Submodule.overSheafIso_hom_ι
        (extendQuasicoherentSubmoduleOver F V N) V))

private def submoduleOverExtensionSchemeIso
    {X : Scheme.{u}} (F : X.Modules) (V : X.Opens) (N : (F.over V).Submodule) :
    (overEquiv V).functor.obj
        ((extendQuasicoherentSubmoduleOver F V N).over V).toSheafOfModules ≅
      (overEquiv V).functor.obj N.toSheafOfModules :=
  (overEquiv V).functor.mapIso (submoduleOverKernelIso F V N) ≪≫
    (overFunctorEquiv V).app
      (kernel (submoduleExtensionMap V.ι F (submoduleOverInclusion F V N))) ≪≫
    submoduleExtensionRestrictIso V.ι F (submoduleOverInclusion F V N)

private theorem submoduleOverExtensionSchemeIso_hom_ι
    {X : Scheme.{u}} (F : X.Modules) (V : X.Opens) (N : (F.over V).Submodule) :
    (submoduleOverExtensionSchemeIso F V N).hom ≫ submoduleOverInclusion F V N =
      (overEquiv V).functor.map ((extendQuasicoherentSubmoduleOver F V N).over V).ι ≫
        ((overFunctorEquiv V).app F).hom := by
  let ψ := submoduleExtensionMap V.ι F (submoduleOverInclusion F V N)
  have hn : ((overFunctorEquiv V).app (kernel ψ)).hom ≫
      (restrictFunctor V.ι).map (kernel.ι ψ) =
      (overEquiv V).functor.map
          (((sheafOfModulesEquivalence X).functor.map (kernel.ι ψ)).over V) ≫
        ((overFunctorEquiv V).app F).hom :=
    ((overFunctorEquiv V).hom.naturality (kernel.ι ψ)).symm
  let S := (overEquiv V).functor
  let a := S.map (submoduleOverKernelIso F V N).hom
  let b := ((overFunctorEquiv V).app (kernel ψ)).hom
  let c := (submoduleExtensionRestrictIso V.ι F (submoduleOverInclusion F V N)).hom
  let d := submoduleOverInclusion F V N
  let k := ((sheafOfModulesEquivalence X).functor.map (kernel.ι ψ)).over V
  let e := ((overFunctorEquiv V).app F).hom
  have hmap : a ≫ S.map k =
      S.map ((extendQuasicoherentSubmoduleOver F V N).over V).ι :=
    (S.map_comp (submoduleOverKernelIso F V N).hom k).symm.trans
      (congrArg S.map (submoduleOverKernelIso_hom_ι F V N))
  have hcd : c ≫ d = (restrictFunctor V.ι).map (kernel.ι ψ) :=
    submoduleExtensionRestrictIso_hom_ι V.ι F (submoduleOverInclusion F V N)
  exact (Category.assoc a (b ≫ c) d).trans
    ((congrArg (fun t => a ≫ t) (Category.assoc b c d)).trans
      ((congrArg (fun t => a ≫ b ≫ t) hcd).trans
        ((congrArg (fun t => a ≫ t) hn).trans
          ((Category.assoc a (S.map k) e).symm.trans
            (congrArg (fun t => t ≫ e) hmap)))))

/-- The constructed extension restricts to the prescribed actual submodule.
The equality is in the native slice-site submodule lattice. -/
theorem extendQuasicoherentSubmoduleOver_over
    {X : Scheme.{u}} (F : X.Modules) (V : X.Opens) (N : (F.over V).Submodule) :
    (extendQuasicoherentSubmoduleOver F V N).over V = N := by
  let e := (overEquiv V).fullyFaithfulFunctor.preimageIso
    (submoduleOverExtensionSchemeIso F V N)
  apply SheafOfModules.Submodule.eq_of_iso_ι _ _ e
  apply (overEquiv V).functor.map_injective
  rw [Functor.map_comp]
  change (overEquiv V).functor.map
      ((overEquiv V).fullyFaithfulFunctor.preimage
        (submoduleOverExtensionSchemeIso F V N).hom) ≫
      (overEquiv V).functor.map N.ι = _
  rw [(overEquiv V).fullyFaithfulFunctor.map_preimage]
  have : IsIso (C := V.toScheme.Modules) ((overFunctorEquiv V).app F).hom :=
    inferInstance
  apply (cancel_mono ((overFunctorEquiv V).app F).hom).mp
  rw [Category.assoc]
  exact submoduleOverExtensionSchemeIso_hom_ι F V N

/-- The actual subsheaf extension is quasicoherent when the open immersion
is quasi-compact and the ambient and prescribed modules are quasicoherent. -/
theorem isQuasicoherent_extendQuasicoherentSubmoduleOver
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    (V : X.Opens) [QuasiCompact V.ι] (N : (F.over V).Submodule)
    (hN : N.toSheafOfModules.IsQuasicoherent) :
    (extendQuasicoherentSubmoduleOver F V N).toSheafOfModules.IsQuasicoherent := by
  have : N.toSheafOfModules.IsQuasicoherent := hN
  have : ((overEquiv V).functor.obj N.toSheafOfModules).IsQuasicoherent :=
    isQuasicoherent_sheafOfModulesEquivOver V X.ringCatSheaf N.toSheafOfModules
  have hK : (kernel
      (submoduleExtensionMap V.ι F (submoduleOverInclusion F V N))).IsQuasicoherent :=
    isQuasicoherent_kernel_submoduleExtensionMap V.ι F (submoduleOverInclusion F V N)
  have hK' : ((sheafOfModulesEquivalence X).functor.obj
      (kernel (submoduleExtensionMap V.ι F
        (submoduleOverInclusion F V N)))).IsQuasicoherent := hK
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (kernelSubmoduleIso (submoduleExtensionMap V.ι F
      (submoduleOverInclusion F V N))).symm hK'

end AlgebraicGeometry.Scheme.Modules
