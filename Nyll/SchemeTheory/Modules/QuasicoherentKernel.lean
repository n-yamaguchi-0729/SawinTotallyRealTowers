/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.ModuleKernelLocalization
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Finite

/-!
# Quasicoherence of kernels over affine schemes

The section functor preserves the actual categorical kernel. Its canonical
comparison with the ordinary linear-map kernel commutes with restrictions.
Localization of kernels therefore proves quasicoherence, without assuming
an identification of the kernel or replacing the kernel by a new object.

This supplies the affine kernel step in Stacks, Tag 01PE.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

private theorem isLocalizedModule_of_commuting_isos
    {R : CommRingCat.{u}} (S : Submonoid R)
    {A B C D : ModuleCat.{u} R} (eA : A ≅ C) (eB : B ≅ D)
    (f : A ⟶ B) (g : C ⟶ D)
    (h : f ≫ eB.hom = eA.hom ≫ g)
    (hg : IsLocalizedModule S g.hom) : IsLocalizedModule S f.hom := by
  apply (IsLocalizedModule.comp_iff_of_bijective_left S eB.hom.hom
    (ConcreteCategory.bijective_of_isIso eB.hom)).mp
  rw [show eB.hom.hom.comp f.hom = g.hom.comp eA.hom.hom from
    congrArg ModuleCat.Hom.hom h]
  exact (IsLocalizedModule.comp_iff_of_bijective_right S eA.hom.hom
    (ConcreteCategory.bijective_of_isIso eA.hom)).mpr hg

private def affineModulePresheaf {R : CommRingCat.{u}} (M : (Spec R).Modules) :
    (Spec R).Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  (modulesSpecToSheaf.obj M).obj

private def affineModuleMap {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (φ : M ⟶ N) : affineModulePresheaf M ⟶ affineModulePresheaf N :=
  (modulesSpecToSheaf.map φ).hom

private def affineBasicOpen (R : CommRingCat.{u}) (r : R) : (Spec R).Opens :=
  PrimeSpectrum.basicOpen r

private def affineBasicOpenInclusion (R : CommRingCat.{u}) (r : R) :
    affineBasicOpen R r ⟶ (⊤ : (Spec R).Opens) :=
  homOfLE le_top

private def nativeAffineSectionFunctor (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    (Spec R).Modules ⥤ ModuleCat.{u} R :=
  SheafOfModules.evaluation.{u} (Spec R).ringCatSheaf (op U) ⋙
    ModuleCat.restrictScalars.{u}
      ((Spec R).ringCatSheaf.obj.map
        ((initialOpOfTerminal isTerminalTop).to (op U))).hom ⋙
      ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso R).inv.hom

private theorem restrictScalars_preservesFiniteLimits_native
    {A B : Type u} [Ring A] [Ring B] (f : A →+* B) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{u} f) where
  preservesFiniteLimits _ _ _ :=
    { preservesLimit := fun {D} => ModuleCat.preservesLimit_restrictScalars f D }

private instance nativeAffineSectionFunctor_preservesFiniteLimits
    (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    PreservesFiniteLimits (nativeAffineSectionFunctor R U) := by
  let A : RingCat.{u} := (Spec R).ringCatSheaf.obj.obj (op U)
  let B : RingCat.{u} := (Spec R).ringCatSheaf.obj.obj (op ⊤)
  let F : (Spec R).Modules ⥤ ModuleCat.{u} A :=
    SheafOfModules.evaluation.{u} (Spec R).ringCatSheaf (op U)
  let G : ModuleCat.{u} A ⥤ ModuleCat.{u} B := ModuleCat.restrictScalars.{u}
    ((Spec R).ringCatSheaf.obj.map
      ((initialOpOfTerminal isTerminalTop).to (op U))).hom
  let H : ModuleCat.{u} B ⥤ ModuleCat.{u} R :=
    ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso R).inv.hom
  have : PreservesFiniteLimits F :=
    SheafOfModules.Finite.evaluationPreservesFiniteLimits.{u} (Spec R).ringCatSheaf (op U)
  have : PreservesFiniteLimits G := restrictScalars_preservesFiniteLimits_native
    ((Spec R).ringCatSheaf.obj.map
      ((initialOpOfTerminal isTerminalTop).to (op U))).hom
  have : PreservesFiniteLimits H :=
    restrictScalars_preservesFiniteLimits_native (Scheme.ΓSpecIso R).inv.hom
  have : PreservesFiniteLimits (G ⋙ H) := comp_preservesFiniteLimits G H
  exact comp_preservesFiniteLimits F (G ⋙ H)

private abbrev affineSectionFunctor (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    (Spec R).Modules ⥤ ModuleCat.{u} R where
  obj M := (affineModulePresheaf M).obj (op U)
  map φ := (affineModuleMap φ).app (op U)
  map_id _ := rfl
  map_comp _ _ := rfl

private def nativeAffineSectionFunctorIso
    (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    nativeAffineSectionFunctor R U ≅ affineSectionFunctor R U :=
  NatIso.ofComponents (fun M => Iso.refl _) (by
    intro M N φ
    rfl)

private instance affineSectionFunctor_preservesFiniteLimits
    (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    PreservesFiniteLimits (affineSectionFunctor R U) :=
  preservesFiniteLimits_of_natIso (nativeAffineSectionFunctorIso R U)

private instance affineSectionFunctor_preservesZeroMorphisms
    (R : CommRingCat.{u}) (U : (Spec R).Opens) :
    (affineSectionFunctor R U).PreservesZeroMorphisms where
  map_zero _ _ := rfl

private def sectionKernel {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (φ : M ⟶ N) (U : (Spec R).Opens) : ModuleCat.{u} R :=
  ModuleCat.of R ((affineModuleMap φ).app (op U)).hom.ker

private def kernelSectionIso {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    {φ : M ⟶ N} (c : KernelFork φ) (hc : IsLimit c) (U : (Spec R).Opens) :
    (affineSectionFunctor R U).obj c.pt ≅
      sectionKernel φ U :=
  (c.mapIsLimit hc (affineSectionFunctor R U)).conePointUniqueUpToIso
    (ModuleCat.kernelIsLimit ((affineSectionFunctor R U).map φ))

private lemma kernelSectionIso_comp_subtype
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    {φ : M ⟶ N} (c : KernelFork φ) (hc : IsLimit c) (U : (Spec R).Opens) :
    (kernelSectionIso c hc U).hom ≫
      ModuleCat.ofHom ((affineSectionFunctor R U).map φ).hom.ker.subtype =
        (affineSectionFunctor R U).map c.ι :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (c.mapIsLimit hc (affineSectionFunctor R U))
    (ModuleCat.kernelIsLimit ((affineSectionFunctor R U).map φ)) WalkingParallelPair.zero

private lemma kernelSectionIso_hom_apply_val
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    {φ : M ⟶ N} (c : KernelFork φ) (hc : IsLimit c) (U : (Spec R).Opens)
    (x : (affineSectionFunctor R U).obj c.pt) :
    ((kernelSectionIso c hc U).hom.hom x).val =
      ((affineSectionFunctor R U).map c.ι).hom x :=
  congrArg (fun f => f.hom x) (kernelSectionIso_comp_subtype c hc U)

private lemma sectionRestriction_square
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (φ : M ⟶ N) {U V : (Spec R).Opens} (i : U ⟶ V) :
    ((affineSectionFunctor R U).map φ).hom.comp
        ((affineModulePresheaf M).map i.op).hom =
      ((affineModulePresheaf N).map i.op).hom.comp
        ((affineSectionFunctor R V).map φ).hom := by
  exact congrArg ModuleCat.Hom.hom ((affineModuleMap φ).naturality i.op)

private def sectionKernelRestriction
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (φ : M ⟶ N) {U V : (Spec R).Opens} (i : U ⟶ V) :
    sectionKernel φ V ⟶ sectionKernel φ U :=
  ModuleCat.ofHom (LinearMap.kernelRestriction
    ((affineModulePresheaf M).map i.op).hom
    ((affineModulePresheaf N).map i.op).hom
    ((affineSectionFunctor R V).map φ).hom
    ((affineSectionFunctor R U).map φ).hom (sectionRestriction_square φ i))

private lemma kernelSectionIso_restriction
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    {φ : M ⟶ N} (c : KernelFork φ) (hc : IsLimit c) {U V : (Spec R).Opens} (i : U ⟶ V) :
    (affineModulePresheaf c.pt).map i.op ≫ (kernelSectionIso c hc U).hom =
      (kernelSectionIso c hc V).hom ≫ sectionKernelRestriction φ i := by
  ext x
  apply Subtype.ext
  change ((kernelSectionIso c hc U).hom.hom
      (((affineModulePresheaf c.pt).map i.op).hom x)).val =
    ((affineModulePresheaf M).map i.op).hom
      ((kernelSectionIso c hc V).hom.hom x).val
  rw [kernelSectionIso_hom_apply_val, kernelSectionIso_hom_apply_val]
  exact congrArg (fun f => f.hom x) ((affineModuleMap c.ι).naturality i.op)

private theorem sectionKernelRestriction_localizes
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (φ : M ⟶ N) {U V : (Spec R).Opens} (i : U ⟶ V) (S : Submonoid R)
    (hM : IsLocalizedModule S ((affineModulePresheaf M).map i.op).hom)
    (hN : IsLocalizedModule S ((affineModulePresheaf N).map i.op).hom) :
    IsLocalizedModule S (sectionKernelRestriction φ i).hom := by
  have : IsLocalizedModule S ((affineModulePresheaf M).map i.op).hom := hM
  have : IsLocalizedModule S ((affineModulePresheaf N).map i.op).hom := hN
  exact LinearMap.isLocalizedModule_kernelRestriction S
    ((affineModulePresheaf M).map i.op).hom
    ((affineModulePresheaf N).map i.op).hom
    ((affineSectionFunctor R V).map φ).hom
    ((affineSectionFunctor R U).map φ).hom (sectionRestriction_square φ i)

private theorem kernelForkRestriction_localizes
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    {φ : M ⟶ N} (c : KernelFork φ) (hc : IsLimit c)
    {U V : (Spec R).Opens} (i : U ⟶ V) (S : Submonoid R)
    (hM : IsLocalizedModule S ((affineModulePresheaf M).map i.op).hom)
    (hN : IsLocalizedModule S ((affineModulePresheaf N).map i.op).hom) :
    IsLocalizedModule S ((affineModulePresheaf c.pt).map i.op).hom :=
  isLocalizedModule_of_commuting_isos S (kernelSectionIso c hc V)
    (kernelSectionIso c hc U) ((affineModulePresheaf c.pt).map i.op)
    (sectionKernelRestriction φ i) (kernelSectionIso_restriction c hc i)
    (sectionKernelRestriction_localizes φ i S hM hN)

private theorem isLocalizing_of_affineModulePresheaf
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (h : ∀ r : R, IsLocalizedModule (Submonoid.powers r)
      ((affineModulePresheaf M).map (affineBasicOpenInclusion R r).op).hom) :
    IsLocalizing (modulesSpecToSheaf.obj M) := h

private theorem affineModulePresheaf_localizes_of_isLocalizing
    {R : CommRingCat.{u}} (M : (Spec R).Modules)
    (hM : IsLocalizing (modulesSpecToSheaf.obj M)) (r : R) :
    IsLocalizedModule (Submonoid.powers r)
      ((affineModulePresheaf M).map (affineBasicOpenInclusion R r).op).hom :=
  hM r

private theorem isLocalizing_of_limitKernelFork
    {R : CommRingCat.{u}} {M N : (Spec R).Modules} {φ : M ⟶ N}
    (c : KernelFork φ) (hc : IsLimit c)
    (hM : IsLocalizing (modulesSpecToSheaf.obj M))
    (hN : IsLocalizing (modulesSpecToSheaf.obj N)) :
    IsLocalizing (modulesSpecToSheaf.obj c.pt) :=
  isLocalizing_of_affineModulePresheaf (R := R) c.pt fun r =>
    kernelForkRestriction_localizes (R := R) (M := M) (N := N) (φ := φ) c hc
      (U := affineBasicOpen R r) (V := ⊤)
      (affineBasicOpenInclusion R r) (Submonoid.powers r)
      (affineModulePresheaf_localizes_of_isLocalizing (R := R) M hM r)
      (affineModulePresheaf_localizes_of_isLocalizing (R := R) N hN r)

/-- Kernels of morphisms between actual localizing modules have localizing
sections. Evaluation of the canonical kernel fork supplies the kernel
comparison; no sectionwise identification is a premise. -/
theorem isLocalizing_kernel_toSpec
    {R : CommRingCat.{u}} {M N : (Spec R).Modules} (φ : M ⟶ N)
    (hM : IsLocalizing (modulesSpecToSheaf.obj M))
    (hN : IsLocalizing (modulesSpecToSheaf.obj N)) :
    IsLocalizing (modulesSpecToSheaf.obj (kernel φ)) :=
  isLocalizing_of_limitKernelFork (R := R) (M := M) (N := N) (φ := φ)
    (KernelFork.ofι (f := φ) (kernel.ι φ) (kernel.condition φ)) (kernelIsKernel φ) hM hN

/-- The actual kernel of a morphism between quasicoherent modules on an
affine scheme is quasicoherent. -/
theorem isQuasicoherent_kernel_toSpec
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    (kernel φ).IsQuasicoherent := by
  apply (isQuasicoherent_iff_isIso_fromTildeΓ (kernel φ)).mpr
  apply (isIso_fromTildeΓ_iff_isLocalizing (kernel φ)).mpr
  exact isLocalizing_kernel_toSpec φ
    ((isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance)
    ((isIso_fromTildeΓ_iff_isLocalizing N).mp inferInstance)

end AlgebraicGeometry.Scheme.Modules
