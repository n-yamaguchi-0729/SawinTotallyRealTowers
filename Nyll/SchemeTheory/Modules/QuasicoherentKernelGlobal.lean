/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.QuasicoherentKernel
import Nyll.SchemeTheory.Modules.QuasicoherentLocal
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.Topology.Sheaves.Module
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Quasicoherence of kernels on schemes

Restriction preserves the actual categorical kernel. Affine kernel
quasicoherence supplies the hypotheses of the shared affine-presentation
criterion, which constructs the global quasicoherent data.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Restriction along an open immersion preserves finite limits, by the
actual native sheaf pushforward adjunction defining the restriction. -/
theorem preservesFiniteLimits_restrictFunctor
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    PreservesFiniteLimits (restrictFunctor f) := by
  let α : X.presheaf ⟶ f.opensFunctor.op ⋙ Y.presheaf :=
    { app U := (f.appIso U.unop).inv }
  let ρ : X.ringCatSheaf ⟶
      (f.opensFunctor.sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y)).obj Y.ringCatSheaf :=
    ⟨Functor.whiskerRight α (forget₂ CommRingCat RingCat)⟩
  have : (PresheafOfModules.pushforward.{u} (F := f.opensFunctor) ρ.hom).IsRightAdjoint :=
    Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
      (PresheafOfModules.pullbackObjIsDefined_eq_top
        (C := X.Opens) (D := Y.Opens) (F := f.opensFunctor)
        (R := Y.ringCatSheaf.obj) (S := X.ringCatSheaf.obj) ρ.hom)
  have : PreservesLimitsOfSize.{u, u} (SheafOfModules.pushforward.{u} ρ) :=
    (SheafOfModules.PullbackConstruction.adjunction.{u}
      (F := f.opensFunctor) (R := Y.ringCatSheaf)
      (S := X.ringCatSheaf) ρ).rightAdjoint_preservesLimits
  exact PreservesLimitsOfSize.preservesFiniteLimits (SheafOfModules.pushforward.{u} ρ)

private instance restrictFunctor_preservesZeroMorphisms_kernel
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] :
    (restrictFunctor f).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- The actual categorical kernel of any morphism of quasicoherent
modules on a scheme is quasicoherent. No separation or compactness
assumption is needed. -/
theorem isQuasicoherent_kernel
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    (kernel φ).IsQuasicoherent := by
  apply isQuasicoherent_of_affineSpecRestrictions (kernel φ)
  intro U hU
  let F : X.Modules ⥤ (Spec Γ(X, U)).Modules := restrictFunctor hU.fromSpec
  have : (F.obj M).IsQuasicoherent :=
    isQuasicoherent_restrictFunctor hU.fromSpec M
  have : (F.obj N).IsQuasicoherent :=
    isQuasicoherent_restrictFunctor hU.fromSpec N
  have : PreservesFiniteLimits F :=
    preservesFiniteLimits_restrictFunctor hU.fromSpec
  have : F.PreservesZeroMorphisms :=
    restrictFunctor_preservesZeroMorphisms_kernel hU.fromSpec
  have hK : (kernel (F.map φ)).IsQuasicoherent :=
    isQuasicoherent_kernel_toSpec (R := Γ(X, U)) (M := F.obj M) (N := F.obj N) (F.map φ)
  let e := (sheafOfModulesEquivalence (Spec Γ(X, U))).functor.mapIso
    (PreservesKernel.iso F φ).symm
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso e hK

end AlgebraicGeometry.Scheme.Modules
