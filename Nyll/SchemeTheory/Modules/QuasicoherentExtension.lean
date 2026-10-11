/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.QuasicoherentKernelGlobal
import Nyll.SchemeTheory.Modules.QuasicoherentCokernel
import Nyll.SchemeTheory.Modules.QuasicoherentPushforward
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Extending actual quasicoherent subobjects across a quasi-compact open

For a monomorphism `φ : G ⟶ F|U`, the extension is the actual kernel of
`F ⟶ j_*coker φ`. The restriction adjunction identifies this kernel over
`U` with `G`, and the identification respects the given inclusion in `F|U`.

This is the geometric kernel construction for Stacks, Tag 01PE(2).
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- The actual map to the direct image of the quotient by a local subobject. -/
def submoduleExtensionMap {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) {G : U.Modules} (φ : G ⟶ F.restrict j) :
    F ⟶ (pushforward j).obj (cokernel φ) :=
  (restrictAdjunction j).unit.app F ≫ (pushforward j).map (cokernel.π φ)

theorem submoduleExtensionMap_restrict_counit
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) {G : U.Modules} (φ : G ⟶ F.restrict j) :
    (restrictFunctor j).map (submoduleExtensionMap j F φ) ≫
      (restrictAdjunction j).counit.app (cokernel φ) = cokernel.π φ := by
  calc
    (restrictFunctor j).map (submoduleExtensionMap j F φ) ≫
        (restrictAdjunction j).counit.app (cokernel φ) =
      (restrictFunctor j).map ((restrictAdjunction j).unit.app F) ≫
        ((restrictFunctor j).map ((pushforward j).map (cokernel.π φ)) ≫
          (restrictAdjunction j).counit.app (cokernel φ)) := by
            rw [submoduleExtensionMap, Functor.map_comp, Category.assoc]
    _ = (restrictFunctor j).map ((restrictAdjunction j).unit.app F) ≫
        ((restrictAdjunction j).counit.app (F.restrict j) ≫ cokernel.π φ) := by
          exact congrArg
            (fun k => (restrictFunctor j).map ((restrictAdjunction j).unit.app F) ≫ k)
            ((restrictAdjunction j).counit.naturality (cokernel.π φ))
    _ = cokernel.π φ := by
      rw [← Category.assoc, (restrictAdjunction j).left_triangle_components F]
      exact Category.id_comp (cokernel.π φ)

private def monoCokernelKernelIso
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) [Mono φ] :
    kernel (cokernel.π φ) ≅ M :=
  (limit.isLimit (parallelPair (cokernel.π φ) 0)).conePointUniqueUpToIso
    (Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ (cokernel.π φ) (cokernel.condition φ)) (cokernelIsCokernel φ))

private theorem monoCokernelKernelIso_hom_ι
    {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) [Mono φ] :
    (monoCokernelKernelIso φ).hom ≫ φ = kernel.ι (cokernel.π φ) :=
  IsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit (parallelPair (cokernel.π φ) 0))
    (Abelian.monoIsKernelOfCokernel
      (CokernelCofork.ofπ (cokernel.π φ) (cokernel.condition φ))
      (cokernelIsCokernel φ)) WalkingParallelPair.zero

/-- Restricting the actual kernel extension recovers the original monomorphism's source. -/
def submoduleExtensionRestrictIso
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) {G : U.Modules} (φ : G ⟶ F.restrict j) [Mono φ] :
    (kernel (submoduleExtensionMap j F φ)).restrict j ≅ G := by
  have : PreservesFiniteLimits (restrictFunctor j) := preservesFiniteLimits_restrictFunctor j
  have : (restrictFunctor j).PreservesZeroMorphisms :=
    { map_zero := fun _ _ => rfl }
  have : IsIso (C := U.Modules) ((restrictAdjunction j).counit.app (cokernel φ)) :=
    inferInstance
  let ε : (restrictFunctor j).obj ((pushforward j).obj (cokernel φ)) ≅ cokernel φ :=
    asIso (C := U.Modules) ((restrictAdjunction j).counit.app (cokernel φ))
  have hε : (restrictFunctor j).map (submoduleExtensionMap j F φ) ≫ ε.hom =
      (Iso.refl (F.restrict j)).hom ≫ cokernel.π φ := by
    change (restrictFunctor j).map (submoduleExtensionMap j F φ) ≫
      (restrictAdjunction j).counit.app (cokernel φ) = 𝟙 (F.restrict j) ≫ cokernel.π φ
    rw [Category.id_comp]
    exact submoduleExtensionMap_restrict_counit j F φ
  exact PreservesKernel.iso (restrictFunctor j) (submoduleExtensionMap j F φ) ≪≫
    kernel.mapIso ((restrictFunctor j).map (submoduleExtensionMap j F φ))
      (cokernel.π φ) (Iso.refl (F.restrict j)) ε hε ≪≫ monoCokernelKernelIso φ

/-- The restriction identification preserves the actual inclusions into `F|U`. -/
theorem submoduleExtensionRestrictIso_hom_ι
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : X.Modules) {G : U.Modules} (φ : G ⟶ F.restrict j) [Mono φ] :
    (submoduleExtensionRestrictIso j F φ).hom ≫ φ =
      (restrictFunctor j).map (kernel.ι (submoduleExtensionMap j F φ)) := by
  simp only [submoduleExtensionRestrictIso, Iso.trans_hom, Category.assoc,
    monoCokernelKernelIso_hom_ι, kernel.mapIso_hom, kernel.map, kernel.lift_ι,
    Iso.refl_hom, Category.comp_id, PreservesKernel.iso_hom, kernelComparison_comp_ι]

/-- The actual kernel extension is quasicoherent when the open immersion
is quasi-compact and both original modules are quasicoherent. -/
theorem isQuasicoherent_kernel_submoduleExtensionMap
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (F : X.Modules) [F.IsQuasicoherent] {G : U.Modules} [G.IsQuasicoherent]
    (φ : G ⟶ F.restrict j) :
    (kernel (submoduleExtensionMap j F φ)).IsQuasicoherent := by
  have : (F.restrict j).IsQuasicoherent := isQuasicoherent_restrictFunctor j F
  have : (cokernel φ).IsQuasicoherent :=
    isQuasicoherent_cokernel (X := U) (M := G) (N := F.restrict j) φ
  have : ((pushforward j).obj (cokernel φ)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_quasiCompact_openImmersion j (cokernel φ)
  exact isQuasicoherent_kernel (X := X) (M := F)
    (N := (pushforward j).obj (cokernel φ)) (submoduleExtensionMap j F φ)

end AlgebraicGeometry.Scheme.Modules
