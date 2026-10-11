/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.SubmoduleRestrictedSections
import Nyll.SchemeTheory.Modules.KernelSubmoduleRestriction
import Nyll.SchemeTheory.Modules.FiniteTypeSchemeRestriction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Actual quasicoherent extensions containing finite local section families

The finite free image on an open subscheme is inserted into the actual
quotient-kernel construction. Its restriction is the original image, so
the extension is finite type on that open and contains the original
specified sections there. These are the actual inputs for the global
finite-type extraction theorem.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- Finitely many sections on a quasi-compact open belong to a global
quasicoherent submodule which is finite type on that open. -/
theorem exists_quasicoherent_submodule_finiteType_over_containing_sections
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] (U : X.Opens)
    [QuasiCompact U.ι] {I : Type u} [Finite I] (s : I → F.val.obj (op U)) :
    ∃ H : F.Submodule, H.toSheafOfModules.IsQuasicoherent ∧
      (H.toSheafOfModules.over U).IsFiniteType ∧
      ∀ i : I, s i ∈ H.toSubmodule.obj (op U) := by
  obtain ⟨N, hNQC, hNFT, hN⟩ :=
    exists_finiteType_restriction_submodule_lifting_sections F U s
  let E := sheafOfModulesEquivalence U.toScheme
  let G : U.toScheme.Modules := E.inverse.obj N.toSheafOfModules
  let φ : G ⟶ F.restrict U.ι := E.inverse.map N.ι
  have : G.IsQuasicoherent := hNQC
  have hMonoN : Mono (C := SheafOfModules.{u} U.toScheme.ringCatSheaf) N.ι :=
    (SheafOfModules.forget U.toScheme.ringCatSheaf).mono_of_mono_map
      (PresheafOfModules.mono_of_injective (fun _ => Subtype.val_injective))
  have : Mono (C := U.toScheme.Modules) φ := Functor.map_mono E.inverse N.ι
  let ψ := submoduleExtensionMap U.ι F φ
  let H : F.Submodule := kernelSubmodule ψ
  let e : (submoduleAsModule H).restrict U.ι ≅ G :=
    kernelSubmoduleExtensionRestrictIso U.ι F φ
  have hHQC : H.toSheafOfModules.IsQuasicoherent := by
    have hKer : (kernel ψ).IsQuasicoherent :=
      isQuasicoherent_kernel_submoduleExtensionMap U.ι F φ
    have hKerNative : ((sheafOfModulesEquivalence X).functor.obj
        (kernel ψ)).IsQuasicoherent := hKer
    exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (kernelSubmoduleIso ψ).symm hKerNative
  have hRestrFT : ((submoduleAsModule H).restrict U.ι).IsFiniteType := by
    let eNative : E.functor.obj G ≅ E.functor.obj ((submoduleAsModule H).restrict U.ι) :=
      E.functor.mapIso e.symm
    exact SheafOfModules.IsFiniteType.of_iso
      (C := U.toScheme.Opens) (R := U.toScheme.ringCatSheaf)
      (M := E.functor.obj G)
      (N := E.functor.obj ((submoduleAsModule H).restrict U.ι)) eNative hNFT
  have hHFT : (H.toSheafOfModules.over U).IsFiniteType :=
    isFiniteType_over_of_restrict (submoduleAsModule H) U hRestrFT
  refine ⟨H, hHQC, hHFT, ?_⟩
  intro i
  obtain ⟨t, ht⟩ := hN i
  let tG : Γ(G, ⊤) := t
  let z : Γ((submoduleAsModule H).restrict U.ι, ⊤) := e.inv.app ⊤ tG
  have he : e.hom ≫ φ =
      (restrictFunctor U.ι).map (submoduleAsModuleInclusion H) :=
    kernelSubmoduleExtensionRestrictIso_hom_ι U.ι F φ
  have hLift : e.inv ≫ (restrictFunctor U.ι).map (submoduleAsModuleInclusion H) = φ :=
    (Iso.inv_comp_eq e).2 he.symm
  apply mem_submodule_of_restrict_lift H U (s i) z
  exact (congrArg (fun f : G ⟶ F.restrict U.ι =>
    (openTopSectionsIso F U).hom (f.app ⊤ tG)) hLift).trans ht

end AlgebraicGeometry.Scheme.Modules
