/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.AffineSubmoduleLocalization
import Nyll.SchemeTheory.Modules.AffineOpenModuleEpi
import Nyll.SchemeTheory.Modules.ImageSubmoduleRestriction
import Nyll.SchemeTheory.RingTheory.LocalizedSubmoduleComparison
import Nyll.SchemeTheory.RingTheory.ModuleFiniteLocalizationModel

/-!
# Finite-type extraction on finitely many principal opens

Starting with an actual quasicoherent native submodule, extract finitely
many global numerator sections using the existing finite localization
theorem. Their actual affine tilde morphism has full range on the specified
principal opens. Its image inside the original ambient module is therefore
a finite-type quasicoherent submodule with exactly the prescribed local
restrictions. The principal opens need not cover the whole spectrum.

This is the affine extraction step of Stacks Tag 01PF, after Tag 01PE has
supplied the actual quasicoherent extension.
-/

noncomputable section

universe u v

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

/-- An actual quasicoherent submodule with finitely generated localizations
on finitely many principal opens admits a finite-type quasicoherent
submodule agreeing on all those opens. -/
theorem exists_finiteType_submodule_eq_on_basicOpens {R : CommRingCat.{u}}
    (F : SheafOfModules.{u} (Spec R).ringCatSheaf) [F.IsQuasicoherent] (H : F.Submodule)
    [H.toSheafOfModules.IsQuasicoherent]
    {ι : Type v} [Finite ι] (r : ι → R)
    (hFinite : ∀ i : ι,
      ((⊤ : Submodule R ((moduleSpecΓFunctor (R := R)).obj
        ((sheafOfModulesEquivalence (Spec R)).inverse.obj H.toSheafOfModules))).localized
          (Submonoid.powers (r i))).FG) :
    ∃ N : F.Submodule, N ≤ H ∧ N.toSheafOfModules.IsQuasicoherent ∧
      N.toSheafOfModules.IsFiniteType ∧
      ∀ i : ι, N.over (PrimeSpectrum.basicOpen (r i)) =
        H.over (PrimeSpectrum.basicOpen (r i)) := by
  let E := sheafOfModulesEquivalence (Spec R)
  let G : (Spec R).Modules := E.inverse.obj H.toSheafOfModules
  have : G.IsQuasicoherent := inferInstanceAs H.toSheafOfModules.IsQuasicoherent
  let M : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj G
  obtain ⟨K, hKFinite, _hKle, hKlocal⟩ :=
    Submodule.exists_fg_le_localized_eq_finite r (⊤ : Submodule R M) hFinite
  have : Module.Finite R K := Module.Finite.of_fg hKFinite
  let A : SheafOfModules.{u} (Spec R).ringCatSheaf := tilde (ModuleCat.of R K)
  let φ : (tilde.functor R).obj (ModuleCat.of R K) ⟶ G := affineSubmoduleMap G K
  let f : A ⟶ H.toSheafOfModules := E.functor.map φ
  let N : F.Submodule := SheafOfModules.imageSubmodule (f ≫ H.ι)
  have : A.IsQuasicoherent := inferInstanceAs (tilde (ModuleCat.of R K)).IsQuasicoherent
  have : A.IsFiniteType := isFiniteType_tilde_of_finite (ModuleCat.of R K)
  refine ⟨N, SheafOfModules.imageSubmodule_le (f ≫ H.ι) H f rfl,
    SheafOfModules.isQuasicoherent_imageSubmodule (f ≫ H.ι),
    SheafOfModules.isFiniteType_imageSubmodule (f ≫ H.ι), ?_⟩
  intro i
  let U : (Spec R).Opens := PrimeSpectrum.basicOpen (R := R) (r i)
  let P : (Spec R).Opensᵒᵖ ⥤ ModuleCat.{u} R := (modulesSpecToSheaf.obj G).obj
  let b : M →ₗ[R] P.obj (op U) := (P.map U.leTop.op).hom
  have : IsLocalizedModule (Submonoid.powers (r i)) b :=
    ((isIso_fromTildeΓ_iff_isLocalizing G).mp inferInstance) (r i)
  have hKtop : K.localized (Submonoid.powers (r i)) = ⊤ := by
    simpa only [Submodule.localized, Submodule.localized'_top] using hKlocal i
  have hRange : ((modulesSpecToSheaf.map φ).hom.app (op U)).hom.range = ⊤ :=
    (affineSubmoduleMap_basicOpen_range G K (r i)).trans
      (Submodule.localized₀_eq_top_of_localized_eq_top
        (Submonoid.powers (r i)) K b hKtop)
  have hSurjR : Function.Surjective
      ((modulesSpecToSheaf.map φ).hom.app (op U)).hom :=
    LinearMap.range_eq_top.mp hRange
  have hSurj : Function.Surjective (φ.app U) := hSurjR
  have : Epi (f.over U) :=
    epi_over_of_surjective_app φ U (IsAffineOpen.Spec_basicOpen (r i)) hSurj
  exact SheafOfModules.imageSubmodule_over_eq_of_epi H f U

end AlgebraicGeometry.Scheme.Modules
