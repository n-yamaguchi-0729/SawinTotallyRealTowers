/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteGeneratingSections
import Nyll.SchemeTheory.Modules.SectionLocalization
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.Topology.Sheaves.Module
import Mathlib.RingTheory.Localization.Finiteness

/-!
# Affine sections of finite-type quasicoherent modules

The actual local finite generators restrict to every subordinate affine
open. Their free epimorphisms yield finite section modules there. Basic
opens subordinate to the given generator cover span the unit ideal of
an affine chart, and the native section-localization maps allow the
existing finite-localization theorem to extract finitely many generators.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private theorem finite_sections_of_finite_spec_restriction
    {X : Scheme.{u}} (M : X.Modules) {R : CommRingCat.{u}}
    (j : Spec R ⟶ X) [IsOpenImmersion j]
    [Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (M.restrict j))] :
    Module.Finite Γ(X, j ''ᵁ ⊤) Γ(M, j ''ᵁ ⊤) := by
  let N : (Spec R).Modules := M.restrict j
  let σ : R →+* Γ(X, j ''ᵁ ⊤) :=
    (((Scheme.ΓSpecIso R).inv) ≫ (j.appIso ⊤).inv).hom
  let e : Γ(N, ⊤) ≅ Γ(M, j ''ᵁ ⊤) := M.restrictAppIso j ⊤
  have : Module.Finite R Γ(N, ⊤) :=
    inferInstanceAs (Module.Finite R ((moduleSpecΓFunctor (R := R)).obj (M.restrict j)))
  let l : Γ(N, ⊤) →ₛₗ[σ] Γ(M, j ''ᵁ ⊤) :=
    { toAddHom := e.hom.hom.toAddHom
      map_smul' := by
        intro r x
        have hid : (Spec R).presheaf.map (⊤ : (Spec R).Opens).leTop.op = 𝟙 _ := by
          rw [Subsingleton.elim (⊤ : (Spec R).Opens).leTop (𝟙 _), op_id,
            CategoryTheory.Functor.map_id]
        have hscalar : r • x = (Scheme.ΓSpecIso R).inv r • x := by
          rw [smul_Spec_def, hid]
          rfl
        rw [hscalar]
        exact congrArg (fun k : Γ(N, ⊤) ⟶ Γ(M, j ''ᵁ ⊤) => k x)
          (M.smul_restrictAppIso_hom j ⊤ ((Scheme.ΓSpecIso R).inv r)) }
  apply Module.Finite.of_surjective l
  intro y
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso e.hom).surjective y
  exact ⟨x, hx⟩

/-- Finite actual generators over an open set give a finite module of
sections over each subordinate affine open. -/
theorem moduleFinite_sections_of_generatingSections_over
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    {U W : X.Opens} (hU : IsAffineOpen U) (hUW : U ≤ W)
    (G : (M.over W).GeneratingSections) [G.IsFiniteType] :
    Module.Finite Γ(X, U) Γ(M, U) := by
  let S : Scheme.{u} := Spec Γ(X, U)
  let j : S ⟶ W.toScheme := hU.isoSpec.inv ≫ X.homOfLE hUW
  have hj : j ≫ W.ι = hU.fromSpec := by
    exact (Category.assoc hU.isoSpec.inv (X.homOfLE hUW) W.ι).trans
      ((congrArg (fun k : U.toScheme ⟶ X => hU.isoSpec.inv ≫ k)
        (X.homOfLE_ι hUW)).trans hU.isoSpec_inv_ι)
  let E := sheafOfModulesEquivalence S
  let F : SheafOfModules.{u} (X.ringCatSheaf.over W) ⥤
      SheafOfModules.{u} S.ringCatSheaf :=
    (overEquiv W).functor ⋙ restrictFunctor j ⋙ E.functor
  have : PreservesColimitsOfSize.{u, u} (overEquiv W).functor :=
    (overEquiv W).toAdjunction.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u} (restrictFunctor j) :=
    (restrictAdjunction j).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u} E.functor :=
    E.toAdjunction.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u} F := inferInstance
  let eUnit : (overEquiv W).functor.obj
      (SheafOfModules.unit (X.ringCatSheaf.over W)) ≅
      (show W.toScheme.Modules from SheafOfModules.unit W.toScheme.ringCatSheaf) :=
    (sheafOfModulesEquivalence W.toScheme).inverse.mapIso
      (W.sheafOfModulesEquivOverUnit X.ringCatSheaf)
  let η : SheafOfModules.unit S.ringCatSheaf ≅
      F.obj (SheafOfModules.unit (X.ringCatSheaf.over W)) :=
    (E.functor.mapIso ((restrictFunctor j).mapIso eUnit ≪≫ restrictUnitIso j)).symm
  let eM : (restrictFunctor j).obj ((overEquiv W).functor.obj (M.over W)) ≅
      M.restrict hU.fromSpec :=
    (restrictFunctor j).mapIso ((overFunctorEquiv W).app M) ≪≫
      ((restrictFunctorComp j W.ι).app M).symm ≪≫ (restrictFunctorCongr hj).app M
  let eNative : F.obj (M.over W) ≅
      (show SheafOfModules.{u} S.ringCatSheaf from M.restrict hU.fromSpec) :=
    E.functor.mapIso eM
  have : IsIso (C := SheafOfModules.{u} S.ringCatSheaf) eNative.hom := eNative.isIso_hom
  have : Epi (C := SheafOfModules.{u} S.ringCatSheaf) eNative.hom :=
    CategoryTheory.IsIso.epi_of_iso (C := SheafOfModules.{u} S.ringCatSheaf) eNative.hom
  have : Finite G.I := SheafOfModules.GeneratingSections.IsFiniteType.finite (σ := G)
  let H := (G.map F η).ofEpi eNative.hom
  have : H.IsFiniteType := ⟨inferInstanceAs (Finite G.I)⟩
  have : Module.Finite Γ(X, U)
      ((moduleSpecΓFunctor (R := Γ(X, U))).obj (M.restrict hU.fromSpec)) :=
    moduleFinite_moduleSpecΓ_of_generatingSections (M.restrict hU.fromSpec) H
  have hfinite : Module.Finite Γ(X, hU.fromSpec ''ᵁ ⊤) Γ(M, hU.fromSpec ''ᵁ ⊤) :=
    finite_sections_of_finite_spec_restriction M hU.fromSpec
  have hImage : hU.fromSpec ''ᵁ ⊤ = U :=
    hU.fromSpec.image_top_eq_opensRange.trans hU.opensRange_fromSpec
  exact Eq.mp (congrArg (fun V : X.Opens => Module.Finite Γ(X, V) Γ(M, V)) hImage) hfinite

/-- A finite-type quasicoherent module has a finite module of sections on
every affine open, with the original coefficient ring and section action. -/
theorem moduleFinite_sections_of_isFiniteType
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] [M.IsFiniteType]
    (U : X.Opens) (hU : IsAffineOpen U) : Module.Finite Γ(X, U) Γ(M, U) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  have hCover : IsOpenCover q.X := (Opens.coversTop_iff X q.X).mp q.coversTop
  let s : Set Γ(X, U) := {r | ∃ i : q.I, X.basicOpen r ≤ q.X i}
  have hs : Ideal.span s = ⊤ := by
    apply hU.self_le_iSup_basicOpen_iff.mp
    intro x hx
    obtain ⟨i, hi⟩ := hCover.exists_mem x
    obtain ⟨r, hr, hxr⟩ := hU.exists_basicOpen_le ⟨x, hi⟩ hx
    exact Opens.mem_iSup.mpr ⟨⟨r, i, hr⟩, hxr⟩
  let R : CommRingCat.{u} := Γ(X, U)
  let Rp (r : s) : CommRingCat.{u} := Γ(X, X.basicOpen r.1)
  let σ (r : s) : R →+* Rp r :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r.1)).op).hom
  let (r : s) : Algebra R (Rp r) := (σ r).toAlgebra
  let Mp (r : s) : ModuleCat.{u} (Rp r) := ModuleCat.of (Rp r) Γ(M, X.basicOpen r.1)
  let (r : s) : Module R (Mp r) := Module.compHom (Mp r) (σ r)
  have (r : s) : IsScalarTower R (Rp r) (Mp r) :=
    IsScalarTower.of_compHom R (Rp r) (Mp r)
  have (r : s) : IsLocalization.Away r.1 (Rp r) := hU.isLocalization_basicOpen r.1
  let l (r : s) : Γ(M, U) →ₗ[R] Mp r :=
    (M.val.map (homOfLE (X.basicOpen_le r.1)).op).hom
  have (r : s) : IsLocalizedModule.Away r.1 (l r) :=
    isLocalizedModule_basicOpen_of_isQuasicoherent_of_qcqs M
      hU.isCompact hU.isQuasiSeparated r.1
  apply Module.Finite.of_localizationSpan' s hs
    (Rₚ := fun r => Rp r) (Mₚ := fun r => Mp r) l
  intro r
  obtain ⟨i, hi⟩ := r.2
  have : (q.generators i).IsFiniteType := hq.isFiniteType i
  exact moduleFinite_sections_of_generatingSections_over M (hU.basicOpen r.1) hi
    (q.generators i)

/-- The affine-section finiteness statement for an actual native submodule. -/
theorem fg_sections_submodule_of_isFiniteType
    {X : Scheme.{u}} {M : X.Modules} (N : M.Submodule)
    [(show X.Modules from N.toSheafOfModules).IsQuasicoherent]
    [N.toSheafOfModules.IsFiniteType]
    (U : X.Opens) (hU : IsAffineOpen U) : (N.toSubmodule.obj (op U)).FG := by
  let R : RingCat.{u} := X.ringCatSheaf.obj.obj (op U)
  let P : Submodule R (M.val.obj (op U)) := N.toSubmodule.obj (op U)
  have hfinite : Module.Finite R P :=
    moduleFinite_sections_of_isFiniteType (show X.Modules from N.toSheafOfModules) U hU
  exact (Module.Finite.iff_fg (R := R) (N := P)).mp hfinite

end AlgebraicGeometry.Scheme.Modules
