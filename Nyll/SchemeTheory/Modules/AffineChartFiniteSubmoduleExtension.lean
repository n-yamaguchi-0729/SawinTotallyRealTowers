/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.AffineFiniteSubmoduleOnOpen
import Nyll.SchemeTheory.Modules.FiniteTypeSchemeRestriction
import Nyll.SchemeTheory.Modules.SubmoduleTopRestriction
import Nyll.SchemeTheory.Modules.KernelSubmoduleRestriction
import Nyll.SchemeTheory.Modules.QuasicoherentExtension
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Extending a finite quasicoherent submodule across one affine chart

The canonical spectrum of the affine chart supplies finite extraction on
the compact overlap. Its actual inclusion is transported back along the
affine isomorphism and extended by the kernel of the quotient direct image.
The resulting global subsheaf is finite type on the chart and agrees with
the original subsheaf on the entire overlap, as a native submodule.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

private def restrictFunctorAlongLEIso
    {X : Scheme.{u}} {U V : X.Opens} (h : U ≤ V) :
    restrictFunctor V.ι ⋙ restrictFunctor (X.homOfLE h) ≅ restrictFunctor U.ι :=
  (restrictFunctorComp (X.homOfLE h) V.ι).symm ≪≫
    restrictFunctorCongr (X.homOfLE_ι h)

private theorem finiteType_of_schemeIso
    {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) (hM : M.IsFiniteType) :
    N.IsFiniteType :=
  SheafOfModules.IsFiniteType.of_iso
    (C := X.Opens) (R := X.ringCatSheaf)
    (M := (sheafOfModulesEquivalence X).functor.obj M)
    (N := (sheafOfModulesEquivalence X).functor.obj N)
    ((sheafOfModulesEquivalence X).functor.mapIso e) hM

private theorem mono_submoduleAsModuleInclusion
    {X : Scheme.{u}} {F : X.Modules} (N : F.Submodule) :
    Mono (submoduleAsModuleInclusion N) := by
  have hn : Mono (C := SheafOfModules.{u} X.ringCatSheaf) N.ι :=
    (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
      (PresheafOfModules.mono_of_injective (fun _ => Subtype.val_injective))
  exact Functor.map_mono (sheafOfModulesEquivalence X).inverse N.ι

/-- Extend over one affine chart while retaining the exact original subsheaf
on the overlap with the compact open where it was already finite type. -/
theorem exists_finiteType_affineChart_extension
    {X : Scheme.{u}} [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] (N : F.Submodule)
    [N.toSheafOfModules.IsQuasicoherent]
    (T : X.Opens) (hT : IsCompact (T : Set X))
    (V : X.Opens) (hV : IsAffineOpen V)
    (hNft : (N.toSheafOfModules.over T).IsFiniteType) :
    ∃ P : F.Submodule, P.toSheafOfModules.IsQuasicoherent ∧
      (P.toSheafOfModules.over V).IsFiniteType ∧ P.over (T ⊓ V) = N.over (T ⊓ V) := by
  have : IsAffine V.toScheme := hV
  have : QuasiCompact V.ι := inferInstance
  let J : X.Opens := T ⊓ V
  let k : J.toScheme ⟶ V.toScheme := X.homOfLE (show J ≤ V from inf_le_right)
  let t : J.toScheme ⟶ T.toScheme := X.homOfLE (show J ≤ T from inf_le_left)
  let e : V.toScheme ≅ Spec Γ(X, V) := hV.isoSpec
  let f : Spec Γ(X, V) ⟶ X := hV.fromSpec
  let W : V.toScheme.Opens := V.ι ⁻¹ᵁ J
  let S : (Spec Γ(X, V)).Opens := e.inv ⁻¹ᵁ W
  let eJ : S.toScheme ≅ J.toScheme :=
    e.inv.preimageIso W ≪≫ Scheme.Opens.isoOfLE (show J ≤ V from inf_le_right)
  have hJ : IsCompact (J : Set X) :=
    hT.inter_of_isOpen hV.isCompact T.isOpen V.isOpen
  have hS : IsCompact (S : Set (Spec Γ(X, V))) :=
    e.inv.isCompact_preimage (V.ι.isCompact_preimage hJ)
  have hfac : eJ.hom ≫ J.ι = S.ι ≫ f := by
    dsimp only [eJ]
    rw [Iso.trans_hom, Category.assoc, Scheme.Opens.isoOfLE_hom_ι,
      ← Category.assoc, Scheme.Hom.preimageIso_hom_ι, Category.assoc]
    rfl
  let M : X.Modules := submoduleAsModule N
  let n : M ⟶ F := submoduleAsModuleInclusion N
  have : M.IsQuasicoherent := inferInstanceAs N.toSheafOfModules.IsQuasicoherent
  have hMT : (M.restrict T.ι).IsFiniteType := isFiniteType_restrict_of_over M T hNft
  have hMJ : (M.restrict J.ι).IsFiniteType :=
    finiteType_of_schemeIso ((restrictFunctorAlongLEIso (show J ≤ T from inf_le_left)).app M)
      (isFiniteType_restrictFunctor t (M.restrict T.ι) hMT)
  let A : (Spec Γ(X, V)).Modules := M.restrict f
  let A' : SheafOfModules.{u} (Spec Γ(X, V)).ringCatSheaf :=
    (sheafOfModulesEquivalence (Spec Γ(X, V))).functor.obj A
  let cs : restrictFunctor f ⋙ restrictFunctor S.ι ≅
      restrictFunctor J.ι ⋙ restrictFunctor eJ.hom :=
    (restrictFunctorComp S.ι f).symm ≪≫ restrictFunctorCongr hfac.symm ≪≫
      restrictFunctorComp eJ.hom J.ι
  have hAS : (A.restrict S.ι).IsFiniteType :=
    finiteType_of_schemeIso (cs.app M).symm
      (isFiniteType_restrictFunctor eJ.hom (M.restrict J.ι) hMJ)
  have hAover : (A'.over S).IsFiniteType := isFiniteType_over_of_restrict A S hAS
  let B : A'.Submodule := ⊤
  let b : B.toSheafOfModules ≅ A' := SheafOfModules.Submodule.topIso A'
  have hAqc : A'.IsQuasicoherent := isQuasicoherent_restrictFunctor f M
  have hBqc : B.toSheafOfModules.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(X, V)).ringCatSheaf).prop_of_iso b.symm hAqc
  have hBft : (B.toSheafOfModules.over S).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso
      (C := Over S) (R := (Spec Γ(X, V)).ringCatSheaf.over S)
      ((SheafOfModules.overFunctor (Spec Γ(X, V)).ringCatSheaf S).mapIso b.symm) hAover
  obtain ⟨Q, _, hQqc, hQft, hQeq⟩ :=
    exists_finiteType_submodule_eq_over_of_isCompact A' B S hS hBft
  let Qm : (Spec Γ(X, V)).Modules := submoduleAsModule (F := A) Q
  let q : Qm ⟶ A := submoduleAsModuleInclusion (F := A) Q
  have hq : Mono q := mono_submoduleAsModuleInclusion Q
  have hqS : IsIso ((restrictFunctor S.ι).map q) :=
    isIso_restrictSubmoduleInclusion_of_over_eq_top Q S hQeq
  have : Qm.IsQuasicoherent := hQqc
  let G : V.toScheme.Modules := Qm.restrict e.hom
  have hGqc : G.IsQuasicoherent := isQuasicoherent_restrictFunctor e.hom Qm
  have hGft : G.IsFiniteType := isFiniteType_restrictFunctor e.hom Qm hQft
  let cv : restrictFunctor f ⋙ restrictFunctor e.hom ≅ restrictFunctor V.ι :=
    (restrictFunctorComp e.hom f).symm ≪≫
      restrictFunctorCongr hV.isoSpec_hom_fromSpec
  let φ : G ⟶ M.restrict V.ι :=
    (restrictFunctor e.hom).map q ≫ (cv.app M).hom
  have : PreservesFiniteLimits (restrictFunctor e.hom) :=
    preservesFiniteLimits_restrictFunctor e.hom
  have : Mono ((restrictFunctor e.hom).map q) := Functor.map_mono _ q
  have : IsIso (C := V.toScheme.Modules) (cv.app M).hom := inferInstance
  have hφ : Mono φ := inferInstanceAs
    (Mono ((restrictFunctor e.hom).map q ≫ (cv.app M).hom))
  have hpre : eJ.inv ≫ S.ι ≫ f = J.ι := by
    rw [← hfac, Iso.inv_hom_id_assoc]
  have hpre' : (eJ.inv ≫ S.ι) ≫ e.inv = k := by
    apply (cancel_mono V.ι).mp
    calc
      ((eJ.inv ≫ S.ι) ≫ e.inv) ≫ V.ι = eJ.inv ≫ S.ι ≫ f := by
        rw [Category.assoc, Category.assoc]
        rfl
      _ = J.ι := hpre
      _ = k ≫ V.ι := (X.homOfLE_ι (show J ≤ V from inf_le_right)).symm
  have hrel : k ≫ e.hom = eJ.inv ≫ S.ι := by
    calc
      k ≫ e.hom = ((eJ.inv ≫ S.ι) ≫ e.inv) ≫ e.hom :=
        congrArg (fun z => z ≫ e.hom) hpre'.symm
      _ = eJ.inv ≫ S.ι := by rw [Category.assoc, e.inv_hom_id, Category.comp_id]
  let ck : restrictFunctor e.hom ⋙ restrictFunctor k ≅
      restrictFunctor S.ι ⋙ restrictFunctor eJ.inv :=
    (restrictFunctorComp k e.hom).symm ≪≫ restrictFunctorCongr hrel ≪≫
      restrictFunctorComp eJ.inv S.ι
  have hqBack : IsIso ((restrictFunctor eJ.inv).map ((restrictFunctor S.ι).map q)) :=
    Functor.map_isIso _ _
  have hqk : IsIso ((restrictFunctor e.hom ⋙ restrictFunctor k).map q) :=
    (NatIso.isIso_map_iff ck q).mpr hqBack
  have hφk : IsIso ((restrictFunctor k).map φ) := by
    change IsIso ((restrictFunctor k).map
      ((restrictFunctor e.hom).map q ≫ (cv.app M).hom))
    rw [Functor.map_comp]
    have : IsIso ((restrictFunctor k).map ((restrictFunctor e.hom).map q)) := hqk
    infer_instance
  have hn : Mono n := mono_submoduleAsModuleInclusion N
  have : PreservesFiniteLimits (restrictFunctor V.ι) := preservesFiniteLimits_restrictFunctor V.ι
  have : Mono ((restrictFunctor V.ι).map n) := Functor.map_mono _ n
  let χ : G ⟶ F.restrict V.ι := φ ≫ (restrictFunctor V.ι).map n
  have hχ : Mono χ := inferInstanceAs (Mono (φ ≫ (restrictFunctor V.ι).map n))
  let ψ := submoduleExtensionMap V.ι F χ
  let P : F.Submodule := kernelSubmodule ψ
  let Pm : X.Modules := submoduleAsModule P
  let p : Pm ⟶ F := submoduleAsModuleInclusion P
  have hKqc : (kernel ψ).IsQuasicoherent :=
    isQuasicoherent_kernel_submoduleExtensionMap V.ι F χ
  have hPqc : P.toSheafOfModules.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
      (kernelSubmoduleIso ψ).symm hKqc
  let ePV : Pm.restrict V.ι ≅ G := kernelSubmoduleExtensionRestrictIso V.ι F χ
  have hePV : ePV.hom ≫ χ = (restrictFunctor V.ι).map p :=
    kernelSubmoduleExtensionRestrictIso_hom_ι V.ι F χ
  have hPft : (P.toSheafOfModules.over V).IsFiniteType :=
    isFiniteType_over_of_restrict Pm V (finiteType_of_schemeIso ePV.symm hGft)
  let D : restrictFunctor V.ι ⋙ restrictFunctor k ≅ restrictFunctor J.ι :=
    restrictFunctorAlongLEIso (show J ≤ V from inf_le_right)
  let d : Pm.restrict J.ι ≅ M.restrict J.ι :=
    (D.app Pm).symm ≪≫ (restrictFunctor k).mapIso ePV ≪≫
      asIso ((restrictFunctor k).map φ) ≪≫ D.app M
  have hd : d.hom ≫ (restrictFunctor J.ι).map n = (restrictFunctor J.ι).map p := by
    let L := restrictFunctor k
    let a := (D.app Pm).inv
    let b := L.map ePV.hom
    let c := L.map φ
    let z := (D.app M).hom
    let nV := L.map ((restrictFunctor V.ι).map n)
    let pV := L.map ((restrictFunctor V.ι).map p)
    let eF := (D.app F).hom
    have hdn : z ≫ (restrictFunctor J.ι).map n = nV ≫ eF :=
      (D.hom.naturality n).symm
    have hdp : pV ≫ eF = (D.app Pm).hom ≫ (restrictFunctor J.ι).map p :=
      D.hom.naturality p
    have hbc : b ≫ c ≫ nV = pV :=
      (congrArg (fun z => b ≫ z) (L.map_comp φ ((restrictFunctor V.ι).map n)).symm).trans
        ((L.map_comp ePV.hom χ).symm.trans (congrArg L.map hePV))
    change (a ≫ b ≫ c ≫ z) ≫ (restrictFunctor J.ι).map n = _
    calc
      _ = a ≫ b ≫ c ≫ (z ≫ (restrictFunctor J.ι).map n) := by
        simp only [Category.assoc]
      _ = a ≫ b ≫ c ≫ (nV ≫ eF) := congrArg (fun w => a ≫ b ≫ c ≫ w) hdn
      _ = a ≫ ((b ≫ c ≫ nV) ≫ eF) := by simp only [Category.assoc]
      _ = a ≫ (pV ≫ eF) := congrArg (fun w => a ≫ (w ≫ eF)) hbc
      _ = a ≫ ((D.app Pm).hom ≫ (restrictFunctor J.ι).map p) :=
        congrArg (fun w => a ≫ w) hdp
      _ = (restrictFunctor J.ι).map p := Iso.inv_hom_id_assoc (D.app Pm) _
  exact ⟨P, hPqc, hPft, submodule_over_eq_of_restrictIso P N J d hd⟩

end AlgebraicGeometry.Scheme.Modules
