/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.AffineChartFiniteSubmoduleExtension
import Nyll.SchemeTheory.Modules.FiniteSubmoduleUnionExtension
import Nyll.SchemeTheory.Modules.QuasicoherentSubmoduleOverExtension
import Nyll.SchemeTheory.Modules.SubmoduleGluingQuasicoherent
import Nyll.SchemeTheory.Modules.SubmoduleOverEquality
import Nyll.SchemeTheory.Modules.FiniteTypeLocality
import Nyll.SchemeTheory.Modules.FiniteTypeTop
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Finite quasicoherent submodule extension on qcqs schemes

The compact-open induction adds one affine chart at a time. Its invariant
is an actual global quasicoherent submodule, finite type on the prescribed
open together with all charts already added, and unchanged on that
prescribed open. Each step constructs the affine refinement, glues the
two actual restrictions, and applies the native quasicoherent extension.

At the top open, cover-locality gives global finite type. Applying this to
the actual quasicoherent extension of any prescribed native submodule
proves the original extension statement of Stacks Tag 01PF.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.Submodule

namespace AlgebraicGeometry.Scheme.Modules

/-- A global quasicoherent submodule finite type on a compact open has a
global finite-type quasicoherent replacement with exactly the same restriction. -/
theorem exists_finiteType_submodule_eq_over_of_qcqs
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent] (H : F.Submodule)
    [H.toSheafOfModules.IsQuasicoherent]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (hHft : (H.toSheafOfModules.over U).IsFiniteType) :
    ∃ N : F.Submodule, N.toSheafOfModules.IsQuasicoherent ∧
      N.toSheafOfModules.IsFiniteType ∧ N.over U = H.over U := by
  let I : X.Opens → Prop := fun S =>
    ∃ N : F.Submodule, N.toSheafOfModules.IsQuasicoherent ∧
      (N.toSheafOfModules.over (U ⊔ S)).IsFiniteType ∧ N.over U = H.over U
  have hTop : I ⊤ := by
    refine compact_open_induction_on (P := I) (⊤ : X.Opens) isCompact_univ ?_ ?_
    · refine ⟨H, inferInstanceAs H.toSheafOfModules.IsQuasicoherent, ?_, rfl⟩
      exact Eq.mpr (congrArg
        (fun W : X.Opens => (H.toSheafOfModules.over W).IsFiniteType)
        (sup_bot_eq U)) hHft
    · intro S hS V hIS
      obtain ⟨N, hNqc, hNft, hNU⟩ := hIS
      have : N.toSheafOfModules.IsQuasicoherent := hNqc
      have hT : IsCompact ((U ⊔ S : X.Opens) : Set X) := hU.union hS
      obtain ⟨P, hPqc, hPft, hPN⟩ :=
        exists_finiteType_affineChart_extension F N (U ⊔ S) hT V V.property hNft
      have : P.toSheafOfModules.IsQuasicoherent := hPqc
      have hOverlap : ∀ (Z : X.Opens) (_a : Z ⟶ U ⊔ S) (_b : Z ⟶ (V : X.Opens)),
          N.toSubmodule.obj (op Z) = P.toSubmodule.obj (op Z) := by
        intro Z a b
        exact (obj_eq_of_over_eq hPN Z
          (homOfLE (le_inf (leOfHom a) (leOfHom b)))).symm
      obtain ⟨L, hLqc, hLft, hLT, _hLV⟩ :=
        exists_finiteType_union_extension F N P (U ⊔ S) V hT V.property.isCompact
          hOverlap hNft hPft
      refine ⟨L, hLqc, ?_, ?_⟩
      · exact Eq.mp (congrArg
          (fun W : X.Opens => (L.toSheafOfModules.over W).IsFiniteType)
          (sup_assoc U S (V : X.Opens))) hLft
      · exact (over_eq_of_over_eq hLT (homOfLE (le_sup_left : U ≤ U ⊔ S))).trans hNU
  obtain ⟨N, hNqc, hNft, hNU⟩ := hTop
  have hNtop : (N.toSheafOfModules.over (⊤ : X.Opens)).IsFiniteType := by
    exact Eq.mp (congrArg
      (fun W : X.Opens => (N.toSheafOfModules.over W).IsFiniteType)
      (sup_top_eq U)) hNft
  exact ⟨N, hNqc, SheafOfModules.IsFiniteType.of_over_top N.toSheafOfModules hNtop, hNU⟩

/-- Stacks Tag 01PF: a finite-type quasicoherent native submodule on a
quasi-compact open of a qcqs scheme extends to a global finite-type
quasicoherent native submodule with literal equality on that open. -/
theorem exists_finiteType_submodule_extension_of_qcqs
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsCompact (U : Set X)) (G : (F.over U).Submodule)
    (hGqc : G.toSheafOfModules.IsQuasicoherent)
    (hGft : G.toSheafOfModules.IsFiniteType) :
    ∃ N : F.Submodule, N.toSheafOfModules.IsQuasicoherent ∧
      N.toSheafOfModules.IsFiniteType ∧ N.over U = G := by
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have : QuasiCompact U.ι := inferInstance
  let H : F.Submodule := extendQuasicoherentSubmoduleOver F U G
  have : H.toSheafOfModules.IsQuasicoherent :=
    isQuasicoherent_extendQuasicoherentSubmoduleOver F U G hGqc
  have hHU : H.over U = G := extendQuasicoherentSubmoduleOver_over F U G
  have hHftNative : (H.over U).toSheafOfModules.IsFiniteType := by
    rw [hHU]
    exact hGft
  have hHft : (H.toSheafOfModules.over U).IsFiniteType :=
    SheafOfModules.IsFiniteType.of_iso
      (C := Over U) (R := X.ringCatSheaf.over U)
      (M := (H.over U).toSheafOfModules) (N := H.toSheafOfModules.over U)
      (overSheafIso H U) hHftNative
  obtain ⟨N, hNqc, hNft, hNU⟩ :=
    exists_finiteType_submodule_eq_over_of_qcqs F H U hU hHft
  exact ⟨N, hNqc, hNft, hNU.trans hHU⟩

end AlgebraicGeometry.Scheme.Modules
