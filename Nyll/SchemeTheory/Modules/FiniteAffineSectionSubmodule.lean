/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteLocalSectionExtension
import Nyll.SchemeTheory.Modules.FiniteSubmoduleExtension
import Nyll.SchemeTheory.Modules.FiniteQuasicoherentSum
import Nyll.SchemeTheory.Modules.FiniteTypeAffineSections
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski

/-!
# Finite quasicoherent submodules containing finite affine-local generators

For each selected affine open, finitely many actual section generators are
included in the actual quotient-kernel extension of their finite free image.
The proved finite-type extension theorem replaces this by a global
finite-type quasicoherent submodule with the same restriction. The actual
finite join retains all of the prescribed generators. The selected opens
need not cover the scheme.
-/

noncomputable section

universe u v

open CategoryTheory Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- A finite family on a compact open of a qcqs scheme belongs to a global
finite-type quasicoherent native submodule. -/
theorem exists_finiteType_submodule_containing_sections_of_isCompact
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    {I : Type u} [Finite I] (s : I → F.val.obj (op U)) :
    ∃ N : F.Submodule, N.toSheafOfModules.IsQuasicoherent ∧
      N.toSheafOfModules.IsFiniteType ∧ ∀ i : I, s i ∈ N.toSubmodule.obj (op U) := by
  let M : X.Modules := (sheafOfModulesEquivalence X).inverse.obj F
  have : M.IsQuasicoherent := inferInstanceAs F.IsQuasicoherent
  have : CompactSpace U := isCompact_iff_compactSpace.mp hU
  have : QuasiCompact U.ι := inferInstance
  obtain ⟨H, hHQC, hHFT, hH⟩ :=
    exists_quasicoherent_submodule_finiteType_over_containing_sections M U s
  have : H.toSheafOfModules.IsQuasicoherent := hHQC
  obtain ⟨N, hNQC, hNFT, hNU⟩ :=
    exists_finiteType_submodule_eq_over_of_qcqs M H U hU hHFT
  refine ⟨N, hNQC, hNFT, ?_⟩
  intro i
  have hObj : N.toSubmodule.obj (op U) = H.toSubmodule.obj (op U) :=
    SheafOfModules.Submodule.obj_eq_of_over_eq (M := F) hNU U (𝟙 U)
  rw [hObj]
  exact hH i

/-- A finitely generated actual section submodule on a compact open is
contained in a global finite-type quasicoherent native submodule. -/
theorem exists_finiteType_submodule_containing_fg_sections
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (K : Submodule (X.ringCatSheaf.obj.obj (op U)) (F.val.obj (op U))) (hK : K.FG) :
    ∃ N : F.Submodule, N.toSheafOfModules.IsQuasicoherent ∧
      N.toSheafOfModules.IsFiniteType ∧ K ≤ N.toSubmodule.obj (op U) := by
  obtain ⟨s, hs⟩ := hK
  obtain ⟨N, hNQC, hNFT, hN⟩ :=
    exists_finiteType_submodule_containing_sections_of_isCompact F U hU
      (fun i : s => i.val)
  refine ⟨N, hNQC, hNFT, ?_⟩
  rw [← hs]
  exact Submodule.span_le.mpr (fun x hx => hN ⟨x, hx⟩)

/-- Finitely many finitely generated affine-local section submodules all
belong to one actual finite-type quasicoherent native submodule. -/
theorem exists_finiteType_submodule_containing_affine_sections
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent]
    {I : Type v} [Finite I] (V : I → X.AffineZariskiSite)
    (K : ∀ i : I, Submodule (X.ringCatSheaf.obj.obj (op (V i).1))
      (F.val.obj (op (V i).1))) (hK : ∀ i : I, (K i).FG) :
    ∃ N : F.Submodule, N.toSheafOfModules.IsQuasicoherent ∧
      N.toSheafOfModules.IsFiniteType ∧
      ∀ i : I, K i ≤ N.toSubmodule.obj (op (V i).1) := by
  classical
  let : Fintype I := Fintype.ofFinite I
  choose N hNQC hNFT hN using fun i : I =>
    exists_finiteType_submodule_containing_fg_sections F (V i).1
      (V i).property.isCompact (K i) (hK i)
  let L : F.Submodule := Finset.univ.sup N
  refine ⟨L,
    SheafOfModules.Submodule.isQuasicoherent_finset_sup Finset.univ N (fun i _ => hNQC i),
    SheafOfModules.Submodule.isFiniteType_finset_sup Finset.univ N (fun i _ => hNFT i), ?_⟩
  intro i
  have hNL : N i ≤ L := Finset.le_sup (f := N) (Finset.mem_univ i)
  exact (hN i).trans (hNL (op (V i).1))

/-- On a qcqs scheme, finitely many specified finitely generated affine
section submodules are contained in one actual quasicoherent submodule
whose section module on every affine open is finitely generated. -/
theorem exists_finite_quasicoherent_submodule_containing_affine_sections
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : SheafOfModules.{u} X.ringCatSheaf) [F.IsQuasicoherent]
    {I : Type v} [Finite I] (V : I → X.AffineZariskiSite)
    (K : ∀ i : I, Submodule (X.ringCatSheaf.obj.obj (op (V i).1))
      (F.val.obj (op (V i).1))) (hK : ∀ i : I, (K i).FG) :
    ∃ N : F.Submodule, N.toSheafOfModules.IsQuasicoherent ∧
      (∀ W : X.AffineZariskiSite, (N.toSubmodule.obj (op W.1)).FG) ∧
      ∀ i : I, K i ≤ N.toSubmodule.obj (op (V i).1) := by
  obtain ⟨N, hNQC, hNFT, hN⟩ :=
    exists_finiteType_submodule_containing_affine_sections F V K hK
  refine ⟨N, hNQC, ?_, hN⟩
  intro W
  exact @fg_sections_submodule_of_isFiniteType X
    ((sheafOfModulesEquivalence X).inverse.obj F) N hNQC hNFT W.1 W.property

end AlgebraicGeometry.Scheme.Modules
