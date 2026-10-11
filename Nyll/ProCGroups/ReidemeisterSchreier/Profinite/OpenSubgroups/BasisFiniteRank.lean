/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.BasisTheorems
import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.RankBound
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Finite-rank bases of open subgroups

Starting from a finite converging-set basis, this module constructs a basis of
the open subgroup and proves the classical finite Schreier rank formula. The
padding lemma works on  so that its index lives in the ambient
universe; its public generating-family wrapper is indexed by , while the
bundled free basis used in the final rank argument retains the lifted carrier.
-/

open scoped Topology Pointwise

namespace ReidemeisterSchreier
namespace Profinite

open ProCGroups
open ProCGroups.FreeProC
open ProCGroups.ProC

universe u

/--
Finite converging-set basis data for an open subgroup of a free pro-\(C\) group on a finite
converging set. The carrier is the open subgroup itself.
-/
theorem exists_finiteIndexBasisCarrierAndMap_openSubgroup
    (C : ProCGroups.FiniteGroupClass.{u})
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
      [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hF : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (H : OpenSubgroup F) :
    ∃ (B : Type u), Finite B ∧
      ∃ μ : B → ↥(H : Subgroup F),
        IsEpimorphicallyFreeProCGroupOnConvergingSet
          (C := C)
          B ↥(H : Subgroup F) μ := by
  classical
  let : TopologicalSpace X := ⊥
  let : DiscreteTopology X := ⟨rfl⟩
  let : Fintype X := Fintype.ofFinite X
  rcases
      exists_compactPointedBasis_openSubgroup_of_freeProCOnConvergingSet
        C hForm hSub hIso hExt hF H with
    ⟨κ, _hκcont, _hκallBase, _hκbase, _hκcompact, _hκclosed, hκfree⟩
  let x0 : Set.range κ :=
    ⟨κ (openSubgroupRightCoset H (1 : F), OnePoint.infty),
      ⟨(openSubgroupRightCoset H (1 : F), OnePoint.infty), rfl⟩⟩
  let : DiscreteTopology (Set.range κ) :=
    DiscreteTopology.of_finite_of_isClosed_singleton fun _ => isClosed_singleton
  let B : Type u := {y : Set.range κ // y ≠ x0}
  let μ : B → ↥(H : Subgroup F) := fun y => y.1.1
  have hμfree :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) B ↥(H : Subgroup F) μ := by
    simpa [B, μ, x0] using
      freeOnFinitePointedDiscreteSpace_has_convergingSetBasis
        (C := C) hκfree
  exact ⟨B, inferInstance, μ, hμfree⟩

/--
An exact-size finite generating family for the open subgroup, indexed by the Schreier
rank-transform cardinal. This is a generating family, not a basis: the padding step may repeat
the distinguished padding element 1.
-/
private theorem exists_exactGeneratingFamily_openSubgroup_of_finiteBasis_ulift
    (C : ProCGroups.FiniteGroupClass.{u})
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hQuot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
      [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hF : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (H : OpenSubgroup F) :
    ∃ κ :
        ULift.{u} (Fin (_root_.ReidemeisterSchreier.Schreier.rankTransform
          (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F))))) →
          ↥(H : Subgroup F),
      Generation.GeneratesAndConvergesToOneAlongOpenSubgroups
        (G := ↥(H : Subgroup F)) (Set.range κ) := by
  classical
  let n : ℕ := _root_.ReidemeisterSchreier.Schreier.rankTransform
    (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F)))
  rcases exists_finiteIndexBasisCarrierAndMap_openSubgroup
      C hForm hSub hIso hExt hF H with
    ⟨B, hBfin, μ, hμfree⟩
  let : Finite B := hBfin
  let : Fintype B := Fintype.ofFinite B
  let Fdata : EpimorphicallyFreeProCGroupOnConvergingSetData
      (C := C) :=
    { basis := B
      carrier :=
        ProCGrp.of C (ProfiniteGrp.of ↥(H : Subgroup F)) hμfree.hasOpenNormalBasisInClass
      inclusion := μ
      isEpimorphicallyFree := hμfree }
  let Fambient : EpimorphicallyFreeProCGroupOnConvergingSetData
      (C := C) :=
    { basis := X
      carrier := ProCGrp.of C (ProfiniteGrp.of F) hF.hasOpenNormalBasisInClass
      inclusion := ι
      isEpimorphicallyFree := hF }
  have hAmbientRank :
      Cardinal.mk X = Generation.topologicalRank F :=
    basisCard_eq_topologicalRank_of_finiteBasis C hQuot hcyc Fambient
  have hdF : Generation.topologicalRank F = Nat.card X := by
    calc
      Generation.topologicalRank F = Cardinal.mk X := hAmbientRank.symm
      _ = (Nat.card X : Cardinal) := (Nat.cast_card (α := X)).symm
  have hdHle :
      Generation.topologicalRank ↥(H : Subgroup F) ≤ (n : Cardinal) := by
    simpa [n] using
      topologicalRank_openSubgroup_le_rankTransform_of_topologicalRank_eq_nat
        (G := F) hdF H
  have hBasisRank :
      Cardinal.mk B = Generation.topologicalRank ↥(H : Subgroup F) := by
    convert basisCard_eq_topologicalRank_of_finiteBasis C hQuot hcyc Fdata using 1
    rfl
  have hBcardLe : Cardinal.mk B ≤ (n : Cardinal) := hBasisRank.trans_le hdHle
  have hBcardNat : Fintype.card B ≤ Fintype.card (ULift.{u} (Fin n)) := by
    have hleNat : Fintype.card B ≤ n := by
      simpa [Nat.card_eq_fintype_card] using
        Cardinal.toNat_le_toNat hBcardLe (Cardinal.natCast_lt_aleph0 (n := n))
    simpa using hleNat
  have hEmb : Nonempty (B ↪ ULift.{u} (Fin n)) :=
    Function.Embedding.nonempty_of_card_le hBcardNat
  let e : B ↪ ULift.{u} (Fin n) := Classical.choice hEmb
  let κ : ULift.{u} (Fin n) → ↥(H : Subgroup F) :=
    Function.extend e μ (fun _ => 1)
  have hext : κ ∘ e = μ := by
    simpa [κ] using
      (Function.extend_comp e.injective μ (fun _ => (1 : ↥(H : Subgroup F))))
  have hrange :
      Set.range μ ⊆ Set.range κ := by
    rintro z ⟨b, rfl⟩
    refine ⟨e b, ?_⟩
    exact congrArg (fun f => f b) hext
  have hκgen :
      Generation.TopologicallyGenerates (G := ↥(H : Subgroup F)) (Set.range κ) :=
    Generation.topologicallyGenerates_mono (G := ↥(H : Subgroup F)) hμfree.generates_range hrange
  have hκconv : Generation.ConvergesToOneAlongOpenSubgroups (G := ↥(H : Subgroup F)) (Set.range
      κ) :=
    Generation.ConvergesToOneAlongOpenSubgroups.of_finite (G := ↥(H : Subgroup F))
        (Set.finite_range κ)
  exact ⟨κ, ⟨hκgen, hκconv⟩⟩


/-- An exact-size finite generating family for the open subgroup on the canonical Fin index.
The universe lift used to construct the padding embedding remains an implementation detail. -/
theorem exists_exactGeneratingFamily_openSubgroup_of_finiteBasis
    (C : ProCGroups.FiniteGroupClass.{u})
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hQuot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
      [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hF : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (H : OpenSubgroup F) :
    ∃ κ :
        Fin (_root_.ReidemeisterSchreier.Schreier.rankTransform
          (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F)))) →
          ↥(H : Subgroup F),
      Generation.GeneratesAndConvergesToOneAlongOpenSubgroups
        (G := ↥(H : Subgroup F)) (Set.range κ) := by
  rcases exists_exactGeneratingFamily_openSubgroup_of_finiteBasis_ulift
      C hForm hSub hIso hQuot hExt hcyc hF H with
    ⟨κ, hκ⟩
  let κFin :
      Fin (_root_.ReidemeisterSchreier.Schreier.rankTransform
        (Nat.card X) (Nat.card (F ⧸ (H : Subgroup F)))) →
        ↥(H : Subgroup F) :=
    fun i => κ (ULift.up i)
  refine ⟨κFin, ?_⟩
  have hrange : Set.range κFin = Set.range κ := by
    apply Set.Subset.antisymm
    · rintro y ⟨i, rfl⟩
      exact ⟨ULift.up i, rfl⟩
    · rintro y ⟨i, rfl⟩
      exact ⟨i.down, by cases i; rfl⟩
  rw [hrange]
  exact hκ

/--
Finite-rank extension-closed variety case using the Schreier rank-transform cardinality bound.
-/
theorem exists_basis_openSubgroup_of_extensionClosed_finiteRank
    (C : ProCGroups.FiniteGroupClass.{u})
    (hVar : ProCGroups.FiniteGroupClass.Variety C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
      [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hF : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (C := C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧
      Cardinal.mk Fdata.basis =
        (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H :
            Subgroup F))) :
          Cardinal) := by
  classical
  rcases hVar.closureBundle_of_isomClosed_extensionClosed hIso hExt with
    ⟨hForm, hSub, hIso', hQuot, hExt'⟩
  let n : ℕ := _root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H
      : Subgroup F)))
  rcases exists_finiteIndexBasisCarrierAndMap_openSubgroup
      C hForm hSub hIso' hExt' hF H with
    ⟨B, hBfin, μ, hμfree⟩
  let : Finite B := hBfin
  let Fdata : EpimorphicallyFreeProCGroupOnConvergingSetData
      (C := C) :=
    { basis := B
      carrier :=
        ProCGrp.of C (ProfiniteGrp.of ↥(H : Subgroup F)) hμfree.hasOpenNormalBasisInClass
      inclusion := μ
      isEpimorphicallyFree := hμfree }
  let Fambient : EpimorphicallyFreeProCGroupOnConvergingSetData
      (C := C) :=
    { basis := X
      carrier := ProCGrp.of C (ProfiniteGrp.of F) hF.hasOpenNormalBasisInClass
      inclusion := ι
      isEpimorphicallyFree := hF }
  have hAmbientRank :
      Cardinal.mk X = Generation.topologicalRank F :=
    basisCard_eq_topologicalRank_of_finiteBasis C hQuot hcyc Fambient
  have hdF : Generation.topologicalRank F = Nat.card X := by
    calc
      Generation.topologicalRank F = Cardinal.mk X := hAmbientRank.symm
      _ = (Nat.card X : Cardinal) := (Nat.cast_card (α := X)).symm
  have hdHle :
      Generation.topologicalRank ↥(H : Subgroup F) ≤ (n : Cardinal) := by
    simpa [n] using
      topologicalRank_openSubgroup_le_rankTransform_of_topologicalRank_eq_nat
        (G := F) hdF H
  have hDataBasis :
      Cardinal.mk Fdata.basis = Generation.topologicalRank Fdata.carrier :=
    basisCard_eq_topologicalRank_of_finiteBasis C hQuot hcyc Fdata
  have hle : Cardinal.mk Fdata.basis ≤ (n : Cardinal) := by
    simpa [Fdata] using hDataBasis.trans_le hdHle
  rcases exists_exactGeneratingFamily_openSubgroup_of_finiteBasis_ulift
      C hForm hSub hIso' hQuot hExt' hcyc hF H with
    ⟨κ, hκ⟩
  let : TopologicalSpace (FreeGroup (ULift.{u} (Fin n))) := ⊥
  let : DiscreteTopology (FreeGroup (ULift.{u} (Fin n))) := ⟨rfl⟩
  let φ : FreeGroup (ULift.{u} (Fin n)) →ₜ* ↥(H : Subgroup F) :=
    { toMonoidHom := FreeGroup.lift κ
      continuous_toFun := continuous_of_discreteTopology }
  have hComp :
      ProCGroups.Completion.IsProCCompletion
        (C)
        (FreeGroup (ULift.{u} (Fin n))) ↥(H : Subgroup F) φ := by
    obtain ⟨Y, hYfree, hYcard⟩ :=
      exists_freeBasis_comap_freeGroupLift_of_openSubgroup_of_rankTransform
        (F := F) (X := X) hF.generates_range H
    let βF : FreeGroup X →* F := FreeGroup.lift ι
    let L : Subgroup (FreeGroup X) := Subgroup.comap βF (H : Subgroup F)
    let ψ : L →* ↥(H : Subgroup F) :=
      { toFun := fun g => ⟨βF g.1, g.2⟩
        map_one' := by simp only [OneMemClass.coe_one, map_one, Subgroup.mk_eq_one]
        map_mul' := by
          intro a b
          ext
          simp only [Subgroup.coe_mul, map_mul]}
    let : TopologicalSpace (FreeGroup X) := ⊥
    let : DiscreteTopology (FreeGroup X) := ⟨rfl⟩
    have hβFdense : DenseRange βF :=
      denseRange_freeGroupLift_of_topologicallyGenerates
        (F := F) (X := X) hF.generates_range
    have hψdense : DenseRange ψ := by
      exact denseRange_comapMap_of_openSubgroup (φ := βF) hβFdense H.isOpen'
    let : TopologicalSpace (FreeGroup Y) := ⊥
    let : DiscreteTopology (FreeGroup Y) := ⟨rfl⟩
    let bY : FreeGroupBasis Y L := Classical.choice hYfree
    let eY : FreeGroup Y ≃* L := bY.repr.symm
    let φY : FreeGroup Y →ₜ* ↥(H : Subgroup F) :=
      { toMonoidHom := ψ.comp eY.toMonoidHom
        continuous_toFun := continuous_of_discreteTopology }
    have hψcont : Continuous ψ := by
      simpa using (continuous_of_discreteTopology : Continuous ψ)
    have hφYdense : DenseRange φY := by
      change DenseRange (fun y : FreeGroup Y => ψ (eY y))
      exact hψdense.comp (Function.Surjective.denseRange eY.surjective) hψcont
    have hψfinite :
        ∀ {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
          [Finite Q] [DiscreteTopology Q],
          C Q →
          ∀ χL : L →* Q,
            ∃! φbar : ↥(H : Subgroup F) →* Q,
              Continuous φbar ∧ φbar.comp ψ = χL := by
      intro Q _ _ _ _ _ hQ χL
      rcases
          exists_continuousFiniteQuotientLift_of_comap_freeGroupLift
            (C := C)
            (hForm := hForm) (hSub := hSub) (hIso := hIso')
            (hQuot := hQuot) (hExt := hExt')
            (X := X) (F := F) (ι := ι) hF H hQ χL with
        ⟨φbar, hφbarCont, hφbarFac⟩
      refine ⟨φbar, ⟨hφbarCont, hφbarFac⟩, ?_⟩
      intro φbar' hφbar'
      have hEq : (fun h : ↥(H : Subgroup F) => φbar h) = fun h => φbar' h := by
        apply DenseRange.equalizer (f := ψ) hψdense
        · exact hφbarCont
        · exact hφbar'.1
        · funext l
          exact congrArg (fun f : L →* Q => f l) (hφbarFac.trans hφbar'.2.symm)
      apply MonoidHom.ext
      intro h
      simpa using (congrArg (fun f : ↥(H : Subgroup F) → Q => f h) hEq).symm
    have hfinite :
        DenseAbstractSchreierFiniteQuotientLiftProperty
          (C := C) H φY.toMonoidHom := by
      exact denseAbstractSchreierFiniteQuotientLiftProperty_of_equiv
        (C := C) (H := H) (eY := eY) (ψ := ψ) hψfinite
    have hCompY :
        ProCGroups.Completion.IsProCCompletion
          (C)
          (FreeGroup Y) ↥(H : Subgroup F) φY := by
      exact isProCCompletion_denseAbstractSchreier_of_finiteQuotientLifts
        (C := C)
        (hForm := hForm) (hSub := hSub) (hIso := hIso')
        (X := X) (F := F) (ι := ι) hF H hφYdense hfinite
    exact
      isProCCompletion_freeGroupLift_of_exactGeneratingFamily_of_completion
        (C := C) hSub hIso' hQuot hcyc
        (Y := Y) (Z := ULift.{u} (Fin n)) (by simpa [n] using hYcard) hCompY hκ
  have hκfree :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) (ULift.{u} (Fin n)) ↥(H : Subgroup F) κ := by
    have hfree :=
      proCCompletionOfAbstractFreeGroup_is_free
        (C := C)
        (X := ULift.{u} (Fin n)) (Fhat := ↥(H : Subgroup F)) (ι := φ) hComp
    convert hfree using 1
    ext x
    change ((κ x : ↥(H : Subgroup F)) : F) =
      ((FreeGroup.lift κ (FreeGroup.of x) : ↥(H : Subgroup F)) : F)
    simp only [FreeGroup.lift_apply_of]
  let Fexact : EpimorphicallyFreeProCGroupOnConvergingSetData
      (C := C) :=
    { basis := ULift.{u} (Fin n)
      carrier :=
        ProCGrp.of C (ProfiniteGrp.of ↥(H : Subgroup F)) hκfree.hasOpenNormalBasisInClass
      inclusion := κ
      isEpimorphicallyFree := hκfree }
  have hExactBasis :
      Cardinal.mk Fexact.basis = Generation.topologicalRank Fexact.carrier :=
    basisCard_eq_topologicalRank_of_finiteBasis C hQuot hcyc Fexact
  have hExactCard : Cardinal.mk Fexact.basis = (n : Cardinal) := by
    simp only [Cardinal.mk_fintype, Fintype.card_ulift, Fintype.card_fin, Fexact]
  have hge : (n : Cardinal) ≤ Cardinal.mk Fdata.basis := by
    exact le_of_eq <| by
      calc
        (n : Cardinal) = Cardinal.mk Fexact.basis := hExactCard.symm
        _ = Generation.topologicalRank Fexact.carrier := hExactBasis
        _ = Generation.topologicalRank Fdata.carrier := by rfl
        _ = Cardinal.mk Fdata.basis := hDataBasis.symm
  refine ⟨Fdata, ⟨ContinuousMulEquiv.refl _⟩, ?_⟩
  have hCard : Cardinal.mk Fdata.basis = (n : Cardinal) := le_antisymm hle hge
  simpa [n] using hCard

/--
Finite-rank Melnikov-formation variant with explicit subgroup closure, using the Schreier
rank-transform cardinality bound.
-/
theorem exists_basis_openSubgroup_of_melnikovFormation_finiteRank_of_subgroupClosed
    (C : ProCGroups.FiniteGroupClass.{u})
    (hC : ProCGroups.FiniteGroupClass.MelnikovFormation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A)
    {X : Type u} [Finite X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
      [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hF : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (H : OpenSubgroup F) :
    ∃ Fdata : EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (C := C),
      Nonempty (Fdata.carrier ≃ₜ* ↥(H : Subgroup F)) ∧
      Cardinal.mk Fdata.basis =
        (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H :
            Subgroup F))) :
          Cardinal) := by
  let hVar : ProCGroups.FiniteGroupClass.Variety C :=
    { subgroupClosed := hSub
      quotientClosed := hC.quotientClosed
      finiteProductClosed := hC.formation.finiteProductClosed }
  exact
    exists_basis_openSubgroup_of_extensionClosed_finiteRank
      (C := C) hVar hC.isomClosed hC.extensionClosed hcyc hF H

end Profinite
end ReidemeisterSchreier
