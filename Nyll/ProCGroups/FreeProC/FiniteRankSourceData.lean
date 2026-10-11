/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FreeProC.FiniteBasis

/-!
# Finite-rank free pro-C source data

This module packages a finite-rank epimorphically free pro-\(C\) group as the canonical
source-data structure and records the cardinality of its lifted finite basis.
-/

namespace CrowellExactSequence

universe u

variable {F : Type u} [TopologicalSpace F] [Group F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]

/-- Package a finite-rank epimorphically free pro-\(\Sigma\) group using the canonical
ProCGroups source-data structure. -/
noncomputable def finiteRank_epimorphicallyFreeProCSourceData
    {sigma : Set ℕ} {r : ℕ} (X : Fin r → F)
    (hFree : ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := (ProCGroups.FiniteGroupClass.sigmaGroup.{u} sigma))
      (Fin r) F X) :
    ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
      (ProCGroups.FiniteGroupClass.sigmaGroup sigma) := by
  exact
    { basis := ULift.{u} (Fin r)
      carrier := ProCGrp.of
        (ProCGroups.FiniteGroupClass.sigmaGroup.{u} sigma)
        (ProfiniteGrp.of F) hFree.hasOpenNormalBasisInClass
      inclusion := fun i => X i.down
      isEpimorphicallyFree := by
        refine ⟨hFree.hasOpenNormalBasisInClass, ?_, ?_, ?_⟩
        · exact
            ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain
              (G := F) (fun i : ULift.{u} (Fin r) => X i.down)
        · have hrange :
              Set.range (fun i : ULift.{u} (Fin r) => X i.down) =
                Set.range X := by
            ext x
            constructor
            · rintro ⟨i, rfl⟩
              exact ⟨i.down, rfl⟩
            · rintro ⟨i, rfl⟩
              exact ⟨ULift.up i, rfl⟩
          change
            ProCGroups.Generation.TopologicallyGenerates
              (G := F) (Set.range (fun i : ULift.{u} (Fin r) => X i.down))
          rw [hrange]
          exact hFree.generates_range
        · intro G _ _ _ _ _ _ hG φ _hφ hgen
          let φFin : Fin r → G := fun i => φ (ULift.up i)
          have hφFinConv :
              ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups
                (G := G) φFin :=
            ProCGroups.FreeProC.FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain φFin
          have hφFinGen :
              ProCGroups.Generation.TopologicallyGenerates
                (G := G) (Set.range φFin) := by
            have hrange : Set.range φFin = Set.range φ := by
              ext g
              constructor
              · rintro ⟨i, rfl⟩
                exact ⟨ULift.up i, rfl⟩
              · rintro ⟨i, rfl⟩
                exact ⟨i.down, by cases i; rfl⟩
            rw [hrange]
            exact hgen
          rcases hFree.existsUnique_lift hG φFin hφFinConv hφFinGen with
            ⟨f, hf, huniq⟩
          refine ⟨f, ⟨hf.1, ?_⟩, ?_⟩
          · intro i
            cases i with
            | up i => exact hf.2 i
          · intro g hg
            apply huniq
            refine ⟨hg.1, ?_⟩
            intro i
            exact hg.2 (ULift.up i) }

/-- The finite-rank free pro-\(C\) source data has the expected basis cardinality. -/
theorem finiteRank_epimorphicallyFreeProCSourceData_basis_card
    {sigma : Set ℕ} {r : ℕ} (X : Fin r → F)
    (hFree : ProCGroups.FreeProC.IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := (ProCGroups.FiniteGroupClass.sigmaGroup.{u} sigma))
      (Fin r) F X) :
    Cardinal.mk (finiteRank_epimorphicallyFreeProCSourceData (F := F) X hFree).basis = r := by
  simp only [finiteRank_epimorphicallyFreeProCSourceData, Cardinal.mk_fintype, Fintype.card_ulift,
    Fintype.card_fin]

end CrowellExactSequence
