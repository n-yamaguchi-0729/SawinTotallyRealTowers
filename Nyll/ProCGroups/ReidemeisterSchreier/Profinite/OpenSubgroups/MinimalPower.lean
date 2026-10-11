/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Profinite.OpenSubgroups.BasisFiniteRank

/-!
# Pointed bases controlled by a minimal generator power

If the first positive power of a distinguished generator entering an open
subgroup is nontrivial, this module constructs a finite converging-set basis
containing that power and refines the finite-rank Schreier basis theorem while
retaining the distinguished basis element.
-/

open scoped Topology Pointwise

namespace ReidemeisterSchreier
namespace Profinite

open ProCGroups
open ProCGroups.FreeProC
open ProCGroups.ProC

universe u


/--
This is the pointed profinite Reidemeister--Schreier theorem over a converging-set basis, with a
prescribed minimal generator power landing in the open subgroup.
-/
theorem exists_compactPointedBasis_openSubgroup_of_minGeneratorPower
    (C : ProCGroups.FiniteGroupClass.{u})
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hExt : ProCGroups.FiniteGroupClass.ExtensionClosed C)
    {X : Type u}
    [TopologicalSpace X] [DiscreteTopology X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
      [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hF : IsEpimorphicallyFreeProCGroupOnConvergingSet
      (C := C) X F ι)
    (H : OpenSubgroup F) (x : X) {N : ℕ}
    (hN : 0 < N)
    (hpow : (ι x) ^ N ∈ (H : Subgroup F))
    (hmin : ∀ m : ℕ, 0 < m → m < N → (ι x) ^ m ∉ (H : Subgroup F)) :
    ∃ κ : OpenSubgroupRightQuotient H × OnePoint X → ↥(H : Subgroup F),
      Continuous κ ∧
      (∀ q : OpenSubgroupRightQuotient H, κ (q, OnePoint.infty) = 1) ∧
      κ (openSubgroupRightCoset H (1 : F), OnePoint.infty) = 1 ∧
      (⟨(ι x) ^ N, hpow⟩ : ↥(H : Subgroup F)) ∈ Set.range κ ∧
      IsCompact (Set.range κ) ∧
      IsClosed (Set.range κ) ∧
      IsEpimorphicallyPointedFreeProCGroupOn
        (C := C)
        (Set.range κ)
        ⟨κ (openSubgroupRightCoset H (1 : F), OnePoint.infty),
          ⟨(openSubgroupRightCoset H (1 : F), OnePoint.infty), rfl⟩⟩
        ↥(H : Subgroup F) Subtype.val := by
  classical
  let iInf : OnePoint X → F := fun z => z.elim 1 ι
  have hιTendsto : Filter.Tendsto ι Filter.cofinite (𝓝 (1 : F)) := by
    rw [Filter.tendsto_def]
    intro s hs
    rcases mem_nhds_iff.mp hs with ⟨W, hWs, hWopen, h1W⟩
    rcases ProCGroups.ProC.exists_openNormalSubgroup_sub_open_nhds_of_one
        (G := F) hWopen h1W with
      ⟨U, hUW⟩
    have hfinite : {x : X | ι x ∉ (U : Set F)}.Finite :=
      hF.convergesToOneAlongOpenSubgroups U.toOpenSubgroup
    have hcof : ∀ᶠ x : X in Filter.cofinite, ι x ∈ (U : Set F) :=
      Filter.eventually_cofinite.2 hfinite
    exact hcof.mono fun x hx => hWs (hUW hx)
  have hPointed :
      IsEpimorphicallyPointedFreeProCGroupOn
        (C := C)
        (OnePoint X) OnePoint.infty F iInf := by
    refine ⟨hF.hasOpenNormalBasisInClass, ?_, by simp only [OnePoint.elim_infty, iInf], ?_, ?_⟩
    · rw [OnePoint.continuous_iff_from_discrete]
      simpa [iInf] using hιTendsto
    · have hsub : Set.range ι ⊆ Set.range iInf := by
        rintro y ⟨x, rfl⟩
        exact ⟨(x : OnePoint X), rfl⟩
      exact Generation.topologicallyGenerates_mono (G := F) hF.generates_range hsub
    · intro G _ _ _ _ _ _ hG φ hφ hφ0 hgenφ
      let ψ : X → G := fun x => φ x
      have hψTendsto : Filter.Tendsto ψ Filter.cofinite (𝓝 (1 : G)) := by
        have hraw := (OnePoint.continuous_iff_from_discrete (f := φ)).1 hφ
        simpa [ψ, hφ0] using hraw
      have hψconv : FamilyConvergesToOneAlongOpenSubgroups (G := G) ψ := by
        intro U
        exact Filter.eventually_cofinite.mp <|
          hψTendsto (U.isOpen'.mem_nhds U.one_mem')
      have hφrange : Set.range φ = Set.range ψ ∪ ({1} : Set G) := by
        ext z
        constructor
        · rintro ⟨x, rfl⟩
          refine OnePoint.rec ?_ ?_ x
          · right
            simpa [iInf] using hφ0
          · intro y
            left
            exact ⟨y, rfl⟩
        · intro hz
          rcases hz with hz | hz
          · rcases hz with ⟨y, rfl⟩
            exact ⟨(y : OnePoint X), rfl⟩
          · exact ⟨OnePoint.infty, hφ0.trans hz.symm⟩
      have hψgen : Generation.TopologicallyGenerates (G := G) (Set.range ψ) := by
        have hgenφ' :
            Generation.TopologicallyGenerates (G := G) (Set.range ψ ∪ ({1} : Set G)) := by
          simpa [hφrange] using hgenφ
        exact (Generation.topologicallyGenerates_union_one_iff (G := G) (X := Set.range ψ)).1
          hgenφ'
      rcases hF.existsUnique_lift hG ψ hψconv hψgen with ⟨f, hf, huniq⟩
      refine ⟨f, ⟨hf.1, ?_⟩, ?_⟩
      · intro z
        refine OnePoint.rec ?_ ?_ z
        · calc
            f (iInf OnePoint.infty) = f 1 := rfl
            _ = 1 := map_one f
            _ = φ OnePoint.infty := hφ0.symm
        · intro y
          exact hf.2 y
      · intro g hg
        apply huniq g
        refine ⟨hg.1, ?_⟩
        intro y
        simpa [iInf, ψ] using hg.2 (y : OnePoint X)
  let x' : OnePoint X := x
  have hpow' : (iInf x') ^ N ∈ (H : Subgroup F) := by
    simpa [iInf, x'] using hpow
  have hmin' : ∀ m : ℕ, 0 < m → m < N → (iInf x') ^ m ∉ (H : Subgroup F) := by
    intro m hm hlt
    simpa [iInf, x'] using hmin m hm hlt
  exact
    exists_pointedFreeRightSchreierGeneratorFamily_of_openSubgroup_of_minimalGeneratorPower
      (C := C) hForm hSub hIso hExt hPointed H x' hN hpow' hmin'


/--
Finite-rank pointed control over a converging-set free pro-\(C\) group: if \(x^N\) is the first
positive power of a basis element landing in \(H\), and this power is nontrivial, the finite
converging-set basis model for \(H\) can be chosen so that \(x^N\) lies in the basis image.
-/
theorem exists_finiteConvergingSetBasis_openSubgroup_of_minimalGeneratorPower
    {C : ProCGroups.FiniteGroupClass.{u}}
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
    (H : OpenSubgroup F) (x : X) {N : ℕ}
    (hN : 0 < N)
    (hpow : (ι x) ^ N ∈ (H : Subgroup F))
    (hpow_ne : (ι x) ^ N ≠ 1)
    (hmin : ∀ m : ℕ, 0 < m → m < N → (ι x) ^ m ∉ (H : Subgroup F)) :
    ∃ Fdata : EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (C := C),
      ∃ e : Fdata.carrier ≃ₜ* ↥(H : Subgroup F),
        (⟨(ι x) ^ N, hpow⟩ : ↥(H : Subgroup F)) ∈
          Set.range (e ∘ Fdata.inclusion) ∧
        Finite Fdata.basis := by
  classical
  let : TopologicalSpace X := ⊥
  let : DiscreteTopology X := ⟨rfl⟩
  let : Fintype X := Fintype.ofFinite X
  rcases
      exists_compactPointedBasis_openSubgroup_of_minGeneratorPower
        C hForm hSub hIso hExt hF H x hN hpow hmin with
    ⟨κ, _hκcont, _hκbase, hκone, hxpowRange, _hκcompact, _hκclosed, hκfree⟩
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
  let Fdata : EpimorphicallyFreeProCGroupOnConvergingSetData
      (C := C) :=
    { basis := B
      carrier :=
        ProCGrp.of C (ProfiniteGrp.of ↥(H : Subgroup F)) hμfree.hasOpenNormalBasisInClass
      inclusion := μ
      isEpimorphicallyFree := hμfree }
  let ypow : Set.range κ := ⟨⟨(ι x) ^ N, hpow⟩, hxpowRange⟩
  have hypow_ne_x0 : ypow ≠ x0 := by
    intro hEq
    apply hpow_ne
    have hval : (ypow : ↥(H : Subgroup F)) = (x0 : ↥(H : Subgroup F)) :=
      congrArg Subtype.val hEq
    have hx0val : (x0 : ↥(H : Subgroup F)) = 1 := by
      simpa [x0] using hκone
    simpa [ypow] using hval.trans hx0val
  let bpow : B := ⟨ypow, hypow_ne_x0⟩
  have hbpow : μ bpow = (⟨(ι x) ^ N, hpow⟩ : ↥(H : Subgroup F)) := rfl
  refine ⟨Fdata, ContinuousMulEquiv.refl _, ?_, ?_⟩
  · refine ⟨bpow, ?_⟩
    change μ bpow = (⟨(ι x) ^ N, hpow⟩ : ↥(H : Subgroup F))
    exact hbpow
  · dsimp [Fdata, B]
    infer_instance

/--
Finite-rank pointed profinite Reidemeister--Schreier theorem: if \(x^N\) is the first positive
power of the chosen ambient basis element landing in \(H\), and this power is nontrivial, then
one can choose a finite-rank basis model of \(H\) whose basis image contains \(x^N\).
-/
theorem exists_basis_openSubgroup_of_extensionClosed_finiteRank_of_minimalGeneratorPower
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
    (H : OpenSubgroup F) (x : X) {N : ℕ}
    (hN : 0 < N)
    (hpow : (ι x) ^ N ∈ (H : Subgroup F))
    (hpow_ne : (ι x) ^ N ≠ 1)
    (hmin : ∀ m : ℕ, 0 < m → m < N → (ι x) ^ m ∉ (H : Subgroup F)) :
    ∃ Fdata : EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
        (C := C),
      ∃ e : Fdata.carrier ≃ₜ* ↥(H : Subgroup F),
        (⟨(ι x) ^ N, hpow⟩ : ↥(H : Subgroup F)) ∈
          Set.range (e ∘ Fdata.inclusion) ∧
        Cardinal.mk Fdata.basis =
          (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H :
              Subgroup F))) :
            Cardinal) := by
  classical
  rcases hVar.closureBundle_of_isomClosed_extensionClosed hIso hExt with
    ⟨hForm, hSub, hIso', hQuot, hExt'⟩
  rcases
      exists_finiteConvergingSetBasis_openSubgroup_of_minimalGeneratorPower
        (C := C) hForm hSub hIso' hExt' hF H x hN hpow hpow_ne hmin with
    ⟨Fdata, eData, hxrange, hFin⟩
  let : Finite Fdata.basis := hFin
  rcases exists_basis_openSubgroup_of_extensionClosed_finiteRank
      (C := C) hVar hIso hExt hcyc hF H with
    ⟨Fexact, hFexactEquiv, hExactCard⟩
  have hFexactLt : Cardinal.mk Fexact.basis < Cardinal.aleph0 := by
    calc
      Cardinal.mk Fexact.basis =
          (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H :
              Subgroup F))) :
            Cardinal) := hExactCard
      _ < Cardinal.aleph0 := Cardinal.natCast_lt_aleph0
  let : Finite Fexact.basis := Cardinal.lt_aleph0_iff_finite.mp hFexactLt
  have hExactBasis :
      Cardinal.mk Fexact.basis = Generation.topologicalRank Fexact.carrier :=
    basisCard_eq_topologicalRank_of_finiteBasis C hQuot hcyc Fexact
  have hDataBasis :
      Cardinal.mk Fdata.basis = Generation.topologicalRank Fdata.carrier :=
    basisCard_eq_topologicalRank_of_finiteBasis C hQuot hcyc Fdata
  rcases hFexactEquiv with ⟨eExact⟩
  have hRankEq :
      Generation.topologicalRank Fexact.carrier =
        Generation.topologicalRank Fdata.carrier := by
    exact Generation.topologicalRank_eq_of_continuousMulEquiv
      (eExact.trans eData.symm)
  have hCard :
      Cardinal.mk Fdata.basis =
        (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H :
            Subgroup F))) :
          Cardinal) := by
    calc
      Cardinal.mk Fdata.basis = Generation.topologicalRank Fdata.carrier := hDataBasis
      _ = Generation.topologicalRank Fexact.carrier := hRankEq.symm
      _ = Cardinal.mk Fexact.basis := hExactBasis.symm
      _ = (_root_.ReidemeisterSchreier.Schreier.rankTransform (Nat.card X) (Nat.card (F ⧸ (H :
          Subgroup F))) :
            Cardinal) := hExactCard
  exact ⟨Fdata, eData, hxrange, hCard⟩

end Profinite
end ReidemeisterSchreier
