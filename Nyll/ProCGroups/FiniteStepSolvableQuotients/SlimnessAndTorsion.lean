/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteStepSolvableQuotients.Faithful
import Nyll.ProCGroups.FiniteStepSolvableQuotients.AbTorsionFree
import Nyll.ProCGroups.Abelian.Transfer
import Nyll.ProCGroups.GroupTheory.CentralizerNormalizerCommensurator
import Nyll.ProCGroups.ProC.GroupPredicates.Abelian

/-!
# Slimness and torsion from abelianization actions

This module defines torsion-free, slim, slim-modulo, and relatively slim groups, and derives
slimness and torsion consequences from faithful conjugation actions on abelianizations.
-/

open scoped Topology commutatorElement

namespace ProCGroups.FiniteStepSolvableQuotients

open ProCGroups.Abelian ProCGroups.ProC

universe u v

/-- A group is torsion-free when every element of finite order is trivial. -/
def IsTorsionFreeGroup
    (G : Type u) [Group G] : Prop :=
  ∀ g : G, IsOfFinOrder g → g = 1

/--
A topological group is slim when every open subgroup has trivial centralizer in the ambient
group.
-/
def IsSlim
    (G : Type u) [TopologicalSpace G] [Group G] : Prop :=
  ∀ H : OpenSubgroup G, Subgroup.centralizer (H : Set G) = ⊥

/--
A topological group is slim modulo \(K\) when every open subgroup has centralizer contained in
\(K\).
-/
def IsSlimModulo
    (G : Type u) [TopologicalSpace G] [Group G]
    (K : Subgroup G) : Prop :=
  ∀ H : OpenSubgroup G, Subgroup.centralizer (H : Set G) ≤ K

/--
A continuous homomorphism is relatively slim when the image of every open subgroup has trivial
centralizer in the target.
-/
def IsRelativelySlim
    {G : Type u} [TopologicalSpace G] [Group G]
    {H : Type v} [TopologicalSpace H] [Group H]
    (f : G →ₜ* H) : Prop :=
  ∀ U : OpenSubgroup G,
    Subgroup.centralizer ((((U : Subgroup G).map f.toMonoidHom : Subgroup H) : Set H)) = ⊥

/-- Relative slimness for the identity map is the same as slimness. -/
theorem isSlim_iff_isRelativelySlim_id
    {G : Type u} [TopologicalSpace G] [Group G] :
    IsSlim G ↔
      IsRelativelySlim
        ({ toMonoidHom := MonoidHom.id G
           continuous_toFun := continuous_id } : G →ₜ* G) := by
  simp only [IsSlim, IsRelativelySlim, Subgroup.map_id, OpenSubgroup.coe_toSubgroup]

/-- A slim profinite group has trivial center. -/
theorem center_eq_bot_of_isSlim
    {G : Type u} [TopologicalSpace G] [Group G]
    (hSlim : IsSlim G) :
    Subgroup.center G = ⊥ := by
  simpa [Subgroup.centralizer_univ] using hSlim (⊤ : OpenSubgroup G)

/-- Slimness modulo \(K\) forces the center into \(K\). -/
theorem center_le_of_isSlimModulo
    {G : Type u} [TopologicalSpace G] [Group G]
    {K : Subgroup G} (hSlim : IsSlimModulo G K) :
    Subgroup.center G ≤ K := by
  simpa [Subgroup.centralizer_univ] using hSlim (⊤ : OpenSubgroup G)

/-- Slimness modulo the trivial subgroup is just slimness. -/
theorem isSlim_of_isSlimModulo_bot
    {G : Type u} [TopologicalSpace G] [Group G]
    (hSlim : IsSlimModulo G (⊥ : Subgroup G)) :
    IsSlim G := by
  intro H
  exact le_antisymm (hSlim H) bot_le

/--
Torsion-freeness of open-subgroup abelianizations implies ordinary torsion-freeness in the
commutative case.
-/
theorem isMulTorsionFree_of_isAbTorsionFree_isMulCommutative
    {G : Type u} [TopologicalSpace G] [Group G] [IsMulCommutative G]
    [IsTopologicalGroup G] [T1Space G]
    (hG : IsAbTorsionFree G) :
    IsMulTorsionFree G := by
  exact (open scoped IsMulCommutative in
    isMulTorsionFree_of_isAbTorsionFree_commGroup (G := G) hG)

/-- Multiplicative torsion-freeness implies the usual finite-order formulation. -/
theorem isTorsionFreeGroup_of_isMulTorsionFree
    {G : Type u} [Group G] [IsMulTorsionFree G] :
    IsTorsionFreeGroup G := by
  intro g hg
  by_contra hne
  exact (not_isOfFinOrder_of_isMulTorsionFree hne) hg

/--
An automorphism of a torsion-free group that is trivial on a finite-index subgroup is trivial
everywhere.
-/
theorem eq_one_mulAut_of_forall_mem_subgroup
    {A : Type u} [Group A] [IsMulTorsionFree A]
    (φ : MulAut A) (B : Subgroup A) [B.FiniteIndex]
    (hφ : ∀ b : A, b ∈ B → φ b = b) :
    φ = 1 := by
  ext a
  let C : Subgroup A := B.normalCore
  let : C.FiniteIndex := Subgroup.finiteIndex_normalCore (H := B)
  have hidx : C.index ≠ 0 := by
    simpa [C] using (Subgroup.finiteIndex_iff (H := C)).mp ‹C.FiniteIndex›
  have haC : a ^ C.index ∈ C := C.pow_index_mem a
  have hpow :
      (φ a) ^ C.index = a ^ C.index := by
    calc
      (φ a) ^ C.index = φ (a ^ C.index) := by simp only [map_pow]
      _ = a ^ C.index := hφ _ ((Subgroup.normalCore_le B) haC)
  exact IsMulTorsionFree.pow_left_injective (M := A) hidx hpow

/--
A nontrivial class in the topological abelianization of a closed subgroup remains nontrivial in
the topological abelianization of some ambient open subgroup containing it.
-/
theorem exists_openSubgroup_nontrivial_topologicalAbelianizationImage
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (T : ClosedSubgroup G)
    {a : TopologicalAbelianization ↥(T : Subgroup G)} (hne : a ≠ 1) :
    ∃ H : OpenSubgroup G,
      (T : Subgroup G) ≤ (H : Subgroup G) ∧
      ∃ f : TopologicalAbelianization ↥(T : Subgroup G) →*
          TopologicalAbelianization ↥(H : Subgroup G),
        f a ≠ 1 := by
  classical
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.closedCommutator (T : Subgroup G)) a
  let A := TopologicalAbelianization ↥(T : Subgroup G)
  have hxne : TopologicalAbelianization.mk ↥(T : Subgroup G) x ≠ 1 := hne
  have : CompactSpace ↥(T : Subgroup G) := by
    exact
      (show IsClosed (((T : Subgroup G) : Set G)) from
          T.2).isClosedEmbedding_subtypeVal.compactSpace
  let C : Subgroup ↥(T : Subgroup G) :=
    Subgroup.closedCommutator (T : Subgroup G)
  let : C.Normal := by dsimp [C]; infer_instance
  have hCclosed : IsClosed (C : Set ↥(T : Subgroup G)) := by
    simp [C]
  let : CompactSpace A := by
    simpa [A, C] using
      (inferInstance : CompactSpace (↥(T : Subgroup G) ⧸ C))
  let : T2Space A := by
    simpa [A, C] using (inferInstance : T2Space (↥(T : Subgroup G) ⧸ C))
  let : TotallyDisconnectedSpace A := by
    simpa [A, C] using
      (ProCGroups.totallyDisconnectedSpace_quotient_closedNormal C hCclosed)
  obtain ⟨Uab, hxUab⟩ :=
    ProCGroups.ProC.exists_openNormalSubgroup_not_mem (G := A) hxne
  let qA : A →* A ⧸ (Uab : Subgroup A) := QuotientGroup.mk' (Uab : Subgroup A)
  have hqAx_ne : qA (TopologicalAbelianization.mk ↥(T : Subgroup G) x) ≠ 1 := by
    intro hq
    exact hxUab ((QuotientGroup.eq_one_iff (N := (Uab : Subgroup A))
      (TopologicalAbelianization.mk ↥(T : Subgroup G) x)).1 hq)
  let N0 : OpenNormalSubgroup ↥(T : Subgroup G) :=
    OpenNormalSubgroup.comap
      (TopologicalAbelianization.mk ↥(T : Subgroup G))
      (by
        exact
          (TopologicalAbelianization.mkₜ
            ↥(T : Subgroup G)).continuous_toFun) Uab
  have hN0ker :
      (N0 : Subgroup ↥(T : Subgroup G)) ≤
        (qA.comp (TopologicalAbelianization.mk ↥(T : Subgroup G))).ker := by
    intro y hy
    change qA (TopologicalAbelianization.mk ↥(T : Subgroup G) y) = 1
    exact (QuotientGroup.eq_one_iff (N := (Uab : Subgroup A))
      (TopologicalAbelianization.mk ↥(T : Subgroup G) y)).2 hy
  obtain ⟨V, hVT⟩ :=
    ProCGroups.ProC.exists_openNormalSubgroup_inter_closedSubgroup_le
      (G := G) T N0.toOpenSubgroup
  let Hsub : Subgroup G := (T : Subgroup G) ⊔ (V : Subgroup G)
  have hHOpen : IsOpen (Hsub : Set G) := by
    exact Subgroup.isOpen_of_openSubgroup Hsub
      (show (V : Subgroup G) ≤ Hsub from le_sup_right)
  let H : OpenSubgroup G := ⟨Hsub, hHOpen⟩
  let ι : ↥(T : Subgroup G) →* ↥(H : Subgroup G) :=
    { toFun := fun y => ⟨y.1, (show (T : Subgroup G) ≤ (H : Subgroup G) from le_sup_left) y.2⟩
      map_one' := by ext; simp only [OneMemClass.coe_one, H, Hsub]
      map_mul' := by intro y z; ext; rfl }
  let qT : ↥(T : Subgroup G) →* A ⧸ (Uab : Subgroup A) :=
    qA.comp (TopologicalAbelianization.mk ↥(T : Subgroup G))
  let VT : OpenNormalSubgroup ↥(T : Subgroup G) :=
    OpenNormalSubgroup.comap ((T : Subgroup G).subtype) continuous_subtype_val V
  have hVTker : (VT : Subgroup ↥(T : Subgroup G)) ≤ qT.ker := by
    exact
      (show (VT : Subgroup ↥(T : Subgroup G)) ≤ (N0 : Subgroup ↥(T : Subgroup G)) from hVT).trans
        hN0ker
  let L : Subgroup (G ⧸ (V : Subgroup G)) :=
    Subgroup.map (QuotientGroup.mk' (V : Subgroup G)) (T : Subgroup G)
  let ψ : ↥(T : Subgroup G) →* L :=
    { toFun := fun y => ⟨QuotientGroup.mk' (V : Subgroup G) y.1, ⟨y.1, y.2, rfl⟩⟩
      map_one' := by ext; rfl
      map_mul' := by intro y z; ext; rfl }
  have hψSurj : Function.Surjective ψ := by
    intro z
    rcases z with ⟨z, hz⟩
    rcases hz with ⟨y, hy, hyz⟩
    exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩
  have hψKer : (VT : Subgroup ↥(T : Subgroup G)) = ψ.ker := by
    ext y
    constructor
    · intro hy
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := (V : Subgroup G)) y.1).2 hy
    · intro hy
      exact (QuotientGroup.eq_one_iff (N := (V : Subgroup G)) y.1).1 <| congrArg Subtype.val hy
  let qTquot : ↥(T : Subgroup G) ⧸ ψ.ker →* A ⧸ (Uab : Subgroup A) :=
    QuotientGroup.lift ψ.ker qT (by simpa [hψKer] using hVTker)
  let qL : L →* A ⧸ (Uab : Subgroup A) :=
    qTquot.comp (QuotientGroup.quotientKerEquivOfSurjective ψ hψSurj).symm.toMonoidHom
  let qLcont : L →ₜ* A ⧸ (Uab : Subgroup A) :=
    { toMonoidHom := qL
      continuous_toFun := by
        exact continuous_of_discreteTopology }
  let qHaux : ↥(H : Subgroup G) →* L :=
    { toFun := fun y =>
        ⟨QuotientGroup.mk' (V : Subgroup G) y.1, by
          rcases
              (Subgroup.mem_sup_of_normal_right
                (s := (T : Subgroup G)) (t := (V : Subgroup G)) (x := y.1)).1 y.2 with
            ⟨t, htT, v, hvV, htv⟩
          refine ⟨t, htT, ?_⟩
          have hv1 : QuotientGroup.mk' (V : Subgroup G) v = 1 := by
            exact (QuotientGroup.eq_one_iff (N := (V : Subgroup G)) v).2 hvV
          calc
            QuotientGroup.mk' (V : Subgroup G) t =
                QuotientGroup.mk' (V : Subgroup G) t * 1 := by simp only
                    [QuotientGroup.mk'_apply, mul_one]
            _ = QuotientGroup.mk' (V : Subgroup G) t *
                  QuotientGroup.mk' (V : Subgroup G) v := by rw [hv1]
            _ = QuotientGroup.mk' (V : Subgroup G) (t * v) := by rw [map_mul]
            _ = QuotientGroup.mk' (V : Subgroup G) y.1 := by rw [htv]⟩
      map_one' := by ext; rfl
      map_mul' := by intro y z; ext; rfl }
  let qH : ↥(H : Subgroup G) →ₜ* A ⧸ (Uab : Subgroup A) :=
    { toMonoidHom := qL.comp qHaux
      continuous_toFun := by
        have hqHaux : Continuous qHaux := by
          exact Continuous.subtype_mk
            (by
              change Continuous
                (fun y : ↥(H : Subgroup G) =>
                  QuotientGroup.mk' (V : Subgroup G) y.1)
              exact QuotientGroup.continuous_mk.comp continuous_subtype_val)
            (fun y => (qHaux y).2)
        exact qLcont.continuous_toFun.comp hqHaux }
  have hqH_on_T : ∀ y : ↥(T : Subgroup G), qH (ι y) = qT y := by
    intro y
    have hqHaux : qHaux (ι y) = ψ y := by
      apply Subtype.ext
      rfl
    change qL (qHaux (ι y)) = qT y
    rw [hqHaux]
    have hmk :
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψSurj).symm (ψ y) =
          QuotientGroup.mk' ψ.ker y := by
      rw [QuotientGroup.quotientKerEquivOfSurjective,
        QuotientGroup.quotientKerEquivOfRightInverse_symm_apply]
      apply QuotientGroup.eq.2
      change ψ ((Exists.choose (Function.Surjective.hasRightInverse hψSurj) (ψ y))⁻¹ * y) = 1
      simp only [map_mul, map_inv, Exists.choose_spec (Function.Surjective.hasRightInverse
          hψSurj) (ψ y),
  inv_mul_cancel]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_comp, MonoidHom.coe_ofClass,
        Function.comp_apply, hmk,
  QuotientGroup.mk'_apply, QuotientGroup.lift_mk, qL, qTquot]
  let ιcont : ↥(T : Subgroup G) →ₜ* ↥(H : Subgroup G) :=
    { toMonoidHom := ι
      continuous_toFun := by
        exact Continuous.subtype_mk continuous_subtype_val
          (fun y => (show (T : Subgroup G) ≤ (H : Subgroup G) from le_sup_left) y.2) }
  have hclosedBot :
      IsClosed (((⊥ : Subgroup (A ⧸ (Uab : Subgroup A))) : Set (A ⧸ (Uab : Subgroup A)))) := by
    change IsClosed ({(1 : A ⧸ (Uab : Subgroup A))} : Set (A ⧸ (Uab : Subgroup A)))
    exact isClosed_singleton
  have hcommMapBot :
      (commutator ↥(H : Subgroup G)).map (qH : ↥(H : Subgroup G) →* A ⧸ (Uab : Subgroup A)) ≤
        (⊥ : Subgroup (A ⧸ (Uab : Subgroup A))) := by
    rw [_root_.map_commutator_eq]
    refine Subgroup.commutator_le.mpr ?_
    intro a ha b hb
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm a b)
  have hcommClosureBot :
      (Subgroup.closedCommutator (H : Subgroup G)).map
          (qH : ↥(H : Subgroup G) →* A ⧸ (Uab : Subgroup A)) ≤
        (⊥ : Subgroup (A ⧸ (Uab : Subgroup A))) := by
    exact TopologicalGroup.map_closure_le_of_map_le
      (f := qH)
      (G₁ := commutator ↥(H : Subgroup G))
      (Q₁ := (⊥ : Subgroup (A ⧸ (Uab : Subgroup A))))
      hcommMapBot
      hclosedBot
  let fAb : TopologicalAbelianization ↥(T : Subgroup G) →*
      TopologicalAbelianization ↥(H : Subgroup G) :=
    TopologicalAbelianization.map ιcont
  have hbne : fAb (TopologicalAbelianization.mk ↥(T : Subgroup G) x) ≠ 1 := by
    intro hb
    have hxcomm :
        ι x ∈ Subgroup.closedCommutator (H : Subgroup G) := by
      have hb' :
          TopologicalAbelianization.mk ↥(H : Subgroup G) (ι x) = 1 := by
        change TopologicalAbelianization.mk ↥(H : Subgroup G) (ι x) = 1 at hb
        exact hb
      exact
        (QuotientGroup.eq_one_iff
          (N := Subgroup.closedCommutator (H : Subgroup G))
          (ι x)).1 hb'
    have hxmap :
        qH (ι x) ∈
          (Subgroup.closedCommutator (H : Subgroup G)).map
            (qH : ↥(H : Subgroup G) →* A ⧸ (Uab : Subgroup A)) := ⟨ι x, hxcomm, rfl⟩
    have hxbot : qH (ι x) ∈ (⊥ : Subgroup (A ⧸ (Uab : Subgroup A))) := hcommClosureBot hxmap
    have hqHx : qH (ι x) = 1 := by simpa using hxbot
    have hqTx : qT x = 1 := by simpa [hqH_on_T x] using hqHx
    exact hqAx_ne (by simpa [qT] using hqTx)
  exact ⟨H, le_sup_left, ⟨fAb, hbne⟩⟩

/--
The topological abelianization of a closed subgroup is torsion-free under the local
abelianization torsion-free hypothesis.
-/
theorem isMulTorsionFree_topologicalAbelianization_of_closedSubgroup
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsAbTorsionFree G)
    (T : ClosedSubgroup G) :
    IsMulTorsionFree (TopologicalAbelianization ↥(T : Subgroup G)) := by
  classical
  rw [isMulTorsionFree_iff_not_isOfFinOrder]
  intro a hne hfin
  obtain ⟨H, -, fAb, hbne⟩ :=
    exists_openSubgroup_nontrivial_topologicalAbelianizationImage (G := G) T (a := a) hne
  have hbfin : IsOfFinOrder (fAb a) := MonoidHom.isOfFinOrder fAb hfin
  have hHtf :
      IsMulTorsionFree (TopologicalAbelianization ↥(H : Subgroup G)) := hG H
  exact
    (isMulTorsionFree_iff_not_isOfFinOrder
      (G := TopologicalAbelianization ↥(H : Subgroup G))).mp hHtf hbne hbfin

/-- The local abelianization torsion-free condition passes to closed subgroups. -/
theorem isAbTorsionFree_closedSubgroup
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsAbTorsionFree G)
    {K : Subgroup G} (hKClosed : IsClosed (K : Set G)) :
    IsAbTorsionFree ↥K := by
  let T : ClosedSubgroup G := ⟨K, hKClosed⟩
  let : IsTopologicalGroup T := by
    change IsTopologicalGroup ↥(T : Subgroup G)
    infer_instance
  intro N
  let N0 : OpenSubgroup T := N
  let : IsTopologicalGroup ↥(N0 : Subgroup T) := by
    infer_instance
  let N' : ClosedSubgroup G := ProCGroups.ProC.closedSubgroupOfOpenSubgroup (G := G) T N0
  have hN'tf :
      IsMulTorsionFree (TopologicalAbelianization ↥(N' : Subgroup G)) :=
    isMulTorsionFree_topologicalAbelianization_of_closedSubgroup (G := G) hG N'
  have hle :
      (N' : Subgroup G) ≤ (T : Subgroup G) :=
    ProCGroups.ProC.closedSubgroupOfOpenSubgroup_le (G := G) T N0
  let eEq : ↥(N0 : Subgroup T) ≃ₜ*
      ↥(((N' : Subgroup G).subgroupOf (T : Subgroup G))) :=
    { toMulEquiv :=
        { toFun := fun x => ⟨x.1, by
            exact
              (ProCGroups.ProC.closedSubgroupOfOpenSubgroup_subgroupOf_eq
                (G := G) T N0).symm ▸ x.2⟩
          invFun := fun x => ⟨x.1, by
            exact
              (ProCGroups.ProC.closedSubgroupOfOpenSubgroup_subgroupOf_eq
                (G := G) T N0) ▸ x.2⟩
          left_inv := by intro x; ext; rfl
          right_inv := by intro x; ext; rfl
          map_mul' := by intro x y; rfl }
      continuous_toFun := by
        exact Continuous.subtype_mk continuous_subtype_val
          (fun x =>
            (ProCGroups.ProC.closedSubgroupOfOpenSubgroup_subgroupOf_eq
              (G := G) T N0).symm ▸ x.2)
      continuous_invFun := by
        exact Continuous.subtype_mk continuous_subtype_val
          (fun x =>
            (ProCGroups.ProC.closedSubgroupOfOpenSubgroup_subgroupOf_eq
              (G := G) T N0) ▸ x.2) }
  let eN : ↥(N0 : Subgroup T) ≃ₜ* ↥(N' : Subgroup G) :=
    eEq.trans (Subgroup.subgroupOfContinuousMulEquivOfLe hle)
  let eAb :
      TopologicalAbelianization ↥(N0 : Subgroup T) ≃ₜ*
        TopologicalAbelianization ↥(N' : Subgroup G) :=
    TopologicalAbelianization.congr (G := ↥(N0 : Subgroup T))
      (H := ↥(N' : Subgroup G)) eN
  exact eAb.symm.isMulTorsionFree

/--
A commutative closed subgroup of an abelianization-torsion-free profinite group is torsion-free.
-/
theorem isTorsionFreeGroup_of_isAbTorsionFree_of_closedCommSubgroup
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {K : Subgroup G} (hKClosed : IsClosed (K : Set G))
    [IsMulCommutative ↥K]
    (hG : IsAbTorsionFree G) :
    IsTorsionFreeGroup ↥K := by
  have hKab : IsAbTorsionFree ↥K := isAbTorsionFree_closedSubgroup (G := G) hG hKClosed
  let T : ClosedSubgroup G := ⟨K, hKClosed⟩
  have : CompactSpace ↥K := by
    exact hKClosed.isClosedEmbedding_subtypeVal.compactSpace
  let : IsMulTorsionFree ↥K :=
    isMulTorsionFree_of_isAbTorsionFree_isMulCommutative (G := ↥K) hKab
  exact isTorsionFreeGroup_of_isMulTorsionFree (G := ↥K)

/-- An abelianization-torsion-free profinite group is torsion-free. -/
theorem isTorsionFreeGroup_of_isAbTorsionFree
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsAbTorsionFree G) :
    IsTorsionFreeGroup G := by
  intro g hg
  have hKClosed : IsClosed (((Subgroup.zpowers g : Subgroup G) : Set G)) := by
    simpa using
      (show (((Subgroup.zpowers g : Subgroup G) : Set G)).Finite from by
        exact Set.finite_coe_iff.mp ((finite_zpowers (a := g)).2 hg)).isClosed
  have hKtf : IsTorsionFreeGroup ↥(Subgroup.zpowers g) :=
    isTorsionFreeGroup_of_isAbTorsionFree_of_closedCommSubgroup
      (G := G) (K := Subgroup.zpowers g) hKClosed hG
  let x : Subgroup.zpowers g := ⟨g, Subgroup.mem_zpowers g⟩
  have hxfin : IsOfFinOrder x := by
    rw [← Submonoid.isOfFinOrder_coe]
    simpa [x] using hg
  have hx : x = 1 := hKtf x hxfin
  simpa [x] using congrArg Subtype.val hx

/--
Maximal finite-step solvable quotients of an abelianization-torsion-free profinite group are
torsion-free.
-/
theorem isTorsionFreeGroup_maxSolvQuot_of_isAbTorsionFree
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsAbTorsionFree G)
    {m : ℕ} (hm : 1 ≤ m) :
    IsTorsionFreeGroup (MaxSolvQuot G m) := by
  refine Nat.strong_induction_on m ?_ hm
  intro m ih hm
  cases m with
  | zero =>
      cases hm
  | succ m =>
      cases m with
      | zero =>
          let : IsMulTorsionFree (MaxSolvQuot G 1) :=
            isMulTorsionFree_maxSolvQuot_one_of_isMulTorsionFree_topologicalAbelianization
              G (isMulTorsionFree_topologicalAbelianization_of_isAbTorsionFree (G := G) hG)
          exact isTorsionFreeGroup_of_isMulTorsionFree (G := MaxSolvQuot G 1)
      | succ m =>
          let D1 : Subgroup G := topDerivedTop G (m + 1)
          let D2 : Subgroup G := topDerivedTop G (m + 2)
          have hD2_le_D1 : D2 ≤ D1 := by
            dsimp [D1, D2, topDerivedTop]
            exact topDerivedTop_antitone (G := G) (Nat.le_succ (m + 1))
          have hprev : IsTorsionFreeGroup (MaxSolvQuot G (m + 1)) := by
            apply ih (m + 1)
            · exact Nat.lt_succ_self (m + 1)
            · exact Nat.succ_le_succ (Nat.zero_le m)
          let π : MaxSolvQuot G (m + 2) →* MaxSolvQuot G (m + 1) :=
            QuotientGroup.map D2 D1 (MonoidHom.id G) (by exact hD2_le_D1)
          have hD1Closed : IsClosed (D1 : Set G) := by
            infer_instance
          have hD1ab : IsAbTorsionFree ↥D1 :=
            isAbTorsionFree_closedSubgroup (G := G) hG hD1Closed
          have hbaseTF : IsMulTorsionFree (MaxSolvQuot D1 1) := by
            exact
              isMulTorsionFree_maxSolvQuot_one_of_isMulTorsionFree_topologicalAbelianization
                D1
                (isMulTorsionFree_topologicalAbelianization_of_isAbTorsionFree
                  (G := D1) hD1ab)
          have hsub :
              D2.subgroupOf D1 = topDerivedTop D1 1 := by
            have hmap : (topDerivedTop D1 1).map D1.subtype = D2 := by
              have hmapTop : ((⊤ : Subgroup D1).map D1.subtype) = D1 := by
                ext x
                constructor
                · rintro ⟨y, -, rfl⟩
                  exact y.2
                · intro hx
                  exact ⟨⟨x, hx⟩, by simp only [Subgroup.coe_top, Set.mem_univ], rfl⟩
              calc
                (topDerivedTop D1 1).map D1.subtype =
                    closedDerivedSeries (G := G) (((⊤ : Subgroup D1).map D1.subtype)) 1 := by
                      simpa [topDerivedTop] using
                        (topDerived_one_map_subtype_eq_of_isClosed_subgroup
                          (G := G) (H := D1) (K := (⊤ : Subgroup D1)) hD1Closed)
                _ = closedDerivedSeries (G := G) D1 1 := by simp only [hmapTop,
                    closedDerivedSeries_succ, closedDerivedSeries_zero]
                _ = D2 := by
                      simp only [closedDerivedSeries, closedDerivedSeries_succ, D1, D2]
            apply (Subgroup.map_injective D1.subtype_injective)
            calc
              (D2.subgroupOf D1).map D1.subtype = D2 := Subgroup.map_subgroupOf_eq_of_le hD2_le_D1
              _ = (topDerivedTop D1 1).map D1.subtype := hmap.symm
          have hquotTF : IsMulTorsionFree (D1 ⧸ D2.subgroupOf D1) := by
            let e : D1 ⧸ D2.subgroupOf D1 ≃* MaxSolvQuot D1 1 :=
              QuotientGroup.quotientMulEquivOfEq hsub
            exact e.symm.isMulTorsionFree
          have hmapTF' : IsMulTorsionFree ↥(Subgroup.map (QuotientGroup.mk' D2) D1) := by
            let φ : D1 →* Subgroup.map (QuotientGroup.mk' D2) D1 :=
              { toFun := fun x => ⟨QuotientGroup.mk' D2 x, ⟨x, x.2, rfl⟩⟩
                map_one' := by ext; rfl
                map_mul' := by intro x y; ext; rfl }
            have hφSurj : Function.Surjective φ := by
              rintro ⟨y, x, hx, rfl⟩
              refine ⟨⟨x, hx⟩, ?_⟩
              ext
              rfl
            have hφKer : φ.ker = D2.subgroupOf D1 := by
              ext x
              constructor
              · intro hx
                have hx' : φ x = 1 := hx
                have hx'' : QuotientGroup.mk' D2 (x : G) = 1 := congrArg Subtype.val hx'
                exact (QuotientGroup.eq_one_iff (N := D2) (x : G)).1 hx''
              · intro hx
                change φ x = 1
                apply Subtype.ext
                exact (QuotientGroup.eq_one_iff (N := D2) (x : G)).2 hx
            let e : D1 ⧸ D2.subgroupOf D1 ≃* Subgroup.map (QuotientGroup.mk' D2) D1 :=
              (QuotientGroup.quotientMulEquivOfEq hφKer.symm).trans
                (QuotientGroup.quotientKerEquivOfSurjective φ hφSurj)
            exact e.isMulTorsionFree
          have hkerTF : IsTorsionFreeGroup ↥(π.ker) := by
            have hker : π.ker = Subgroup.map (QuotientGroup.mk' D2) D1 := by
              simpa [π] using
                (QuotientGroup.ker_map (N := D2) (M := D1) (f := MonoidHom.id G) (by
                  exact hD2_le_D1))
            let eKer : π.ker ≃* Subgroup.map (QuotientGroup.mk' D2) D1 :=
              { toFun := fun x => ⟨x.1, by simpa [hker] using x.2⟩
                invFun := fun x => ⟨x.1, by rw [hker]; exact x.2⟩
                left_inv := by intro x; ext; rfl
                right_inv := by intro x; ext; rfl
                map_mul' := by intro x y; ext; rfl }
            let : IsMulTorsionFree ↥(π.ker) := eKer.symm.isMulTorsionFree
            exact isTorsionFreeGroup_of_isMulTorsionFree (G := ↥(π.ker))
          intro z hz
          have hzπ : IsOfFinOrder (π z) := MonoidHom.isOfFinOrder π hz
          have hzπ1 : π z = 1 := hprev (π z) hzπ
          have hzk : z ∈ π.ker := hzπ1
          let zk : π.ker := ⟨z, hzk⟩
          have hzkFin : IsOfFinOrder zk := by
            rw [← Submonoid.isOfFinOrder_coe]
            simpa [zk] using hz
          have hzk1 : zk = 1 := hkerTF zk hzkFin
          simpa [zk] using congrArg Subtype.val hzk1

/-- Closed subgroups of an abelianization-torsion-free profinite group are torsion-free. -/
theorem isTorsionFreeGroup_of_isAbTorsionFree_of_closedSubgroup
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {K : Subgroup G} (hKClosed : IsClosed (K : Set G))
    (hG : IsAbTorsionFree G) :
    IsTorsionFreeGroup ↥K := by
  have : CompactSpace ↥K := hKClosed.isClosedEmbedding_subtypeVal.compactSpace
  have hKab : IsAbTorsionFree ↥K :=
    isAbTorsionFree_closedSubgroup (G := G) (K := K) hG hKClosed
  exact isTorsionFreeGroup_of_isAbTorsionFree (G := ↥K) hKab

/-- Slimness is equivalent to every open subgroup being center-free. -/
theorem isSlim_iff_openSubgroups_center_eq_bot
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G] :
    IsSlim G ↔ ∀ H : OpenSubgroup G, Subgroup.center ↥((H : Subgroup G)) = ⊥ := by
  constructor
  · intro hslim H
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    have hzcent :
        ((z : ↥((H : Subgroup G))) : G) ∈
          Subgroup.centralizer ((H : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz) ⟨y, hy⟩)
    have hzbot : ((z : ↥((H : Subgroup G))) : G) ∈ (⊥ : Subgroup G) := by
      simpa [hslim H] using hzcent
    exact Subtype.ext (by simpa using hzbot)
  · intro hcenter H
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    let a : G := (z : G)
    let V : Subgroup G := (H : Subgroup G) ⊔ Subgroup.zpowers a
    have hVopen : IsOpen (V : Set G) := by
      exact Subgroup.isOpen_of_openSubgroup V (show (H : Subgroup G) ≤ V from le_sup_left)
    let Vopen : OpenSubgroup G := { toSubgroup := V, isOpen' := hVopen }
    have haV : a ∈ V := by
      exact
        (le_sup_right : Subgroup.zpowers a ≤ V)
          (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp only [zpow_one]⟩)
    have hHc : (H : Subgroup G) ≤ Subgroup.centralizer ({a} : Set G) := by
      intro h hh
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      exact (Subgroup.mem_centralizer_iff.mp hz (h : G) hh).symm
    have hza : Subgroup.zpowers a ≤ Subgroup.centralizer ({a} : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rcases Set.mem_singleton_iff.mp hy with rfl
      rcases Subgroup.mem_zpowers_iff.mp hx with ⟨n, rfl⟩
      exact (Commute.refl a).zpow_right n |>.eq
    have hVle : V ≤ Subgroup.centralizer ({a} : Set G) := sup_le hHc hza
    have hacenter : (⟨a, haV⟩ : V) ∈ Subgroup.center ↥V := by
      rw [Subgroup.mem_center_iff]
      intro x
      have hxcent : x.1 ∈ Subgroup.centralizer ({a} : Set G) := hVle x.2
      have hxeq : x.1 * a = a * x.1 := by
        exact (Subgroup.mem_centralizer_iff.mp hxcent a (by simp only [Set.mem_singleton_iff])).symm
      ext
      exact hxeq
    have hcenV : Subgroup.center ↥((Vopen : OpenSubgroup G) : Subgroup G) = ⊥ := hcenter Vopen
    have hgoneV : (⟨a, haV⟩ : V) = 1 := by
      rw [show Vopen.toSubgroup = V by rfl] at hcenV
      rw [hcenV] at hacenter
      simpa using hacenter
    exact congrArg Subtype.val hgoneV

/-- Slimness forces all open subgroups to be center-free. -/
theorem openSubgroup_center_eq_bot_of_isSlim
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (hslim : IsSlim G) (H : OpenSubgroup G) :
    Subgroup.center ↥((H : Subgroup G)) = ⊥ :=
  (isSlim_iff_openSubgroups_center_eq_bot (G := G)).1 hslim H

/-- Center-freeness of all open subgroups implies slimness. -/
theorem isSlim_of_openSubgroups_center_eq_bot
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (hcenter : ∀ H : OpenSubgroup G, Subgroup.center ↥((H : Subgroup G)) = ⊥) :
    IsSlim G :=
  (isSlim_iff_openSubgroups_center_eq_bot (G := G)).2 hcenter

/-- Faithfulness of the abelianized action implies slimness. -/
theorem isSlim_of_isAbFaithful
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hG : IsAbFaithful G) :
    IsSlim G := by
  rw [isSlim_iff_openSubgroups_center_eq_bot]
  intro H
  exact ProCGroups.FiniteStepSolvableQuotients.openSubgroup_center_eq_bot_of_isAbFaithful
    (G := G) hG H

/--
If the quotient action on the topological abelianization is trivial on a finite-index subgroup,
then the acting element already lies in the open normal subgroup.
-/
theorem mem_openNormal_of_action_trivial_on_finiteIndexSubgroup
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    (U : OpenNormalSubgroup Q)
    (hUtf : IsMulTorsionFree (TopologicalAbelianization ↥(U : Subgroup Q)))
    (hρinj :
      Function.Injective
        (quotientConjugationTopologicalAbelianizationMap (G := Q) (N := (U : Subgroup Q))))
    {c : Q}
    (B : Subgroup (TopologicalAbelianization ↥(U : Subgroup Q))) [B.FiniteIndex]
    (htriv :
      ∀ a : TopologicalAbelianization ↥(U : Subgroup Q),
        a ∈ B →
          quotientConjugationTopologicalAbelianizationMap (G := Q) (N := (U : Subgroup Q))
            (QuotientGroup.mk' (U : Subgroup Q) c) a = a) :
    c ∈ (U : Subgroup Q) := by
  let ρ :
      (Q ⧸ (U : Subgroup Q)) →*
        MulAut (TopologicalAbelianization ↥(U : Subgroup Q)) :=
    quotientConjugationTopologicalAbelianizationMap (G := Q) (N := (U : Subgroup Q))
  have hρc : ρ (QuotientGroup.mk' (U : Subgroup Q) c) = 1 := by
    exact
      eq_one_mulAut_of_forall_mem_subgroup
        (φ := ρ (QuotientGroup.mk' (U : Subgroup Q) c)) (B := B) htriv
  have hρone : ρ (QuotientGroup.mk' (U : Subgroup Q) (1 : Q)) = 1 := by
    dsimp [ρ]
    exact
      quotientConjugationTopologicalAbelianizationMap_mk_eq_one_of_mem_center
        (G := Q) (N := (U : Subgroup Q)) (x := (1 : Q)) (by
          rw [Subgroup.mem_center_iff]
          intro y
          simp only [mul_one, one_mul])
  exact
    (QuotientGroup.eq_one_iff (N := (U : Subgroup Q)) c).1 <|
      hρinj (hρc.trans hρone.symm)

/--
If the images of \(S\cap U\) have finite index in \(\operatorname{Ab}(U)\) for every open normal
supergroup of \(K\), then the centralizer of \(S\) is contained in \(K\).
-/
theorem centralizer_subgroup_le_of_torsionFree_and_inj_action_on_openNormalSupergroups
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [TotallyDisconnectedSpace Q]
    {K : Subgroup Q} (hKClosed : IsClosed (K : Set Q)) (hKNormal : K.Normal)
    (hTF :
      ∀ U : OpenNormalSubgroup Q, K ≤ (U : Subgroup Q) →
        IsMulTorsionFree (TopologicalAbelianization ↥(U : Subgroup Q)))
    (hFaithful :
      ∀ U : OpenNormalSubgroup Q, K ≤ (U : Subgroup Q) →
        Function.Injective
          (quotientConjugationTopologicalAbelianizationMap
            (G := Q) (N := (U : Subgroup Q))))
    (S : Subgroup Q)
    (hLarge :
      ∀ U : OpenNormalSubgroup Q, K ≤ (U : Subgroup Q) →
        Finite
          ((TopologicalAbelianization ↥(U : Subgroup Q)) ⧸
            subgroupImageInTopologicalAbelianization (Q := Q) S U)) :
    Subgroup.centralizer (S : Set Q) ≤ K := by
  let Kclosed : ClosedSubgroup Q := ⟨K, hKClosed⟩
  have hK_eq :
      K =
        sInf {N : Subgroup Q | IsOpen (N : Set Q) ∧ K ≤ N ∧ N.Normal} := by
    change (Kclosed : Subgroup Q) =
      sInf {N : Subgroup Q | IsOpen (N : Set Q) ∧ K ≤ N ∧ N.Normal}
    exact ProCGroups.ProC.closedSubgroup_eq_sInf_openNormal (G := Q) Kclosed
  intro c hc
  rw [hK_eq]
  simp only [Subgroup.mem_sInf]
  intro N hN
  let U : OpenNormalSubgroup Q :=
    { toSubgroup := N
      isOpen' := hN.1
      isNormal' := hN.2.2 }
  have hUNormal : (U : Subgroup Q).Normal := U.isNormal'
  let B : Subgroup (TopologicalAbelianization ↥(U : Subgroup Q)) :=
    subgroupImageInTopologicalAbelianization (Q := Q) S U
  let : Finite ((TopologicalAbelianization ↥(U : Subgroup Q)) ⧸ B) := hLarge U hN.2.1
  let : B.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient (H := B)
  exact
    mem_openNormal_of_action_trivial_on_finiteIndexSubgroup
      (Q := Q) U (hTF U hN.2.1) (hFaithful U hN.2.1) (c := c) (B := B) (by
        intro a ha
        rcases ha with ⟨x, hx, rfl⟩
        have hxSU : (x : Q) ∈ S ⊓ (U : Subgroup Q) := by
          simpa [Subgroup.mem_subgroupOf] using hx
        have hxS : (x : Q) ∈ S := hxSU.1
        have hcomm : c * (x : Q) = (x : Q) * c := by
          exact (Subgroup.mem_centralizer_iff.mp hc (x : Q) hxS).symm
        exact
          quotientConjAbMap_apply_mk_of_commute
            (G := Q) (N := (U : Subgroup Q)) (g := c) (x := x) hcomm)

/--
The centralizer of an open subgroup is contained in \(K\) whenever every open normal supergroup
of \(K\) has torsion-free abelianization and faithful quotient action.
-/
theorem centralizer_openSubgroup_le_of_torsionFree_and_inj_action_on_openNormalSupergroups
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [TotallyDisconnectedSpace Q]
    {K : Subgroup Q} (hKClosed : IsClosed (K : Set Q)) (hKNormal : K.Normal)
    (hTF :
      ∀ U : OpenNormalSubgroup Q, K ≤ (U : Subgroup Q) →
        IsMulTorsionFree (TopologicalAbelianization ↥(U : Subgroup Q)))
    (hFaithful :
      ∀ U : OpenNormalSubgroup Q, K ≤ (U : Subgroup Q) →
        Function.Injective
          (quotientConjugationTopologicalAbelianizationMap
            (G := Q) (N := (U : Subgroup Q))))
    (H : OpenSubgroup Q) :
    Subgroup.centralizer (H : Set Q) ≤ K := by
  refine
    centralizer_subgroup_le_of_torsionFree_and_inj_action_on_openNormalSupergroups
      (Q := Q) (K := K) hKClosed hKNormal hTF hFaithful (S := (H : Subgroup Q)) ?_
  intro U hKU
  let SU : OpenSubgroup ↥(U : Subgroup Q) :=
    OpenSubgroup.comap ((U : Subgroup Q).subtype) continuous_subtype_val H
  let A : Type u := TopologicalAbelianization ↥(U : Subgroup Q)
  let B : Subgroup A :=
    subgroupImageInTopologicalAbelianization (Q := Q) (S := (H : Subgroup Q)) U
  have hBOpen : IsOpen (B : Set A) := by
    have hsourceOpen :
        IsOpen
          (((((H : Subgroup Q) ⊓ (U : Subgroup Q)).subgroupOf
            (U : Subgroup Q)) : Subgroup ↥(U : Subgroup Q)) :
              Set ↥(U : Subgroup Q)) := by
      rw [Subgroup.inf_subgroupOf_right]
      exact SU.isOpen'
    have hopen :=
      QuotientGroup.isOpenMap_coe
        (N := Subgroup.closedCommutator (U : Subgroup Q))
        _ hsourceOpen
    change IsOpen
      ((TopologicalAbelianization.mk ↥(U : Subgroup Q)) ''
        (((((H : Subgroup Q) ⊓ (U : Subgroup Q)).subgroupOf
          (U : Subgroup Q)) : Subgroup ↥(U : Subgroup Q)) :
            Set ↥(U : Subgroup Q))) at hopen
    simpa [B, subgroupImageInTopologicalAbelianization, A] using hopen
  have hUClosed : IsClosed ((U : Subgroup Q) : Set Q) := U.isClosed
  have : CompactSpace ↥(U : Subgroup Q) := by
    exact hUClosed.isClosedEmbedding_subtypeVal.compactSpace
  let : CompactSpace A := by
    dsimp [A]
    infer_instance
  exact Subgroup.quotient_finite_of_isOpen B hBOpen

/--
If the topological closure of S is open, then the centralizer of S is already contained in K
under the same torsion-free and faithful hypotheses.
-/
theorem centralizer_subgroup_le_of_open_topologicalClosure
    {Q : Type u} [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    {K S : Subgroup Q} (hKClosed : IsClosed (K : Set Q)) (hKNormal : K.Normal)
    (hTF :
      ∀ U : OpenNormalSubgroup Q, K ≤ (U : Subgroup Q) →
        IsMulTorsionFree (TopologicalAbelianization ↥(U : Subgroup Q)))
    (hFaithful :
      ∀ U : OpenNormalSubgroup Q, K ≤ (U : Subgroup Q) →
        Function.Injective
          (quotientConjugationTopologicalAbelianizationMap
            (G := Q) (N := (U : Subgroup Q))))
    (hSOpen : IsOpen (((S.topologicalClosure : Subgroup Q) : Set Q))) :
    Subgroup.centralizer (S : Set Q) ≤ K := by
  let H : OpenSubgroup Q := ⟨S.topologicalClosure, hSOpen⟩
  have hH :
      Subgroup.centralizer (((S.topologicalClosure : Subgroup Q) : Set Q)) ≤ K := by
    have hraw :=
      centralizer_openSubgroup_le_of_torsionFree_and_inj_action_on_openNormalSupergroups
        (Q := Q) (K := K) hKClosed hKNormal hTF hFaithful H
    have hset :
        (H : Set Q) = (((S.topologicalClosure : Subgroup Q) : Set Q)) := by
      rfl
    rw [hset] at hraw
    exact hraw
  intro g hg
  have hg' : g ∈ Subgroup.centralizer (((S.topologicalClosure : Subgroup Q) : Set Q)) := by
    have hcentralizer :
        Subgroup.centralizer (((S.topologicalClosure : Subgroup Q) : Set Q)) =
          Subgroup.centralizer (S : Set Q) := by
      simpa [ProCGroups.GroupTheory.centralizer] using
        ProCGroups.GroupTheory.centralizer_eq_centralizer_topologicalClosure (G := Q) S
    rw [hcentralizer]
    exact hg
  exact hH hg'

/--
The inclusion into the topological abelianization is compatible with the finite quotient
construction.
-/
noncomputable def topologicalAbelianizationInclusion
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    {S T : Subgroup G} (hST : S ≤ T) :
    TopologicalAbelianization ↥S →ₜ* TopologicalAbelianization ↥T :=
  TopologicalAbelianization.map
    { toMonoidHom := Subgroup.inclusion hST
      continuous_toFun := by
        exact Continuous.subtype_mk continuous_subtype_val (fun x => hST x.2) }

/--
If the ambient inclusion into topological abelianization is trivial on a fixed point, then the
fixed point itself is trivial under torsion-freeness.
-/
theorem fixedPoint_eq_one_of_openNormal_torsionFreeAb
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    (N : OpenNormalSubgroup G) [Finite (G ⧸ (N : Subgroup G))]
    (hNtf : IsMulTorsionFree (TopologicalAbelianization ↥(N : Subgroup G)))
    {a : TopologicalAbelianization ↥(N : Subgroup G)}
    (hfix :
      ∀ q : G ⧸ (N : Subgroup G),
        quotientConjugationTopologicalAbelianizationMap (G := G) (N := (N : Subgroup G)) q a = a)
    (ha :
      TopologicalAbelianization.map
        { toMonoidHom := (N : Subgroup G).subtype
          continuous_toFun := continuous_subtype_val } a = 1) :
    a = 1 := by
  classical
  let : Fintype (G ⧸ (N : Subgroup G)) := Fintype.ofFinite _
  have hpow :=
    openNormalTransferTopologicalAbelianization_eq_pow_of_fixed (G := G) N hfix
  have hpow' :
      openNormalTransferTopologicalAbelianization (G := G) N
        (TopologicalAbelianization.map
          { toMonoidHom := (N : Subgroup G).subtype
            continuous_toFun := continuous_subtype_val } a) =
        a ^ Nat.card (G ⧸ (N : Subgroup G)) := by
    simpa [Nat.card_eq_fintype_card] using hpow
  have hpow1 : a ^ Nat.card (G ⧸ (N : Subgroup G)) = 1 := by
    calc
      a ^ Nat.card (G ⧸ (N : Subgroup G)) =
          openNormalTransferTopologicalAbelianization (G := G) N
            (TopologicalAbelianization.map
              { toMonoidHom := (N : Subgroup G).subtype
                continuous_toFun := continuous_subtype_val } a) := by
              rw [hpow']
      _ = openNormalTransferTopologicalAbelianization (G := G) N 1 := by
            rw [ha]
      _ = 1 := by
            simp only [openNormalTransferTopologicalAbelianization, map_one]
  have hcard : Nat.card (G ⧸ (N : Subgroup G)) ≠ 0 := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_ne_zero
  have hpowEq :
      a ^ Nat.card (G ⧸ (N : Subgroup G)) =
        (1 : TopologicalAbelianization ↥(N : Subgroup G)) ^ Nat.card (G ⧸ (N : Subgroup G)) := by
    simpa using hpow1
  exact
    (IsMulTorsionFree.pow_left_injective
      (M := TopologicalAbelianization ↥(N : Subgroup G)) hcard) hpowEq

/--
A nontrivial class in \(\operatorname{Ab}(K)\) survives in the abelianization of some open
normal supergroup of \(K\).
-/
theorem exists_openNormalSubgroup_nontrivial_topologicalAbelianizationInclusion
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {K : Subgroup G} (hKClosed : IsClosed (K : Set G)) (hKNormal : K.Normal)
    {a : TopologicalAbelianization ↥K} (hne : a ≠ 1) :
    ∃ H : OpenNormalSubgroup G, ∃ hKH : K ≤ (H : Subgroup G),
      topologicalAbelianizationInclusion hKH a ≠ 1 := by
  classical
  let T : ClosedSubgroup G := ⟨K, hKClosed⟩
  have : CompactSpace ↥K := by
    exact hKClosed.isClosedEmbedding_subtypeVal.compactSpace
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.closedCommutator K) a
  let A := TopologicalAbelianization ↥K
  have hxne : TopologicalAbelianization.mk ↥K x ≠ 1 := hne
  let C : Subgroup ↥K := Subgroup.closedCommutator K
  let : C.Normal := by dsimp [C]; infer_instance
  have hCclosed : IsClosed (C : Set ↥K) := by
    simp [C]
  let : CompactSpace A := by
    simpa [A, C] using (inferInstance : CompactSpace (↥K ⧸ C))
  let : T2Space A := by
    simpa [A, C] using (inferInstance : T2Space (↥K ⧸ C))
  let : TotallyDisconnectedSpace A := by
    simpa [A, C] using
      (ProCGroups.totallyDisconnectedSpace_quotient_closedNormal C hCclosed)
  obtain ⟨Uab, hxUab⟩ :=
    ProCGroups.ProC.exists_openNormalSubgroup_not_mem (G := A) hxne
  let qA : A →* A ⧸ (Uab : Subgroup A) := QuotientGroup.mk' (Uab : Subgroup A)
  have hqAx_ne : qA (TopologicalAbelianization.mk ↥K x) ≠ 1 := by
    intro hq
    exact hxUab ((QuotientGroup.eq_one_iff (N := (Uab : Subgroup A))
      (TopologicalAbelianization.mk ↥K x)).1 hq)
  let N0 : OpenNormalSubgroup ↥K :=
    OpenNormalSubgroup.comap
      (TopologicalAbelianization.mk ↥K)
      (by
        exact (TopologicalAbelianization.mkₜ ↥K).continuous_toFun) Uab
  have hN0ker :
      (N0 : Subgroup ↥K) ≤ (qA.comp (TopologicalAbelianization.mk ↥K)).ker := by
    intro y hy
    change qA (TopologicalAbelianization.mk ↥K y) = 1
    exact (QuotientGroup.eq_one_iff (N := (Uab : Subgroup A))
      (TopologicalAbelianization.mk ↥K y)).2 hy
  obtain ⟨V, hVK⟩ :=
    exists_openNormalSubgroup_inter_closedSubgroup_le (G := G) T N0.toOpenSubgroup
  let Hsub : Subgroup G := K ⊔ (V : Subgroup G)
  have hHopen : IsOpen (Hsub : Set G) := by
    exact Subgroup.isOpen_of_openSubgroup Hsub
      (show (V : Subgroup G) ≤ Hsub from le_sup_right)
  let H : OpenNormalSubgroup G :=
    { toOpenSubgroup := ⟨Hsub, hHopen⟩
      isNormal' := by
        change (K ⊔ (V : Subgroup G)).Normal
        infer_instance }
  have hKH : K ≤ (H : Subgroup G) := le_sup_left
  let ι : ↥K →* ↥(H : Subgroup G) := Subgroup.inclusion hKH
  let qT : ↥K →* A ⧸ (Uab : Subgroup A) :=
    qA.comp (TopologicalAbelianization.mk ↥K)
  let VK : OpenNormalSubgroup ↥K :=
    OpenNormalSubgroup.comap (K.subtype) continuous_subtype_val V
  have hVKker : (VK : Subgroup ↥K) ≤ qT.ker := by
    exact (show (VK : Subgroup ↥K) ≤ (N0 : Subgroup ↥K) from hVK).trans hN0ker
  let L : Subgroup (G ⧸ (V : Subgroup G)) :=
    Subgroup.map (QuotientGroup.mk' (V : Subgroup G)) K
  let ψ : ↥K →* L :=
    { toFun := fun y => ⟨QuotientGroup.mk' (V : Subgroup G) y.1, ⟨y.1, y.2, rfl⟩⟩
      map_one' := by ext; rfl
      map_mul' := by intro y z; ext; rfl }
  have hψsurj : Function.Surjective ψ := by
    intro z
    rcases z with ⟨z, hz⟩
    rcases hz with ⟨y, hy, hyz⟩
    refine ⟨⟨y, hy⟩, ?_⟩
    apply Subtype.ext
    exact hyz
  have hψker : (VK : Subgroup ↥K) = ψ.ker := by
    ext y
    constructor
    · intro hy
      change ψ y = 1
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (N := (V : Subgroup G)) y.1).2 hy
    · intro hy
      exact (QuotientGroup.eq_one_iff (N := (V : Subgroup G)) y.1).1 <| congrArg Subtype.val hy
  let qTquot : ↥K ⧸ ψ.ker →* A ⧸ (Uab : Subgroup A) :=
    QuotientGroup.lift ψ.ker qT (by simpa [hψker] using hVKker)
  let qL : L →* A ⧸ (Uab : Subgroup A) :=
    qTquot.comp (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).symm.toMonoidHom
  have hLdisc : DiscreteTopology L := by infer_instance
  let qLcont : L →ₜ* A ⧸ (Uab : Subgroup A) :=
    { toMonoidHom := qL
      continuous_toFun := continuous_of_discreteTopology }
  let qHaux : ↥(H : Subgroup G) →* L :=
    { toFun := fun y =>
        ⟨QuotientGroup.mk' (V : Subgroup G) y.1, by
          have hyHsub : y.1 ∈ Hsub := y.2
          have hydecomp : ∃ t ∈ K, ∃ v ∈ (V : Subgroup G), t * v = y.1 := by
            exact (Subgroup.mem_sup_of_normal_right
              (s := K) (t := (V : Subgroup G)) (x := y.1)).1 hyHsub
          change QuotientGroup.mk' (V : Subgroup G) y.1 ∈
            Subgroup.map (QuotientGroup.mk' (V : Subgroup G)) K
          rcases hydecomp with ⟨t, htK, v, hvV, htv⟩
          have hv1 : QuotientGroup.mk' (V : Subgroup G) v = 1 := by
            exact (QuotientGroup.eq_one_iff (N := (V : Subgroup G)) v).2 hvV
          refine ⟨t, htK, ?_⟩
          calc
            QuotientGroup.mk' (V : Subgroup G) t =
                QuotientGroup.mk' (V : Subgroup G) t * 1 := by simp only
                    [QuotientGroup.mk'_apply, mul_one]
            _ =
                QuotientGroup.mk' (V : Subgroup G) t *
                  QuotientGroup.mk' (V : Subgroup G) v := by rw [hv1]
            _ = QuotientGroup.mk' (V : Subgroup G) (t * v) := by rw [map_mul]
            _ = QuotientGroup.mk' (V : Subgroup G) y.1 := by rw [htv]⟩
      map_one' := by ext; rfl
      map_mul' := by intro y z; ext; rfl }
  let qH : ↥(H : Subgroup G) →ₜ* A ⧸ (Uab : Subgroup A) :=
    { toMonoidHom := qL.comp qHaux
      continuous_toFun := by
        have hqHaux : Continuous qHaux := by
          exact Continuous.subtype_mk
            (by
              change Continuous
                (fun y : ↥(H : Subgroup G) =>
                  QuotientGroup.mk' (V : Subgroup G) y.1)
              exact QuotientGroup.continuous_mk.comp continuous_subtype_val)
            (fun y => (qHaux y).2)
        exact qLcont.continuous_toFun.comp hqHaux }
  have hqH_on_K : ∀ y : ↥K, qH (ι y) = qT y := by
    intro y
    change qL (qHaux (ι y)) = qT y
    have hqHaux : qHaux (ι y) = ψ y := by
      apply Subtype.ext
      rfl
    rw [hqHaux]
    change qTquot ((QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).symm (ψ y)) = qT y
    have hmk :
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).symm (ψ y) =
          QuotientGroup.mk' ψ.ker y := by
      apply (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).injective
      rw [MulEquiv.apply_symm_apply]
      exact
        (show
          (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)
            ((QuotientGroup.mk' ψ.ker) y) = ψ y by
          rfl).symm
    rw [hmk]
    rfl
  let fAb : TopologicalAbelianization ↥K →ₜ*
      TopologicalAbelianization ↥(H : Subgroup G) :=
    topologicalAbelianizationInclusion hKH
  have hclosedBot :
      IsClosed (((⊥ : Subgroup (A ⧸ (Uab : Subgroup A))) : Set (A ⧸ (Uab : Subgroup A)))) := by
    change IsClosed ({(1 : A ⧸ (Uab : Subgroup A))} : Set (A ⧸ (Uab : Subgroup A)))
    exact isClosed_singleton
  have hcommMapBot :
      (commutator ↥(H : Subgroup G)).map (qH : ↥(H : Subgroup G) →* A ⧸ (Uab : Subgroup A)) ≤
        (⊥ : Subgroup (A ⧸ (Uab : Subgroup A))) := by
    rw [_root_.map_commutator_eq]
    refine Subgroup.commutator_le.mpr ?_
    intro a ha b hb
    change ⁅a, b⁆ = (1 : A ⧸ (Uab : Subgroup A))
    exact commutatorElement_eq_one_iff_mul_comm.2 (mul_comm a b)
  have hcommClosureBot :
      (Subgroup.closedCommutator (H : Subgroup G)).map
          (qH : ↥(H : Subgroup G) →* A ⧸ (Uab : Subgroup A)) ≤
        (⊥ : Subgroup (A ⧸ (Uab : Subgroup A))) := by
    exact TopologicalGroup.map_closure_le_of_map_le
      (f := qH)
      (G₁ := commutator ↥(H : Subgroup G))
      (Q₁ := (⊥ : Subgroup (A ⧸ (Uab : Subgroup A))))
      hcommMapBot
      hclosedBot
  have hbne : fAb (TopologicalAbelianization.mk ↥K x) ≠ 1 := by
    intro hb
    have hxcomm : ι x ∈ Subgroup.closedCommutator (H : Subgroup G) := by
      have hb' : TopologicalAbelianization.mk ↥(H : Subgroup G) (ι x) = 1 := by
        change topologicalAbelianizationInclusion hKH (TopologicalAbelianization.mk ↥K x) = 1 at hb
        rw [topologicalAbelianizationInclusion,
          TopologicalAbelianization.map_apply_mk] at hb
        have hιx :
            ι x = (Subgroup.inclusion hKH) x := by
          rfl
        rw [hιx]
        exact hb
      exact
        (QuotientGroup.eq_one_iff
          (N := Subgroup.closedCommutator (H : Subgroup G))
          (ι x)).1 hb'
    have hxmap :
        qH (ι x) ∈
          (Subgroup.closedCommutator (H : Subgroup G)).map
            (qH : ↥(H : Subgroup G) →* A ⧸ (Uab : Subgroup A)) := ⟨ι x, hxcomm, rfl⟩
    have hxbot : qH (ι x) ∈ (⊥ : Subgroup (A ⧸ (Uab : Subgroup A))) := hcommClosureBot hxmap
    have hqHx : qH (ι x) = 1 := by
      simpa using hxbot
    have hqTx : qT x = 1 := by
      simpa [hqH_on_K x] using hqHx
    exact hqAx_ne (by simpa [qT] using hqTx)
  refine ⟨H, hKH, ?_⟩
  change fAb (TopologicalAbelianization.mk ↥K x) ≠ 1
  exact hbne

/--
If every open normal supergroup of \(K\) has torsion-free abelianization, then
\(\operatorname{Ab}(K)\) has no nontrivial fixed points under the quotient conjugation action.
-/
theorem noFixedPoints_of_torsionFree_on_openNormalSupergroups
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {K : Subgroup G} (hKClosed : IsClosed (K : Set G))
    (hKNormal : K.Normal) (hK : K ≤ topDerivedTop G 1)
    (hTF :
      ∀ H : OpenNormalSubgroup G, K ≤ (H : Subgroup G) →
        IsMulTorsionFree (TopologicalAbelianization ↥(H : Subgroup G))) :
    let _ : K.Normal := hKNormal
    HasNoNontrivialFixedPoints
      (quotientConjugationTopologicalAbelianizationMap (G := G) (N := K)) := by
  change HasNoNontrivialFixedPoints
    (quotientConjugationTopologicalAbelianizationMap (G := G) (N := K))
  intro a hfix
  by_contra hne
  obtain ⟨H, hKH, hHne⟩ :=
    exists_openNormalSubgroup_nontrivial_topologicalAbelianizationInclusion
      (G := G) (K := K) hKClosed hKNormal hne
  have hfixH :
      ∀ q : G ⧸ (H : Subgroup G),
        quotientConjugationTopologicalAbelianizationMap (G := G) (N := (H : Subgroup G)) q
            (topologicalAbelianizationInclusion hKH a) =
          topologicalAbelianizationInclusion hKH a := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (H : Subgroup G) q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.closedCommutator K) a
    have hconj :
        topologicalAbelianizationInclusion hKH
          (quotientConjugationTopologicalAbelianizationMap (G := G) (N := K)
            (QuotientGroup.mk' K g) (TopologicalAbelianization.mk ↥K x)) =
        quotientConjugationTopologicalAbelianizationMap (G := G) (N := (H : Subgroup G))
          (QuotientGroup.mk' (H : Subgroup G) g)
          (topologicalAbelianizationInclusion hKH (TopologicalAbelianization.mk ↥K x)) := by
      simp only [QuotientGroup.mk'_apply]
      change
        topologicalAbelianizationInclusion hKH
            (TopologicalAbelianization.mk ↥K ((MulAut.conjNormal g) x)) =
          TopologicalAbelianization.mk ↥(H : Subgroup G)
            ((MulAut.conjNormal g) ((Subgroup.inclusion hKH) x))
      simp only [topologicalAbelianizationInclusion, ContinuousMonoidHom.coe_toMonoidHom,
          MonoidHom.coe_ofClass]
      rfl
    exact hconj.trans
      (congrArg (topologicalAbelianizationInclusion hKH) (hfix (QuotientGroup.mk' K g)))
  have haH :
      TopologicalAbelianization.map
        { toMonoidHom := (H : Subgroup G).subtype
          continuous_toFun := continuous_subtype_val }
        (topologicalAbelianizationInclusion hKH a) = 1 := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective
      (Subgroup.closedCommutator K) a
    have hx1 : TopologicalAbelianization.mk G x.1 = 1 := by
      exact
        (QuotientGroup.eq_one_iff
          (N := Subgroup.closedCommutator G) x.1).2
          (by simpa [topDerivedTop] using hK x.2)
    change
      TopologicalAbelianization.map
        { toMonoidHom := (H : Subgroup G).subtype
          continuous_toFun := continuous_subtype_val }
        (topologicalAbelianizationInclusion hKH (TopologicalAbelianization.mk ↥K x)) = 1
    rw [topologicalAbelianizationInclusion,
      TopologicalAbelianization.map_apply_mk,
      TopologicalAbelianization.map_apply_mk]
    change TopologicalAbelianization.mk G x.1 = 1
    exact hx1
  have hHtf : IsMulTorsionFree (TopologicalAbelianization ↥(H : Subgroup G)) := hTF H hKH
  exact hHne <|
    fixedPoint_eq_one_of_openNormal_torsionFreeAb
      (G := G) H hHtf hfixH haH

/--
The local torsion-free abelianization hypothesis rules out nontrivial fixed points on every
closed normal subgroup contained in the first closed derived subgroup.
-/
theorem noFixedPoints_of_isAbTorsionFree
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {K : Subgroup G} (hKClosed : IsClosed (K : Set G))
    (hKNormal : K.Normal) (hK : K ≤ topDerivedTop G 1)
    (hG : IsAbTorsionFree G) :
    let _ : K.Normal := hKNormal
    HasNoNontrivialFixedPoints
      (quotientConjugationTopologicalAbelianizationMap (G := G) (N := K)) := by
  exact
    noFixedPoints_of_torsionFree_on_openNormalSupergroups
      (G := G) hKClosed hKNormal hK (fun H _ => hG H.toOpenSubgroup)

/--
Open subgroups above the last derived subgroup in a maximal finite-step solvable quotient have
torsion-free topological abelianization under the ambient abelianization-torsion-free
hypothesis.
-/
theorem isMulTorsionFree_topologicalAbelianization_of_aboveLastDerived_of_isAbTorsionFree
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G]
    (hG : IsAbTorsionFree G)
    {m : ℕ} (hm : 2 ≤ m)
    (H : OpenSubgroup (MaxSolvQuot G m))
    (hH : aboveLastDerived (G := G) m H) :
    IsMulTorsionFree
      (TopologicalAbelianization ↥(H : Subgroup (MaxSolvQuot G m))) := by
  let Q : Type u := MaxSolvQuot G m
  let π : G →ₜ* Q := continuousToMaxSolvQuot G m
  let Hpre : OpenSubgroup G := preimageOpenSubgroup π H
  have hπsurj : Function.Surjective π := by
    simpa [π, Q] using continuousToMaxSolvQuot_surjective (G := G) m
  have hder_pre : topDerivedTop G (m - 1) ≤ ((H : Subgroup Q).comap (π : G →* Q)) := by
    intro x hx
    exact hH ((topDerivedTop_le_comap (f := π) (m := m - 1)) hx)
  have hm1 : 1 ≤ m := le_trans (by decide) hm
  have hker :
      (π : G →* Q).ker ≤
        (topDerivedTop ↥((Hpre : Subgroup G)) 1).map ((Hpre : Subgroup G).subtype) := by
    simpa [π, Q, Hpre] using
      (continuousToMaxSolvQuot_ker_le_topDerived_one_map_subtype_of_le
        (G := G) (m := m) hm1 H (by simpa [π, Q] using hder_pre))
  have hclosed :
      IsClosedMap (ProCGroups.ContinuousMonoidHom.restrictPreimage π (H : Subgroup Q)) := by
    exact
      TopologicalGroup.restrictPreimage_isClosedMap_of_isClosedMap
        (π := π) (Q₁ := (H : Subgroup Q))
        ((continuousToMaxSolvQuot G m).continuous_toFun.isClosedMap)
        (Subgroup.isClosed_of_isOpen (H : Subgroup Q) H.isOpen')
  let e :
      MaxSolvQuot ↥((Hpre : Subgroup G)) 1 ≃*
        MaxSolvQuot ↥(H : Subgroup Q) 1 :=
    Classical.choice <|
      preimageOpenSubgroup_maxSolvQuot_mulEquiv_of_ker_le π hπsurj H hclosed 1 hker
  have hpreTF : IsMulTorsionFree (TopologicalAbelianization ↥((Hpre : Subgroup G))) := hG Hpre
  have hpreTF' : IsMulTorsionFree (MaxSolvQuot ↥((Hpre : Subgroup G)) 1) := by
    exact
      isMulTorsionFree_maxSolvQuot_one_of_isMulTorsionFree_topologicalAbelianization
        ↥((Hpre : Subgroup G)) hpreTF
  change IsMulTorsionFree (MaxSolvQuot ↥(H : Subgroup Q) 1)
  exact e.isMulTorsionFree

/--
Open normal supergroups above the last derived subgroup in a maximal finite-step solvable
quotient have torsion-free topological abelianization under the ambient
abelianization-torsion-free hypothesis.
-/
theorem isMulTorsionFree_topologicalAbelianization_of_openNormalSupergroup_of_isAbTorsionFree
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G]
    (hG : IsAbTorsionFree G)
    {m : ℕ} (hm : 2 ≤ m)
    (U : OpenNormalSubgroup (MaxSolvQuot G m))
    (hU : lastDerivedSubgroup (G := G) m ≤ (U : Subgroup (MaxSolvQuot G m))) :
    IsMulTorsionFree
      (TopologicalAbelianization ↥(U : Subgroup (MaxSolvQuot G m))) := by
  simpa using
    isMulTorsionFree_topologicalAbelianization_of_aboveLastDerived_of_isAbTorsionFree
      (G := G) hG hm U.toOpenSubgroup hU

/-- The \(m\)-th closed derived subgroup vanishes in the maximal \(m\)-step solvable quotient. -/
theorem topDerivedTop_eq_bot_maxSolvQuot
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G]
    (m : ℕ) :
    topDerivedTop (MaxSolvQuot G m) m = ⊥ := by
  let Q : Type u := MaxSolvQuot G m
  let π : G →ₜ* Q := continuousToMaxSolvQuot G m
  let : T2Space Q := by
    dsimp [Q, MaxSolvQuot]
    infer_instance
  have hπsurj : Function.Surjective π := by
    simpa [Q, π] using continuousToMaxSolvQuot_surjective (G := G) m
  have hclosed :
      ∀ n : ℕ,
        IsClosed (((closedCommutator (topDerivedTop G n) (topDerivedTop G n)).map
          (π : G →* Q) : Subgroup Q) : Set Q) := by
    intro n
    refine
      TopologicalGroup.isClosed_map_of_isClosedMap
        (f := π) ((continuousToMaxSolvQuot G m).continuous_toFun.isClosedMap)
        (K := closedCommutator (topDerivedTop G n) (topDerivedTop G n)) ?_
    exact Subgroup.isClosed_topologicalClosure (s := ⁅topDerivedTop G n, topDerivedTop G n⁆)
  have hmap := topDerived_map_eq_of_surj (f := π) hπsurj hclosed m
  calc
    topDerivedTop Q m = (topDerivedTop G m).map (π : G →* Q) := by
      symm
      simpa [Q, π] using hmap
    _ = ⊥ := by
      refine (Subgroup.map_eq_bot_iff (f := (π : G →* Q)) (H := topDerivedTop G m)).2 ?_
      intro x hx
      exact (MonoidHom.mem_ker).2
        ((continuousToMaxSolvQuot_eq_one_iff (G := G) (m := m) (x := x)).2 hx)

/--
Maximal finite-step solvable quotients are center-free under the local torsion-free and faithful
abelianization hypotheses.
-/
theorem center_eq_bot_maxSolvQuot_of_isAbTorsionFree_of_isAbFaithful
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hTorsion : IsAbTorsionFree G) (hFaithful : IsAbFaithful G)
    {m : ℕ} (hm : 2 ≤ m) :
    Subgroup.center (MaxSolvQuot G m) = ⊥ := by
  let Q : Type u := MaxSolvQuot G m
  let : CompactSpace Q := by dsimp [Q, MaxSolvQuot]; infer_instance
  let : T2Space Q := by dsimp [Q, MaxSolvQuot]; infer_instance
  let : TotallyDisconnectedSpace Q := by
    dsimp [Q, MaxSolvQuot]
    exact ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (topDerivedTop G m)
      (show IsClosed ((topDerivedTop G m : Subgroup G) : Set G) by infer_instance)
  let K : Subgroup Q := lastDerivedSubgroup (G := G) m
  let : K.Normal := by
    dsimp [K, lastDerivedSubgroup]
    infer_instance
  have hm1 : 1 ≤ m := by
    exact le_trans (by decide) hm
  have hmK : 1 ≤ m - 1 := Nat.le_sub_of_add_le hm
  have hcenter_le : Subgroup.center Q ≤ K := by
    simpa [Q, K] using
      center_le_lastDerivedSubgroup_of_isAbFaithful (G := G) (m := m) hFaithful hm1
  have hKClosed : IsClosed ((K : Subgroup Q) : Set Q) := by
    simpa [K, lastDerivedSubgroup] using
      (show IsClosed ((topDerivedTop Q (m - 1) : Subgroup Q) : Set Q) by infer_instance)
  have hKle1 : K ≤ topDerivedTop Q 1 := by
    have hanti : Antitone (topDerivedTop (MaxSolvQuot G m)) := by
      apply antitone_nat_of_succ_le
      intro n
      dsimp [topDerivedTop, closedDerivedSeries, closedCommutator]
      exact
        Subgroup.topologicalClosure_minimal
          (s := ⁅topDerivedTop (MaxSolvQuot G m) n, topDerivedTop (MaxSolvQuot G m) n⁆)
          (t := topDerivedTop (MaxSolvQuot G m) n)
          (Subgroup.commutator_le_self (topDerivedTop (MaxSolvQuot G m) n))
          (by infer_instance)
    change topDerivedTop (MaxSolvQuot G m) (m - 1) ≤ topDerivedTop (MaxSolvQuot G m) 1
    exact hanti hmK
  have hstepK : closedDerivedSeries (G := Q) K 1 = ⊥ := by
    calc
      closedDerivedSeries (G := Q) K 1 = topDerivedTop Q m := by
        simpa [K, lastDerivedSubgroup, tsub_add_cancel_of_le hm1] using
          (topDerived_add (G := Q) (m := m - 1) (n := 1))
      _ = ⊥ := topDerivedTop_eq_bot_maxSolvQuot (G := G) m
  have hKder1bot : topDerivedTop K 1 = ⊥ := by
    exact
      topDerivedTop_one_eq_bot_of_closedDerivedSeries_eq_bot
        (Q := Q) (K := K) hKClosed hstepK
  have hinj : Function.Injective (TopologicalAbelianization.mk ↥K) := by
    exact injective_topologicalAbelianizationMk_of_topDerivedTop_one_eq_bot (G := K) hKder1bot
  have hfixed :
      HasNoNontrivialFixedPoints
        (quotientConjugationTopologicalAbelianizationMap (G := Q) (N := K)) := by
    exact
      noFixedPoints_of_torsionFree_on_openNormalSupergroups
        (G := Q) hKClosed (show K.Normal by infer_instance) hKle1
        (fun U hKU =>
          isMulTorsionFree_topologicalAbelianization_of_openNormalSupergroup_of_isAbTorsionFree
            (G := G) hTorsion hm U hKU)
  exact
    center_eq_bot_of_center_le_of_noNontrivialFixedPoints_of_inj_topologicalAbelianization
      (Q := Q) (K := K) hcenter_le hfixed hinj

/--
If the topological closure of a subgroup is open in a maximal finite-step solvable quotient, its
centralizer is contained in the last derived subgroup under the local torsion-free and faithful
abelianization hypotheses.
-/
theorem centralizer_subgroup_le_lastDerived_of_abTorsionFree_faithful
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hTorsion : IsAbTorsionFree G) (hFaithful : IsAbFaithful G)
    {m : ℕ} (hm : 1 ≤ m)
    (S : Subgroup (MaxSolvQuot G m))
    (hSOpen :
      IsOpen (((S.topologicalClosure : Subgroup (MaxSolvQuot G m)) :
        Set (MaxSolvQuot G m)))) :
    Subgroup.centralizer (S : Set (MaxSolvQuot G m))
      ≤ lastDerivedSubgroup (G := G) m := by
  by_cases hm1 : m = 1
  · subst hm1
    change Subgroup.centralizer (S : Set (MaxSolvQuot G 1)) ≤
      (⊤ : Subgroup (MaxSolvQuot G 1))
    exact le_top
  have hm2 : 2 ≤ m := Nat.succ_le_of_lt (lt_of_le_of_ne hm (Ne.symm hm1))
  let Q : Type u := MaxSolvQuot G m
  let : CompactSpace Q := by dsimp [Q, MaxSolvQuot]; infer_instance
  let : T2Space Q := by dsimp [Q, MaxSolvQuot]; infer_instance
  let : TotallyDisconnectedSpace Q := by
    dsimp [Q, MaxSolvQuot]
    exact ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (topDerivedTop G m)
      (show IsClosed ((topDerivedTop G m : Subgroup G) : Set G) by infer_instance)
  let K : Subgroup Q := lastDerivedSubgroup (G := G) m
  have hKClosed : IsClosed ((K : Subgroup Q) : Set Q) := by
    simpa [Q, K, lastDerivedSubgroup] using
      (show IsClosed ((topDerivedTop Q (m - 1) : Subgroup Q) : Set Q) by infer_instance)
  have hKNormal : K.Normal := by
    dsimp [Q, K, lastDerivedSubgroup]
    infer_instance
  exact
    centralizer_subgroup_le_of_open_topologicalClosure
      (Q := Q) (K := K) hKClosed hKNormal
      (hTF := by
        intro U hKU
        exact
          isMulTorsionFree_topologicalAbelianization_of_openNormalSupergroup_of_isAbTorsionFree
            (G := G) hTorsion hm2 U hKU)
      (hFaithful := by
        intro U hKU
        exact
          injective_quotientConjAbelianization_of_openNormalSupergroup_of_abFaithful
            (G := G) hFaithful hm2 U hKU)
      hSOpen

/-- Open subgroups of a maximal finite-step solvable quotient have centralizer contained in the
last derived subgroup under the local torsion-free and faithful abelianization hypotheses. -/
theorem
    centralizer_openSubgroup_le_lastDerived_of_abTorsionFree_faithful
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hTorsion : IsAbTorsionFree G) (hFaithful : IsAbFaithful G)
    {m : ℕ} (hm : 1 ≤ m)
    (H : OpenSubgroup (MaxSolvQuot G m)) :
    Subgroup.centralizer (H : Set (MaxSolvQuot G m))
      ≤ lastDerivedSubgroup (G := G) m := by
  by_cases hm1 : m = 1
  · subst hm1
    change Subgroup.centralizer (H : Set (MaxSolvQuot G 1)) ≤
      (⊤ : Subgroup (MaxSolvQuot G 1))
    exact le_top
  have hm2 : 2 ≤ m := Nat.succ_le_of_lt (lt_of_le_of_ne hm (Ne.symm hm1))
  let Q : Type u := MaxSolvQuot G m
  let : CompactSpace Q := by dsimp [Q, MaxSolvQuot]; infer_instance
  let : T2Space Q := by dsimp [Q, MaxSolvQuot]; infer_instance
  let : TotallyDisconnectedSpace Q := by
    dsimp [Q, MaxSolvQuot]
    exact ProCGroups.totallyDisconnectedSpace_quotient_closedNormal
      (topDerivedTop G m)
      (show IsClosed ((topDerivedTop G m : Subgroup G) : Set G) by infer_instance)
  let K : Subgroup Q := lastDerivedSubgroup (G := G) m
  have hKClosed : IsClosed ((K : Subgroup Q) : Set Q) := by
    simpa [Q, K, lastDerivedSubgroup] using
      (show IsClosed ((topDerivedTop Q (m - 1) : Subgroup Q) : Set Q) by infer_instance)
  have hKNormal : K.Normal := by
    dsimp [Q, K, lastDerivedSubgroup]
    infer_instance
  exact
    centralizer_openSubgroup_le_of_torsionFree_and_inj_action_on_openNormalSupergroups
      (Q := Q) (K := K) hKClosed hKNormal
      (hTF := by
        intro U hKU
        exact
          isMulTorsionFree_topologicalAbelianization_of_openNormalSupergroup_of_isAbTorsionFree
            (G := G) hTorsion hm2 U hKU)
      (hFaithful := by
        intro U hKU
        exact
          injective_quotientConjAbelianization_of_openNormalSupergroup_of_abFaithful
            (G := G) hFaithful hm2 U hKU)
      H

/--
Maximal finite-step solvable quotients are slim modulo their last derived subgroup under the
local torsion-free and faithful abelianization hypotheses.
-/
theorem isSlimModulo_lastDerivedSubgroup_maxSolvQuot_of_isAbTorsionFree_of_isAbFaithful
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hTorsion : IsAbTorsionFree G) (hFaithful : IsAbFaithful G)
    {m : ℕ} (hm : 1 ≤ m) :
    IsSlimModulo (MaxSolvQuot G m)
      (lastDerivedSubgroup (G := G) m) := by
  intro H
  exact
    centralizer_openSubgroup_le_lastDerived_of_abTorsionFree_faithful
      (G := G) hTorsion hFaithful hm H

/--
The center of a maximal finite-step solvable quotient is contained in the last derived subgroup
under the local torsion-free and faithful abelianization hypotheses.
-/
theorem center_le_lastDerivedSubgroup_of_isAbTorsionFree_of_isAbFaithful
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hTorsion : IsAbTorsionFree G) (hFaithful : IsAbFaithful G)
    {m : ℕ} (hm : 1 ≤ m) :
    Subgroup.center (MaxSolvQuot G m) ≤
      lastDerivedSubgroup (G := G) m := by
  exact
    center_le_of_isSlimModulo
      (G := MaxSolvQuot G m)
      (K := lastDerivedSubgroup (G := G) m)
      (isSlimModulo_lastDerivedSubgroup_maxSolvQuot_of_isAbTorsionFree_of_isAbFaithful
        (G := G) hTorsion hFaithful hm)

/--
If the last derived subgroup already vanishes, then the maximal finite-step solvable quotient is
slim under the local torsion-free and faithful abelianization hypotheses.
-/
theorem isSlim_maxSolvQuot_of_isAbTorsionFree_of_isAbFaithful_of_lastDerivedSubgroup_eq_bot
    {G : Type u} [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    (hTorsion : IsAbTorsionFree G) (hFaithful : IsAbFaithful G)
    {m : ℕ} (hm : 1 ≤ m)
    (hder : lastDerivedSubgroup (G := G) m = ⊥) :
    IsSlim (MaxSolvQuot G m) := by
  exact
    isSlim_of_isSlimModulo_bot
      (G := MaxSolvQuot G m)
      (by
        simpa [hder] using
          (isSlimModulo_lastDerivedSubgroup_maxSolvQuot_of_isAbTorsionFree_of_isAbFaithful
            (G := G) hTorsion hFaithful hm))

end ProCGroups.FiniteStepSolvableQuotients
