/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FiniteGeneration.CharacteristicChainsAndIndices

/-!
# Reidemeister Schreier / Profinite / Open Subgroups / Finite Permutation Targets

This module packages the finite permutation image of the coset action of an
open subgroup, proves continuity of the action homomorphism, and transfers
finite-group-class membership to the image.
-/

open Set
open scoped Topology

namespace ReidemeisterSchreier
namespace Profinite

universe u v

section FinitePermutationTargets

open ProCGroups.ProC

/-- The actual permutation image of the finite coset action, before any universe lift. -/
abbrev openSubgroupIndexActionImage
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n) : Type :=
  (ProCGroups.FiniteGeneration.openSubgroupIndexContinuousHom
      (G := G) (H : Subgroup G) H.isOpen'
      (Subgroup.quotient_finite_of_isOpen (H : Subgroup G) H.isOpen') hn).range

/-- The actual finite permutation image belongs to the class across universes. -/
theorem openSubgroupIndexContinuousHom_range_mem_class
    {C : ProCGroups.FiniteGroupClass.{u}}
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hQuot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C G)
    (H : OpenSubgroup G) {n : ℕ}
    (hn : Nat.card (G ⧸ (H : Subgroup G)) = n) :
    C.MemAcrossUniverses (openSubgroupIndexActionImage (G := G) H hn) := by
  let φ : G →ₜ* Equiv.Perm (Fin n) :=
    ProCGroups.FiniteGeneration.openSubgroupIndexContinuousHom (G := G) (H : Subgroup G)
      H.isOpen' (Subgroup.quotient_finite_of_isOpen (H : Subgroup G) H.isOpen') hn
  let U : OpenNormalSubgroup G :=
    { toOpenSubgroup :=
        { toSubgroup := φ.toMonoidHom.ker
          isOpen' := by
            have h1open :
                IsOpen ({1} : Set (Equiv.Perm (Fin n))) := isOpen_discrete _
            change IsOpen (φ ⁻¹' ({1} : Set (Equiv.Perm (Fin n))))
            exact h1open.preimage φ.continuous_toFun }
      isNormal' := inferInstance }
  have hQuotU : C (G ⧸ (U : Subgroup G)) :=
    HasOpenNormalBasisInClass.hasAllOpenNormalQuotientsInClass_of_basis_of_quotientClosed
      hIso hQuot hG U
  exact
    (C.memAcrossUniverses_iff_of_mulEquiv
      (QuotientGroup.quotientKerEquivRange φ.toMonoidHom)).1
      (C.memAcrossUniverses_of_mem hQuotU)

/-- Universe-lifted permutation image of the finite coset action attached to an open subgroup. -/
abbrev openSubgroupIndexActionRange
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n) : Type u :=
  ULift.{u} (openSubgroupIndexActionImage (G := G) H hn)

/--
The finite permutation image is equipped with the discrete topology inherited from the finite
permutation target.
-/
instance openSubgroupIndexActionRange_topologicalSpace
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n) :
    TopologicalSpace (openSubgroupIndexActionRange (G := G) H hn) :=
  inferInstance

/-- The finite permutation image carries the discrete topology. -/
instance openSubgroupIndexActionRange_discreteTopology
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n) :
    DiscreteTopology (openSubgroupIndexActionRange (G := G) H hn) :=
  inferInstance

/-- The finite permutation image is a topological group with its discrete topology. -/
instance openSubgroupIndexActionRange_isTopologicalGroup
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n) :
    IsTopologicalGroup (openSubgroupIndexActionRange (G := G) H hn) :=
  inferInstance

/-- The permutation image of the open-subgroup coset action is finite. -/
instance openSubgroupIndexActionRange_finite
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n) :
    Finite (openSubgroupIndexActionRange (G := G) H hn) :=
  inferInstance

/-- The finite coset-action homomorphism lifted to its universe-lifted permutation image. -/
noncomputable def openSubgroupIndexActionRangeContinuousHom
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n) :
    G →ₜ* openSubgroupIndexActionRange (G := G) H hn := by
  let φ : G →ₜ* Equiv.Perm (Fin n) :=
    ProCGroups.FiniteGeneration.openSubgroupIndexContinuousHom (G := G) (H : Subgroup G)
      H.isOpen' (Subgroup.quotient_finite_of_isOpen (H : Subgroup G) H.isOpen') hn
  refine
    { toMonoidHom :=
        { toFun := fun g => ⟨⟨φ g, ⟨g, rfl⟩⟩⟩
          map_one' := by
            apply ULift.ext
            apply Subtype.ext
            simp only [map_one, ContinuousMonoidHom.coe_toMonoidHom, ULift.one_down,
                OneMemClass.coe_one, φ]
          map_mul' := by
            intro g h
            apply ULift.ext
            apply Subtype.ext
            change φ (g * h) = φ g * φ h
            exact map_mul φ g h }
      continuous_toFun := ?_ }
  exact continuous_uliftUp.comp <|
    Continuous.subtype_mk φ.continuous_toFun _

/--
The lifted permutation image acts on the finite coset index set through its underlying
permutation.
-/
instance openSubgroupIndexActionRange_mulAction
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n) :
    MulAction (openSubgroupIndexActionRange (G := G) H hn) (Fin n) where
  smul g i := g.down.1 i
  one_smul i := by
    rfl
  mul_smul g h i := by
    rfl

/-- The lifted permutation image acts on a finite coset by applying the represented permutation. -/
@[simp] theorem openSubgroupIndexActionRange_smul_apply
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n)
    (g : openSubgroupIndexActionRange (G := G) H hn) (i : Fin n) :
    g • i = g.down.1 i :=
  rfl

/-- The inverse transported permutation action of the coset-permutation image on the quotient. -/
noncomputable def openSubgroupIndexActionRange_leftQuotient_smul
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n) :
    openSubgroupIndexActionRange (G := G) H hn →
      (G ⧸ (H : Subgroup G)) → (G ⧸ (H : Subgroup G)) :=
  fun g q =>
    let e := ProCGroups.FiniteGeneration.openSubgroupIndexEquiv
      (G := G) (H : Subgroup G)
      (Subgroup.quotient_finite_of_isOpen (H : Subgroup G) H.isOpen') hn
    e.symm (g.down.1 (e q))

/-- The finite permutation action evaluates on a coset by applying the represented group element. -/
@[simp 900] theorem openSubgroupIndexActionRange_leftQuotientMulAction_apply
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n)
    (g : openSubgroupIndexActionRange (G := G) H hn) (q : G ⧸ (H : Subgroup G)) :
    let e := ProCGroups.FiniteGeneration.openSubgroupIndexEquiv
      (G := G) (H : Subgroup G)
      (Subgroup.quotient_finite_of_isOpen (H : Subgroup G) H.isOpen') hn
    e (openSubgroupIndexActionRange_leftQuotient_smul (G := G) H hn g q) = g.down.1 (e q) := by
  simp only [openSubgroupIndexActionRange_leftQuotient_smul, ContinuousMonoidHom.coe_toMonoidHom,
  Equiv.apply_symm_apply]

/--
The permutation image acts on the quotient by the inverse transported permutation, so that
\(\rho(g)\) sends the basepoint coset to the coset of \(g\).
-/
noncomputable instance openSubgroupIndexActionRange_leftQuotientMulAction
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n) :
    MulAction (openSubgroupIndexActionRange (G := G) H hn) (G ⧸ (H : Subgroup G)) where
  smul := openSubgroupIndexActionRange_leftQuotient_smul (G := G) H hn
  one_smul q := by
    let e := ProCGroups.FiniteGeneration.openSubgroupIndexEquiv
      (G := G) (H : Subgroup G)
      (Subgroup.quotient_finite_of_isOpen (H : Subgroup G) H.isOpen') hn
    apply e.injective
    change e (openSubgroupIndexActionRange_leftQuotient_smul (G := G) H hn 1 q) = e q
    simp only [openSubgroupIndexActionRange_leftQuotient_smul, ContinuousMonoidHom.coe_toMonoidHom,
  ULift.one_down, OneMemClass.coe_one, Equiv.Perm.coe_one, id_eq, Equiv.symm_apply_apply]
  mul_smul g h q := by
    let e := ProCGroups.FiniteGeneration.openSubgroupIndexEquiv
      (G := G) (H : Subgroup G)
      (Subgroup.quotient_finite_of_isOpen (H : Subgroup G) H.isOpen') hn
    apply e.injective
    change
      e (openSubgroupIndexActionRange_leftQuotient_smul (G := G) H hn (g * h) q) =
        e (openSubgroupIndexActionRange_leftQuotient_smul (G := G) H hn g
          (openSubgroupIndexActionRange_leftQuotient_smul (G := G) H hn h q))
    rw [openSubgroupIndexActionRange_leftQuotientMulAction_apply (G := G) H hn (g * h) q]
    rw [openSubgroupIndexActionRange_leftQuotientMulAction_apply (G := G) H hn g]
    rw [openSubgroupIndexActionRange_leftQuotientMulAction_apply (G := G) H hn h q]
    rfl

/--
The induced action of the finite permutation image on the quotient by the open subgroup is
continuous.
-/
instance openSubgroupIndexActionRange_leftQuotientContinuousSMul
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n) :
    ContinuousSMul (openSubgroupIndexActionRange (G := G) H hn) (G ⧸ (H : Subgroup G)) := by
  exact ⟨continuous_of_discreteTopology⟩

/-- The lifted finite permutation action sends the basepoint coset to the expected coset. -/
@[simp 900] theorem openSubgroupIndexActionRangeContinuousHom_smul_basepoint
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n) (g : G) :
    openSubgroupIndexActionRangeContinuousHom (G := G) H hn g •
        (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G)) =
      QuotientGroup.mk (s := (H : Subgroup G)) g := by
  classical
  let e := ProCGroups.FiniteGeneration.openSubgroupIndexEquiv
    (G := G) (H : Subgroup G)
    (Subgroup.quotient_finite_of_isOpen (H : Subgroup G) H.isOpen') hn
  let φ : G →* Equiv.Perm (Fin n) :=
    ProCGroups.FiniteGeneration.openSubgroupIndexAction (G := G) (H : Subgroup G)
      (Subgroup.quotient_finite_of_isOpen (H : Subgroup G) H.isOpen') hn
  have hbase :
      g • (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G)) =
        QuotientGroup.mk (s := (H : Subgroup G)) g := by
    change QuotientGroup.mk (s := (H : Subgroup G)) (g * 1) =
        QuotientGroup.mk (s := (H : Subgroup G)) g
    simp only [mul_one]
  have haction :
      openSubgroupIndexActionRangeContinuousHom (G := G) H hn g •
          (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G)) =
        g • (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G)) := by
    have himage :
        e (openSubgroupIndexActionRangeContinuousHom (G := G) H hn g •
              (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G))) =
          e (g • (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G))) := by
      change
        e (openSubgroupIndexActionRange_leftQuotient_smul (G := G) H hn
              (openSubgroupIndexActionRangeContinuousHom (G := G) H hn g)
              (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G))) =
          e (g • (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G)))
      rw [openSubgroupIndexActionRange_leftQuotientMulAction_apply]
      change φ g (e (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G))) =
          e (g • (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G)))
      rw [show φ g = e.permCongr (MulAction.toPerm g) by
        rfl]
      rw [Equiv.permCongr_apply, e.symm_apply_apply]
      rfl
    exact e.injective himage
  exact haction.trans hbase

/--
Under the subgroup-membership condition, the lifted finite permutation action fixes the
basepoint coset as prescribed.
-/
@[simp] theorem openSubgroupIndexActionRangeContinuousHom_smul_basepoint_of_mem
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (H : OpenSubgroup G) {n : ℕ} (hn : Nat.card (G ⧸ (H : Subgroup G)) = n)
    {g : G} (hg : g ∈ (H : Subgroup G)) :
    openSubgroupIndexActionRangeContinuousHom (G := G) H hn g •
        (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G)) =
      QuotientGroup.mk (s := (H : Subgroup G)) (1 : G) := by
  rw [openSubgroupIndexActionRangeContinuousHom_smul_basepoint (G := G) H hn g]
  simpa [QuotientGroup.eq] using hg

/--
The universe-lifted finite permutation image of an open-subgroup action belongs to the ambient
finite-group class.
-/
theorem openSubgroupIndexActionRange_mem_class
    {C : ProCGroups.FiniteGroupClass.{u}}
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hQuot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C G)
    (H : OpenSubgroup G) {n : ℕ}
    (hn : Nat.card (G ⧸ (H : Subgroup G)) = n) :
    C (openSubgroupIndexActionRange (G := G) H hn) := by
  apply C.mem_of_memAcrossUniverses
  exact
    (C.memAcrossUniverses_ulift_iff
      (openSubgroupIndexActionImage (G := G) H hn)).2
      (openSubgroupIndexContinuousHom_range_mem_class
        (C := C) hIso hQuot hG H hn)

end FinitePermutationTargets


end Profinite
end ReidemeisterSchreier
