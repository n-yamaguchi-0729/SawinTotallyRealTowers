/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Constructions
import Mathlib.Topology.Instances.ZMod
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Nyll.ProCGroups.FreeProC.Basic

/-!
# Pro C Groups / Free pro-C / Abelianization

This module identifies the topological abelianization of a free pro-\(C\)
group through its universal property and finite abelian targets.
-/

open scoped Topology

namespace ProCGroups.FreeProC

universe u v

/--
A finite cyclic coordinate on the topological abelianization of a finite-rank free
pro-\(\Sigma\) group, sending one chosen basis element to the standard generator.
-/
theorem exists_freeAbelianizationCyclicCoordinate
    {sigma : Set ℕ}
    {F : Type u} [TopologicalSpace F] [Group F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {r L : ℕ} (hLpos : 0 < L)
    (hLsigma : ProCGroups.FiniteGroupClass.IsSigmaNumber sigma L)
    (X : Fin r → F)
    (hFree :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := (ProCGroups.FiniteGroupClass.sigmaGroup sigma)) (Fin r) F X)
    (i : Fin r) :
    ∃ χ : TopologicalAbelianization F →ₜ* Multiplicative (ZMod L),
      χ (ProCGroups.Abelian.TopologicalAbelianization.mk F (X i)) =
        Multiplicative.ofAdd (1 : ZMod L) := by
  classical
  let C : ProCGroups.FiniteGroupClass.{u} := ProCGroups.FiniteGroupClass.sigmaGroup sigma
  let : NeZero L := ⟨Nat.ne_of_gt hLpos⟩
  let T : Type u := ULift.{u} (Multiplicative (ZMod L))
  let φ : Fin r → T :=
    fun j => if j = i then ULift.up (Multiplicative.ofAdd (1 : ZMod L)) else 1
  have hφ : FamilyConvergesToOneAlongOpenSubgroups (G := T) φ :=
    FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain φ
  have htarget : ProCGroups.ProC.HasOpenNormalBasisInClass C T := by
    exact
      ProCGroups.ProC.HasOpenNormalBasisInClass.of_finite_discrete
        (C := C) (G := T)
        (ProCGroups.FiniteGroupClass.sigmaGroup_quotientClosed sigma)
        (ProCGroups.FiniteGroupClass.sigmaGroup_cyclicZMod (sigma := sigma) hLpos hLsigma)
  rcases
      hFree.existsUnique_liftHom_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass
        C
        (ProCGroups.FiniteGroupClass.sigmaGroup_isomClosed sigma)
        (ProCGroups.FiniteGroupClass.sigmaGroup_subgroupClosed sigma)
        htarget φ hφ with
    ⟨χF, hχF, _⟩
  let down : T →ₜ* Multiplicative (ZMod L) :=
    { toMonoidHom := (MulEquiv.ulift : T ≃* Multiplicative (ZMod L)).toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }
  refine ⟨down.comp (ProCGroups.Abelian.TopologicalAbelianization.lift χF), ?_⟩
  change down (ProCGroups.Abelian.TopologicalAbelianization.lift χF
    (ProCGroups.Abelian.TopologicalAbelianization.mk F (X i))) =
      Multiplicative.ofAdd (1 : ZMod L)
  rw [ProCGroups.Abelian.TopologicalAbelianization.lift_apply_mk, hχF]
  change (MulEquiv.ulift : T ≃* Multiplicative (ZMod L)) (φ i) =
    Multiplicative.ofAdd (1 : ZMod L)
  simp only [↓reduceIte, φ]
  rfl

end ProCGroups.FreeProC
