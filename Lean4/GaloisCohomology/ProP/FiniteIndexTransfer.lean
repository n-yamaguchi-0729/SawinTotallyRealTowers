/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Transfer
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.ContinuousMonoidHom

set_option autoImplicit false
/-!
# Continuous transfer from an open finite-index subgroup

The algebraic transfer is continuous: its transversal formula is a finite product,
and representatives are continuous functions of the discrete coset space. Normality
of the subgroup and discreteness of the target are not needed.
-/

open scoped Pointwise

namespace ClassFieldTower.Cohomology

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]

/-- Transfer from an open finite-index subgroup preserves continuity. -/
theorem continuous_transfer_of_openSubgroup
    (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (φ : H →* A) (hφ : Continuous φ) : Continuous (MonoidHom.transfer φ) := by
  classical
  let T : H.toSubgroup.LeftTransversal := default
  let := H.toSubgroup.fintypeQuotientOfFiniteIndex
  have hrep : Continuous (fun q : G ⧸ H.toSubgroup =>
      (T.2.leftQuotientEquiv q : G)) := continuous_of_discreteTopology
  have hdef : (MonoidHom.transfer φ : G → A) =
      fun g => Subgroup.leftTransversals.diff φ T (g • T) := by
    funext g
    exact MonoidHom.transfer_def φ T g
  rw [hdef]
  unfold Subgroup.leftTransversals.diff
  apply continuous_finsetProd
  intro q _hq
  apply hφ.comp
  apply Continuous.subtype_mk
  apply continuous_const.mul
  simp_rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, smul_eq_mul]
  exact continuous_id.mul (hrep.comp (continuous_inv.smul continuous_const))

/-- The algebraic transfer bundled as a continuous homomorphism. -/
noncomputable def openSubgroupTransfer
    (H : OpenSubgroup G) [H.toSubgroup.FiniteIndex]
    (φ : H →ₜ* A) : G →ₜ* A where
  __ := MonoidHom.transfer φ.toMonoidHom
  continuous_toFun := continuous_transfer_of_openSubgroup H φ.toMonoidHom φ.continuous_toFun

end ClassFieldTower.Cohomology
