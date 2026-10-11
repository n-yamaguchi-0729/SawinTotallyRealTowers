/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.InducedFunctions
import Nyll.ProCGroups.FiniteGroups.StandardClasses

/-!
# Finite-class preservation for induced groups

The induced group is a subgroup of the finite product of copies of its
coefficient group. This gives Sigma membership and preserves finite
abelian exponent bounds without a choice of coset representatives.
-/

namespace ProCGroups.InducedFunctions

universe u

variable {G B : Type u} [Group G] [Finite G] [CommGroup B]
variable (H : Subgroup G) [MulDistribMulAction H B]

/-- Induction along a subgroup of a finite group preserves finite Sigma
groups. Its commutative group structure is inherited from the function group. -/
theorem induced_sigmaGroup (sigma : Set ℕ)
    (hB : FiniteGroupClass.sigmaGroup sigma B) :
    FiniteGroupClass.sigmaGroup sigma (InducedModule (B := B) H) := by
  let : Fintype G := Fintype.ofFinite G
  apply FiniteGroupClass.sigmaGroup_subgroupClosed sigma (inducedSubgroup (B := B) H)
  exact FiniteGroupClass.sigmaGroup_finiteProductClosed sigma (G := fun _ : G => B)
    (fun _ : G => hB)

/-- Induction along a subgroup of a finite group preserves finite abelian
groups of exponent dividing `n`, including elementary abelian prime groups. -/
theorem induced_abelianExponent (n : ℕ)
    (hB : FiniteGroupClass.abelianExponent n B) :
    FiniteGroupClass.abelianExponent n (InducedModule (B := B) H) := by
  let : Fintype G := Fintype.ofFinite G
  apply FiniteGroupClass.abelianExponent_subgroupClosed n (inducedSubgroup (B := B) H)
  exact FiniteGroupClass.abelianExponent_finiteProductClosed n (G := fun _ : G => B)
    (fun _ : G => hB)

end ProCGroups.InducedFunctions
