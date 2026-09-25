/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.GroupTheory.Sylow
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free

set_option autoImplicit false

/-!
# A central prime-degree step in a finite Galois p-extension

A nontrivial finite p-group has a central subgroup of order p. Its fixed
field gives a smaller Galois p-extension of the base, with a cyclic
prime-degree extension on top. This constructs the intermediate field
needed for induction without imposing any cohomological hypotheses.
-/

open Module

namespace IsGalois

/-- A nontrivial finite Galois p-extension has a smaller Galois p-subextension
with central, cyclic, prime-degree top extension. -/
theorem exists_intermediateField_prime_degree_of_isPGroup
    (K L : Type*) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (p : ℕ) [Fact p.Prime] [Nontrivial Gal(L/K)]
    (hP : IsPGroup p Gal(L/K)) :
    ∃ E : IntermediateField K L,
      IsGalois K E ∧ IsGalois E L ∧ IsPGroup p Gal(E/K) ∧
      IsCyclic Gal(L/E) ∧ finrank E L = p ∧
      finrank K E < finrank K L ∧
      E.fixingSubgroup ≤ Subgroup.center Gal(L/K) := by
  have hp : p.Prime := Fact.out
  have hCenter : IsPGroup p (Subgroup.center Gal(L/K)) :=
    hP.to_subgroup (Subgroup.center Gal(L/K))
  obtain ⟨n, hn, hCard⟩ :=
    hCenter.nontrivial_iff_card.mp hP.center_nontrivial
  have hLe : p ^ 1 ≤ Nat.card (Subgroup.center Gal(L/K)) := by
    rw [hCard]
    exact pow_le_pow_right₀ hp.one_lt.le hn
  obtain ⟨H, hH, hOrder⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card hp hP hLe
  have hOrderPrime : Nat.card H = p := by
    simpa only [pow_one] using hOrder
  have : H.Normal := ⟨by
    intro x hx g
    rw [Subgroup.mem_center_iff.mp (hH hx) g, mul_inv_cancel_right]
    exact hx⟩
  let E : IntermediateField K L := IntermediateField.fixedField H
  have hGaloisBase : IsGalois K E :=
    IsGalois.of_fixedField_normal_subgroup H
  have hGaloisTop : IsGalois E L := IsGalois.of_fixed_field L H
  have hGroupBase : IsPGroup p Gal(E/K) :=
    (hP.to_quotient H).of_equiv (IsGalois.normalAutEquivQuotient H)
  have hTopDegree : finrank E L = p :=
    (IntermediateField.finrank_fixedField_eq_card H).trans hOrderPrime
  have hCyclic : IsCyclic Gal(L/E) :=
    (IntermediateField.subgroupEquivAlgEquiv H).isCyclic.mp
      (isCyclic_of_prime_card hOrderPrime)
  refine ⟨E, hGaloisBase, hGaloisTop, hGroupBase, hCyclic, hTopDegree, ?_, ?_⟩
  · have hTower : finrank K E * p = finrank K L := by
      rw [← hTopDegree]
      exact finrank_mul_finrank K E L
    rw [← hTower]
    exact lt_mul_of_one_lt_right finrank_pos hp.one_lt
  · change (IntermediateField.fixedField H).fixingSubgroup ≤ Subgroup.center Gal(L/K)
    rw [IntermediateField.fixingSubgroup_fixedField H]
    exact hH

end IsGalois
