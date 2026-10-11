/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.Transfer
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.GroupTheory.Index

/-!
# Restricting transfer of a conjugation-invariant character

A normal subgroup acts trivially on its coset space. Each factor of the
transfer of an element of the subgroup is therefore a conjugate of that
element. Conjugation invariance of the character makes the product its
value raised to the subgroup index.
-/

open scoped Pointwise

namespace ClassFieldTower.Cohomology

variable {G A : Type*} [Group G] [CommGroup A]

/-- Transfer restricts to the index power of a conjugation-invariant
character on a normal finite-index subgroup. -/
theorem transfer_subtype_eq_pow_of_conjInvariant
    (H : Subgroup G) [H.Normal] [H.FiniteIndex] (φ : H →* A)
    (hinv : ∀ (g : G) (h : H), φ (MulAut.conjNormal g h) = φ h) (h : H) :
    MonoidHom.transfer φ (h : G) = φ h ^ H.index := by
  classical
  let T : H.LeftTransversal := default
  let := H.fintypeQuotientOfFiniteIndex
  have hsmul (q : G ⧸ H) : (h : G)⁻¹ • q = q := by
    refine Quotient.inductionOn' q ?_
    intro g
    change (((h : G)⁻¹ * g : G) : G ⧸ H) = (g : G ⧸ H)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      (QuotientGroup.eq_one_iff (h : G)).mpr h.property, inv_one, one_mul]
  rw [MonoidHom.transfer_def φ T]
  unfold Subgroup.leftTransversals.diff
  calc
    _ = ∏ q : G ⧸ H, φ h := by
      apply Finset.prod_congr rfl
      intro q hq
      trans φ (MulAut.conjNormal ((T.2.leftQuotientEquiv q : G)⁻¹) h)
      · apply congrArg φ
        apply Subtype.ext
        simp only [Subgroup.smul_apply_eq_smul_apply_inv_smul, hsmul, smul_eq_mul,
          MulAut.conjNormal_apply, inv_inv, mul_assoc]
      · exact hinv ((T.2.leftQuotientEquiv q : G)⁻¹) h
    _ = φ h ^ H.index := by
      simp only [Finset.prod_const, Finset.card_univ, Subgroup.index_eq_card,
        Nat.card_eq_fintype_card]

end ClassFieldTower.Cohomology
