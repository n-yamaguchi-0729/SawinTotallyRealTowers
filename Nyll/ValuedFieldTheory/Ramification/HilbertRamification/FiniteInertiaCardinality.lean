/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.SeparableDegree

/-!
# Finite inertia cardinality with inseparable residue degree

The residue extension need not be separable. Its automorphism group has order
its separable degree. Cancelling this factor from the actual decomposition
identity gives `|I| = e * f_insep`, which is the cardinal input for Stacks 0BUA.
-/

noncomputable section

namespace HilbertRamification.Dedekind

/-- Normality identifies field automorphisms with all field embeddings. -/
theorem card_aut_eq_finSepDegree_of_normal
    (k l : Type*) [Field k] [Field l] [Algebra k l] [Normal k l] :
    Nat.card (l ≃ₐ[k] l) = Field.finSepDegree k l := by
  calc
    Nat.card (l ≃ₐ[k] l) = Nat.card (l →ₐ[k] l) :=
      Nat.card_congr (Algebra.IsAlgebraic.algEquivEquivAlgHom k l)
    _ = Field.finSepDegree k l :=
      (Field.finSepDegree_eq_of_adjoin_splits k l l (IntermediateField.adjoin_univ k l)
        (fun x _ => ⟨Algebra.IsIntegral.isIntegral x,
          Normal.splits (inferInstance : Normal k l) x⟩)).symm

attribute [local instance] Ideal.Quotient.field

/-- The residue quotient of decomposition has the separable residue degree,
without a separability hypothesis on the residue extension. -/
theorem decompositionQuotientInertia_card_eq_finSepDegree
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsMaximal] (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    Nat.card (decompositionGroup Q G ⧸
      (inertiaGroup Q G).subgroupOf (decompositionGroup Q G)) =
      Field.finSepDegree (A ⧸ p) (B ⧸ Q) := by
  have : Normal (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.normal (A := A) G p Q
  exact (Nat.card_congr
    (dedekindRamification_decompositionQuotientInertiaEquivResidueGalois p Q G).toEquiv).trans
      (card_aut_eq_finSepDegree_of_normal (A ⧸ p) (B ⧸ Q))

/-- The actual finite decomposition order factors through the separable
residue degree and the actual ideal inertia group. -/
theorem decomposition_card_eq_finSepDegree_mul_inertia_card
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : Ideal A) [p.IsMaximal] (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    Nat.card (decompositionGroup Q G) =
      Field.finSepDegree (A ⧸ p) (B ⧸ Q) * Nat.card (inertiaGroup Q G) := by
  rw [dedekindRamification_decomposition_card_eq_quotient_card_mul_inertia_card Q G,
    decompositionQuotientInertia_card_eq_finSepDegree p Q G]

/-- The original finite inertia cardinality, including the inseparable
residue factor. No perfectness or residue-separability premise is imposed. -/
theorem inertia_card_eq_ramificationIdx_mul_finInsepDegree
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsDedekindDomain A] [IsDedekindDomain B]
    [Module.Finite A B] [Module.IsTorsionFree A B]
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver p]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B]
    [IsGaloisGroup G A B] :
    Nat.card (inertiaGroup Q G) =
      Q.ramificationIdx A * Field.finInsepDegree (A ⧸ p) (B ⧸ Q) := by
  have : Normal (A ⧸ p) (B ⧸ Q) := Ideal.Quotient.normal (A := A) G p Q
  have hpos : 0 < Field.finSepDegree (A ⧸ p) (B ⧸ Q) := by
    rw [← card_aut_eq_finSepDegree_of_normal (A ⧸ p) (B ⧸ Q)]
    exact Nat.card_pos
  have h := (decomposition_card_eq_finSepDegree_mul_inertia_card p Q G).symm.trans
    (dedekindRamification_decomposition_card_eq_ramificationIdxIn_mul_inertiaDegIn
      p hp Q G)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p Q G,
    Ideal.inertiaDegIn_eq_inertiaDeg p Q G,
    Ideal.inertiaDeg_eq_of_isMaximal p Q,
    ← Field.finSepDegree_mul_finInsepDegree (A ⧸ p) (B ⧸ Q)] at h
  apply Nat.eq_of_mul_eq_mul_left hpos
  calc
    _ = Q.ramificationIdx A *
        (Field.finSepDegree (A ⧸ p) (B ⧸ Q) *
          Field.finInsepDegree (A ⧸ p) (B ⧸ Q)) := h
    _ = _ := by rw [mul_left_comm]

end HilbertRamification.Dedekind
