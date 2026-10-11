/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Tame inertia forces a separable residue extension

This file supplies the residue-field step in the SGA 1 form of Abhyankar's
lemma.  It works at an arbitrary nonzero maximal ideal of a finite Galois
extension of Dedekind domains; no completeness or Henselian hypothesis is
used.
-/

noncomputable section

namespace TameAbhyankar.SGA1

open Algebra Module
open HilbertRamification.Dedekind

attribute [local instance] Ideal.Quotient.field

/-- A finite algebra remains finite after passing to residue rings at a pair
of ideals with the upper ideal lying over the lower one. -/
theorem residueModule_finite_of_liesOver
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Finite R S]
    (p : Ideal R) (P : Ideal S) [P.LiesOver p] :
    Module.Finite (R ⧸ p) (S ⧸ P) := by
  let residueMap : S →ₛₗ[Ideal.Quotient.mk p] (S ⧸ P) :=
    { toFun := Ideal.Quotient.mk P
      map_add' := map_add (Ideal.Quotient.mk P)
      map_smul' := by
        intro r s
        rw [Algebra.smul_def, Algebra.smul_def]
        change Ideal.Quotient.mk P (algebraMap R S r * s) =
          algebraMap (R ⧸ p) (S ⧸ P) (Ideal.Quotient.mk p r) *
            Ideal.Quotient.mk P s
        rw [map_mul, Ideal.Quotient.algebraMap_mk_of_liesOver] }
  exact Module.Finite.of_surjective residueMap Ideal.Quotient.mk_surjective

variable {A B G : Type*}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsDedekindDomain A] [IsDedekindDomain B]
variable [Module.Finite A B] [IsTorsionFree A B]
variable [Group G] [Finite G] [MulSemiringAction G B]
variable [IsGaloisGroup G A B]

/-- For a finite Galois extension of Dedekind domains, the inertia-group
cardinality at a nonzero maximal ideal is the ramification index times the
inseparable degree of the residue-field extension.

This is the form of the inertia-cardinality formula that does not assume the
residue extension is separable. -/
theorem inertia_card_eq_ramificationIdx_mul_finInsepDegree
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p] :
    Nat.card (P.toAddSubgroup.inertia G) =
      p.ramificationIdx' P *
        Field.finInsepDegree (A ⧸ p) (B ⧸ P) := by
  let : Module.Finite (A ⧸ p) (B ⧸ P) :=
    residueModule_finite_of_liesOver p P
  let : Normal (A ⧸ p) (B ⧸ P) :=
    dedekindRamification_residueExtension_normal (A := A) (B := B) p P G
  have hquotient :
      Nat.card
          (decompositionGroup P G ⧸
            (inertiaGroup P G).subgroupOf (decompositionGroup P G)) =
        Field.finSepDegree (A ⧸ p) (B ⧸ P) := by
    calc
      Nat.card
          (decompositionGroup P G ⧸
            (inertiaGroup P G).subgroupOf (decompositionGroup P G)) =
          Nat.card ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)) :=
        Nat.card_congr
          (dedekindRamification_decompositionQuotientInertiaEquivResidueGalois
            (A := A) (B := B) p P G).toEquiv
      _ = Nat.card (Field.Emb (A ⧸ p) (B ⧸ P)) := by
        symm
        exact Nat.card_congr
          (Normal.algHomEquivAut (A ⧸ p) (AlgebraicClosure (B ⧸ P)) (B ⧸ P) :
            Field.Emb (A ⧸ p) (B ⧸ P) ≃
              ((B ⧸ P) ≃ₐ[A ⧸ p] (B ⧸ P)))
      _ = Field.finSepDegree (A ⧸ p) (B ⧸ P) := rfl
  have hdecompositionQuotient :=
    dedekindRamification_decomposition_card_eq_quotient_card_mul_inertia_card
      (B := B) P G
  rw [hquotient] at hdecompositionQuotient
  have hdecompositionRamification :=
    dedekindRamification_decomposition_card_eq_ramificationIdxIn_mul_inertiaDegIn
      (A := A) (B := B) p hp P G
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx p P G,
    ← Ideal.ramificationIdx'_eq_ramificationIdx p P hp,
    Ideal.inertiaDegIn_eq_inertiaDeg p P G,
    Ideal.inertiaDeg_eq_of_isMaximal p P] at hdecompositionRamification
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.pos_of_ne_zero (NeZero.ne (Field.finSepDegree (A ⧸ p) (B ⧸ P))))
  calc
    Field.finSepDegree (A ⧸ p) (B ⧸ P) *
          Nat.card (P.toAddSubgroup.inertia G) =
        Nat.card (decompositionGroup P G) :=
      hdecompositionQuotient.symm
    _ = p.ramificationIdx' P *
          Module.finrank (A ⧸ p) (B ⧸ P) :=
      hdecompositionRamification
    _ = p.ramificationIdx' P *
          (Field.finSepDegree (A ⧸ p) (B ⧸ P) *
            Field.finInsepDegree (A ⧸ p) (B ⧸ P)) := by
      rw [Field.finSepDegree_mul_finInsepDegree]
    _ = Field.finSepDegree (A ⧸ p) (B ⧸ P) *
          (p.ramificationIdx' P *
            Field.finInsepDegree (A ⧸ p) (B ⧸ P)) := by
      ac_rfl

/-- If the inertia-group cardinality is prime to the exponential
characteristic of the residue field, then the residue-field extension is
separable. -/
theorem residue_isSeparable_of_inertia_card_coprime_ringExpChar
    (p : Ideal A) [p.IsMaximal] (hp : p ≠ ⊥)
    (P : Ideal B) [P.IsMaximal] [P.LiesOver p]
    (hcop : Nat.Coprime (Nat.card (P.toAddSubgroup.inertia G))
      (ringExpChar (A ⧸ p))) :
    Algebra.IsSeparable (A ⧸ p) (B ⧸ P) := by
  let : Module.Finite (A ⧸ p) (B ⧸ P) :=
    residueModule_finite_of_liesOver p P
  rw [isSeparable_iff_finInsepDegree_eq_one]
  have hdvd : Field.finInsepDegree (A ⧸ p) (B ⧸ P) ∣
      Nat.card (P.toAddSubgroup.inertia G) := by
    refine ⟨p.ramificationIdx' P, ?_⟩
    rw [inertia_card_eq_ramificationIdx_mul_finInsepDegree
      (A := A) (B := B) (G := G) p hp P, mul_comm]
  have hcopInsep : Nat.Coprime
      (Field.finInsepDegree (A ⧸ p) (B ⧸ P))
      (ringExpChar (A ⧸ p)) :=
    hcop.of_dvd_left hdvd
  obtain ⟨n, hn⟩ := finInsepDegree_eq_pow
    (A ⧸ p) (B ⧸ P) (ringExpChar (A ⧸ p))
  obtain hcharPrime | hcharOne :=
    expChar_is_prime_or_one (A ⧸ p) (ringExpChar (A ⧸ p))
  · have hnzero : n = 0 := by
      by_contra hn0
      have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      have hcopPow : Nat.Coprime ((ringExpChar (A ⧸ p)) ^ n)
          (ringExpChar (A ⧸ p)) := by
        simpa [hn] using hcopInsep
      have hself : Nat.Coprime (ringExpChar (A ⧸ p))
          (ringExpChar (A ⧸ p)) :=
        (Nat.coprime_pow_left_iff hnpos _ _).mp hcopPow
      have hone : ringExpChar (A ⧸ p) = 1 := by
        simpa using hself
      exact hcharPrime.ne_one hone
    rw [hn, hnzero, pow_zero]
  · simpa [hcharOne] using hn

end TameAbhyankar.SGA1
