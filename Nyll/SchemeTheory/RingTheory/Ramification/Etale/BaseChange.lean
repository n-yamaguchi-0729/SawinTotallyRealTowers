/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.Smooth.Flat

/-!
# Ramification index under an étale tensor base change

This file records the ramification-index comparison needed after choosing an étale factor as
in Stacks Project, Tag 00UJ.  The contraction equality supplied by that construction is the only
prime-comparison input: residue-field bijectivity, height-one hypotheses, and normalization are
not needed for this step.

The nondefault algebra structure on the right tensor factor, its scalar tower, and the transferred
étale structure are kept local to the proof so that importing this leaf does not add global
instances.
-/

noncomputable section

namespace EtaleFundamentalGroups

/-- Ramification indices are unchanged after an étale tensor base change.

Here `Q` is a prime of `C ⊗[R] B` lying over `q` through the right tensor-factor map.  This is
the precise contraction equality produced by the chosen-prime part of Tag 00UJ.
-/
theorem ramificationIdx_tensorProduct_eq_of_etale
    {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] [Algebra.Etale R C]
    (q : Ideal B) [q.IsPrime]
    (Q : Ideal (TensorProduct R C B)) [Q.IsPrime]
    (hQ : Q.comap Algebra.TensorProduct.includeRight.toRingHom = q) :
    Q.ramificationIdx C = q.ramificationIdx R := by
  let T := TensorProduct R C B
  let : Algebra B T := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R B T := Algebra.TensorProduct.right_isScalarTower
  let commB : AlgEquiv B (TensorProduct R B C) T :=
    { toRingEquiv := (Algebra.TensorProduct.comm R B C).toRingEquiv
      commutes' := by
        intro b
        exact (Algebra.TensorProduct.right_algebraMap_apply b).symm }
  let : Algebra.Etale B T := Algebra.Etale.of_equiv commB
  let : Q.LiesOver q :=
    { over := by
        simpa [Ideal.under_def,
          Algebra.TensorProduct.algebraMap_eq_includeRight] using hQ.symm }
  let P := Q.under C
  let p := P.under R
  let Rp := Localization.AtPrime p
  let Cp := Localization.AtPrime P
  let TQ := Localization.AtPrime Q
  have h_unramified : Algebra.IsUnramifiedAt R P := by
    exact (Algebra.formallyUnramified_iff_forall.mp
      (inferInstance : Algebra.FormallyUnramified R C))
        (PrimeSpectrum.mk P inferInstance)
  let : Algebra.IsUnramifiedAt R P := h_unramified
  let : Algebra Rp Cp := Localization.AtPrime.algebraOfLiesOver p P
  let : Algebra Cp TQ := Localization.AtPrime.algebraOfLiesOver P Q
  have hp_map : p.map (algebraMap R Cp) = IsLocalRing.maximalIdeal Cp :=
    ((Algebra.isUnramifiedAt_iff_map_eq R p P).mp h_unramified).2
  have hP_map : P.map (algebraMap C Cp) = IsLocalRing.maximalIdeal Cp :=
    Localization.AtPrime.map_eq_maximalIdeal
  have h_same_ideal :
      p.map (algebraMap R TQ) = P.map (algebraMap C TQ) := by
    calc
      p.map (algebraMap R TQ) =
          (p.map (algebraMap R Cp)).map (algebraMap Cp TQ) := by
        symm
        rw [Ideal.map_map, IsScalarTower.algebraMap_eq R Cp TQ]
      _ = (P.map (algebraMap C Cp)).map (algebraMap Cp TQ) := by
        rw [hp_map, hP_map]
      _ = P.map (algebraMap C TQ) := by
        rw [Ideal.map_map, IsScalarTower.algebraMap_eq C Cp TQ]
  have hQ_over_p : Q.LiesOver p := by
    exact Ideal.LiesOver.trans Q P p
  let : Q.LiesOver p := hQ_over_p
  have h_over_base : Q.ramificationIdx C = Q.ramificationIdx R := by
    rw [Ideal.ramificationIdx_eq P Q, Ideal.ramificationIdx_eq p Q,
      h_same_ideal]
  calc
    Q.ramificationIdx C = Q.ramificationIdx R := h_over_base
    _ = q.ramificationIdx R * Q.ramificationIdx B :=
      Ideal.ramificationIdx_tower q Q
    _ = q.ramificationIdx R := by
      rw [Ideal.ramificationIdx_eq_one Q B, mul_one]

end EtaleFundamentalGroups

end
