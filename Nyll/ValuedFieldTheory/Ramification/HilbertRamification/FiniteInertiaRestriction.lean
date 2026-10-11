/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.BaseChange
import Mathlib.FieldTheory.Galois.Profinite
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.HenselianInertiaRestriction

/-!
# Restriction maps between finite inertia groups

Define finite inertia restriction and transition maps, compare them with
Galois restriction, and prove compatibility and surjectivity over a
Henselian base.
-/

namespace RamificationTheory.HilbertRamification.ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- Actual restriction of inertia to a finite Galois intermediate field. -/
noncomputable def finiteInertiaRestriction
    (A : _root_.ValuationSubring L) (E : FiniteGaloisIntermediateField K L) :
    inertiaGroup K A →*
      inertiaGroup K (A.comap E.toIntermediateField.val.toRingHom) :=
  _root_.HilbertRamification.ValuationSubring.galoisPullback_inertiaGroupMap
    (RingHom.id K) E.toIntermediateField.val.toRingHom
    (by
      apply RingHom.ext
      intro a
      exact E.toIntermediateField.val.commutes a) A

/-- Inertia restriction agrees with the standard Galois restriction homomorphism. -/
theorem finiteInertiaRestriction_coe
    (A : _root_.ValuationSubring L) (E : FiniteGaloisIntermediateField K L)
    (σ : inertiaGroup K A) :
    inertiaGroupToAut (K := K) (A.comap E.toIntermediateField.val.toRingHom)
        (finiteInertiaRestriction A E σ) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E
        (inertiaGroupToAut (K := K) A σ) := by
  have hsquare : E.toIntermediateField.val.toRingHom.comp (algebraMap K E) =
      (algebraMap K L).comp (RingHom.id K) := by
    apply RingHom.ext
    intro a
    exact E.toIntermediateField.val.commutes a
  apply AlgEquiv.ext
  intro x
  apply E.toIntermediateField.val.injective
  calc
    _ = inertiaGroupToAut (K := K) A σ (E.toIntermediateField.val x) :=
      _root_.HilbertRamification.galoisPullback_galoisPullback_commutes
        (RingHom.id K) E.toIntermediateField.val.toRingHom hsquare
        (inertiaGroupToAut (K := K) A σ) x
    _ = _ :=
      (AlgEquiv.restrictNormal_commutes (inertiaGroupToAut (K := K) A σ) E x).symm


/-- Inertia restriction along an inclusion of finite Galois fields. -/
noncomputable def finiteInertiaTransition
    (A : _root_.ValuationSubring L)
    (E F : FiniteGaloisIntermediateField K L) (hEF : E ≤ F) :
    inertiaGroup K (A.comap F.toIntermediateField.val.toRingHom) →*
      inertiaGroup K (A.comap E.toIntermediateField.val.toRingHom) :=
  _root_.HilbertRamification.ValuationSubring.galoisPullback_inertiaGroupMap
    (RingHom.id K) (IntermediateField.inclusion hEF).toRingHom
    (by
      apply RingHom.ext
      intro a
      exact (IntermediateField.inclusion hEF).commutes a)
    (A.comap F.toIntermediateField.val.toRingHom)

/-- Actual finite inertia restriction commutes with transition to a lower field. -/
theorem finiteInertiaTransition_comp
    (A : _root_.ValuationSubring L)
    (E F : FiniteGaloisIntermediateField K L) (hEF : E ≤ F)
    (σ : inertiaGroup K A) :
    finiteInertiaTransition A E F hEF (finiteInertiaRestriction A F σ) =
      finiteInertiaRestriction A E σ := by
  let i : E →+* F := (IntermediateField.inclusion hEF).toRingHom
  let B : _root_.ValuationSubring F := A.comap F.toIntermediateField.val.toRingHom
  have hsquare : i.comp (algebraMap K E) =
      (algebraMap K F).comp (RingHom.id K) := by
    apply RingHom.ext
    intro a
    exact (IntermediateField.inclusion hEF).commutes a
  apply Subtype.ext
  apply Subtype.ext
  apply AlgEquiv.ext
  intro x
  apply E.toIntermediateField.val.injective
  calc
    _ = F.toIntermediateField.val
        (inertiaGroupToAut (K := K) B (finiteInertiaRestriction A F σ) (i x)) :=
      congrArg F.toIntermediateField.val
        (_root_.HilbertRamification.galoisPullback_galoisPullback_commutes
          (RingHom.id K) i hsquare
          (inertiaGroupToAut (K := K) B (finiteInertiaRestriction A F σ)) x)
    _ = inertiaGroupToAut (K := K) A σ (E.toIntermediateField.val x) := by
      rw [finiteInertiaRestriction_coe]
      exact AlgEquiv.restrictNormal_commutes (inertiaGroupToAut (K := K) A σ) F (i x)
    _ = _ := by
      have hcoe := congrArg (fun g : E ≃ₐ[K] E => E.toIntermediateField.val (g x))
        (finiteInertiaRestriction_coe A E σ)
      exact (AlgEquiv.restrictNormal_commutes
        (inertiaGroupToAut (K := K) A σ) E x).symm.trans hcoe.symm

/-- The finite inertia transition is onto over a Henselian base. -/
theorem finiteInertiaTransition_surjective_of_henselianRing [IsGalois K L]
    (V : _root_.ValuationSubring K)
    [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (A : _root_.ValuationSubring L) [V.valuation.HasExtension A.valuation]
    (E F : FiniteGaloisIntermediateField K L) (hEF : E ≤ F) :
    Function.Surjective (finiteInertiaTransition A E F hEF) := by
  intro t
  obtain ⟨σ, hσ⟩ :=
    galoisPullback_inertiaGroupMap_surjective_of_henselianRing V A E.toIntermediateField t
  exact ⟨finiteInertiaRestriction A F σ,
    (finiteInertiaTransition_comp A E F hEF σ).trans hσ⟩

end RamificationTheory.HilbertRamification.ValuationSubring
