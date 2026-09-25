/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.QuadraticClosure
import SawinTotallyRealTowers.QuadraticSupportedGenerator
import SawinTotallyRealTowers.FiniteRealPExtension
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.Algebra.Rat

set_option autoImplicit false

/-!
# Identifying quadratic subfields from their generators

A root of the same quadratic equation generates the same subfield of the
fixed algebraic closure. This identifies arbitrary quadratic layers with
the concrete constructors and makes squarefree radicands unique.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTower.Sawin

/-- The quadratic subfield is independent of the choice of square root. -/
theorem quadraticClosure_eq_adjoin_of_sq
    (d : ℚ) (hd : ¬ IsSquare d) (β : AlgebraicClosure ℚ)
    (hβ : β ^ 2 = algebraMap ℚ (AlgebraicClosure ℚ) d) :
    (quadraticClosure d hd).toIntermediateField =
      IntermediateField.adjoin ℚ ({β} : Set (AlgebraicClosure ℚ)) := by
  rw [quadraticClosure_toIntermediateField]
  have hEq : quadraticClosureRoot d = β ∨ quadraticClosureRoot d = -β :=
    sq_eq_sq_iff_eq_or_eq_neg.mp ((quadraticClosureRoot_sq d).trans hβ.symm)
  rcases hEq with hPos | hNeg
  · exact congrArg (fun x : AlgebraicClosure ℚ ↦ IntermediateField.adjoin ℚ {x}) hPos
  · apply le_antisymm
    · apply IntermediateField.adjoin_simple_le_iff.mpr
      rw [hNeg]
      exact IntermediateField.neg_mem _ (IntermediateField.mem_adjoin_simple_self ℚ β)
    · apply IntermediateField.adjoin_simple_le_iff.mpr
      have hβNeg : β = -quadraticClosureRoot d := by rw [hNeg, neg_neg]
      rw [hβNeg]
      exact IntermediateField.neg_mem _
        (IntermediateField.mem_adjoin_simple_self ℚ (quadraticClosureRoot d))

/-- An internal square-root generator identifies an arbitrary finite
Galois intermediate field with the concrete quadratic subfield. -/
theorem eq_quadraticClosure_of_generator
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (d : ℚ) (hd : ¬ IsSquare d) (β : E)
    (hβ : β ^ 2 = algebraMap ℚ E d)
    (hGenerate : IntermediateField.adjoin ℚ ({β} : Set E) = ⊤) :
    E = quadraticClosure d hd := by
  have hAmbient : (β : AlgebraicClosure ℚ) ^ 2 =
      algebraMap ℚ (AlgebraicClosure ℚ) d := by
    exact (map_pow E.toIntermediateField.val β 2).symm.trans
      ((congrArg E.toIntermediateField.val hβ).trans
        (RingHom.map_rat_algebraMap E.toIntermediateField.val.toRingHom d))
  have hField : E.toIntermediateField =
      IntermediateField.adjoin ℚ ({(β : AlgebraicClosure ℚ)} : Set (AlgebraicClosure ℚ)) := by
    calc
      E.toIntermediateField = IntermediateField.lift
          (⊤ : IntermediateField ℚ E.toIntermediateField) :=
        (IntermediateField.lift_top ℚ E.toIntermediateField).symm
      _ = IntermediateField.lift (IntermediateField.adjoin ℚ ({β} : Set E)) :=
        congrArg (fun L : IntermediateField ℚ E ↦ IntermediateField.lift L) hGenerate.symm
      _ = IntermediateField.adjoin ℚ {(β : AlgebraicClosure ℚ)} :=
        IntermediateField.lift_adjoin_simple ℚ E.toIntermediateField β
  apply FiniteGaloisIntermediateField.val_injective
  exact hField.trans (quadraticClosure_eq_adjoin_of_sq d hd β hAmbient).symm

/-- Every admissible quadratic layer has a positive squarefree supported
radicand and equals the actual quadratic subfield constructed from it. -/
theorem exists_supported_radicand_of_admissible_quadratic
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))
    (hDegree : Module.finrank ℚ E = 2)
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (hE : IsAdmissibleFiniteLayer 2 T E)
    (hTwo : (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨2, Nat.prime_two⟩ : Nat.Primes) ∉ T) :
    ∃ d : ℤ, ∃ hd : ¬ IsSquare (d : ℚ),
      0 < d ∧ Squarefree d.natAbs ∧ d % 4 = 1 ∧
        (∀ q : Nat.Primes, (q : ℤ) ∣ d →
          (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm q ∈ T) ∧
        E = quadraticClosure (d : ℚ) hd := by
  let : NumberField E := NumberField.of_module_finite ℚ E
  let : Algebra.IsQuadraticExtension ℚ E := { finrank_eq_two' := hDegree }
  let : IsTotallyReal E :=
    (isUnramifiedAtInfinitePlaces_rat_iff_isTotallyReal E).mp hE.2.2
  obtain ⟨d, β, hdPos, hdSquarefree, hMod, hSquare, hGenerate, hd, hSupport⟩ :=
    exists_positive_squarefree_supported_generator E T hE.2.1 hTwo
  exact ⟨d, hd, hdPos, hdSquarefree, hMod, hSupport,
    eq_quadraticClosure_of_generator E (d : ℚ) hd β hSquare hGenerate⟩

end ClassFieldTower.Sawin
