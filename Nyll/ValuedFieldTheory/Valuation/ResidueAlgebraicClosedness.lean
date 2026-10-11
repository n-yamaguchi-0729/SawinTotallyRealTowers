/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Algebraic closedness of a valuation residue field

A valuation subring of an algebraically closed field has algebraically closed
residue field. Lift a monic residue polynomial, choose its root in the ambient
field, and use integral closedness to realize that same root in the valuation
ring before reducing it. No hypothesis on the valuation rank or residue
characteristic is needed.
-/

namespace ValuationSubring

universe u

/-- The residue field of any valuation subring of an algebraically closed
field is algebraically closed. -/
theorem isAlgClosed_residueField
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (A : ValuationSubring Ω) :
    IsAlgClosed (IsLocalRing.ResidueField A) := by
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  have hlifts : p ∈ Polynomial.lifts (IsLocalRing.residue A) :=
    Polynomial.mem_lifts_of_surjective IsLocalRing.residue_surjective p
  obtain ⟨q, hqmap, hqdegree, hqmonic⟩ :=
    Polynomial.lifts_and_degree_eq_and_monic hlifts hp
  have hqdegree_ne_zero : q.degree ≠ 0 := by
    rw [hqdegree]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hirr)
  have hinj : Function.Injective (algebraMap A Ω) := by
    intro a b hab
    exact Subtype.ext hab
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero_of_injective
    Ω hinj q hqdegree_ne_zero
  have hxintegral : IsIntegral A x := ⟨q, hqmonic, hx⟩
  obtain ⟨a, ha⟩ :=
    IsIntegrallyClosed.algebraMap_eq_of_integral (R := A) (K := Ω) hxintegral
  have hqa : q.eval a = 0 := by
    apply hinj
    rw [map_zero, ← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, ha]
    exact hx
  refine ⟨IsLocalRing.residue A a, ?_⟩
  rw [← hqmap, Polynomial.eval_map_apply, hqa, map_zero]

end ValuationSubring
