/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.HenselianIdempotents
import Mathlib.RingTheory.Idempotents

/-!
# Lifting complete orthogonal families over a Henselian pair

The actual bijection on quotient idempotents of an integral algebra lifts
each member of a finite family. Uniqueness lifts orthogonality and the
equation that their sum is one. The algebra need not be finite or finite
type over the base.
-/

namespace Algebra

universe u v w

/-- A complete orthogonal family in the closed fiber of an integral algebra
over a Henselian pair lifts to an actual complete orthogonal family. -/
theorem exists_completeOrthogonalIdempotents_lift_of_isIntegral
    {R : Type u} {B : Type v} {ι : Type w}
    [CommRing R] [CommRing B] [Algebra R B] [Algebra.IsIntegral R B]
    [Fintype ι] (I : Ideal R) [HenselianRing R I]
    (e : ι → B ⧸ I.map (algebraMap R B)) (he : CompleteOrthogonalIdempotents e) :
    ∃ e' : ι → B, CompleteOrthogonalIdempotents e' ∧
      ∀ i, Ideal.Quotient.mk (I.map (algebraMap R B)) (e' i) = e i := by
  classical
  let q := Ideal.Quotient.mk (I.map (algebraMap R B))
  have hbij := bijective_idempotents_quotient_of_henselian (B := B) I
  have hrigid {a b : B} (ha : IsIdempotentElem a) (hb : IsIdempotentElem b)
      (hab : q a = q b) : a = b :=
    congrArg Subtype.val (hbij.1 (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext hab))
  have hlift (i : ι) : ∃ a : {a : B // IsIdempotentElem a}, q a.val = e i := by
    obtain ⟨a, ha⟩ := hbij.2 ⟨e i, he.idem i⟩
    exact ⟨a, congrArg Subtype.val ha⟩
  choose a ha using hlift
  let e' : ι → B := fun i => (a i).val
  have horth : OrthogonalIdempotents e' := by
    refine ⟨fun i => (a i).property, ?_⟩
    intro i j hij
    apply hrigid ((a i).property.mul (a j).property) IsIdempotentElem.zero
    change q ((a i).val * (a j).val) = q 0
    rw [map_mul, ha i, ha j, he.ortho hij, map_zero]
  have hcomplete : ∑ i, e' i = 1 := by
    apply hrigid horth.isIdempotentElem_sum IsIdempotentElem.one
    rw [map_sum, map_one]
    calc
      ∑ i, q (e' i) = ∑ i, e i := Finset.sum_congr rfl (fun i _ => ha i)
      _ = 1 := he.complete
  exact ⟨e', ⟨horth, hcomplete⟩, ha⟩

end Algebra
