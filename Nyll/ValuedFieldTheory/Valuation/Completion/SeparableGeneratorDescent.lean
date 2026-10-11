/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableRootApproximation
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.SeparableClosure
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Lifts

/-!
# Descending separable generators to a dense subfield

A nearby root supplied by polynomial approximation generates the same
extension as the original separable element. Comparing the degrees also
shows that the new generator is separable over the dense subfield, with
the original extension degree.
-/

namespace ValuationTheory.Completion

open Polynomial IntermediateField

/-- A finite separable simple extension of a complete nonarchimedean field
has a generator separable over any dense subfield, with the same degree. -/
theorem exists_isSeparable_adjoin_eq_of_denseRange
    {K A : Type*} [Field K] [NontriviallyNormedField A]
    [CompleteSpace A] [IsUltrametricDist A] [Algebra K A]
    (hd : DenseRange (algebraMap K A)) (α : AlgebraicClosure A)
    (hα : IsSeparable A α) :
    ∃ β : AlgebraicClosure A, IsSeparable K β ∧ A⟮β⟯ = A⟮α⟯ ∧
      (minpoly K β).natDegree = (minpoly A α).natDegree := by
  obtain ⟨g, β, hg, hdegree, hroot, hαβ⟩ :=
    exists_monic_root_with_adjoin_containment hd α hα
  have hrootA : aeval β (g.map (algebraMap K A)) = 0 := by
    rw [Polynomial.aeval_map_algebraMap]
    exact hroot
  have hβK : IsIntegral K β := ⟨g, hg, hroot⟩
  have hβA : IsIntegral A β :=
    ⟨g.map (algebraMap K A), hg.map (algebraMap K A), hrootA⟩
  have : FiniteDimensional A A⟮β⟯ := IntermediateField.adjoin.finiteDimensional hβA
  have hβdegree : (minpoly A β).natDegree ≤ (minpoly A α).natDegree := by
    calc
      (minpoly A β).natDegree ≤ (g.map (algebraMap K A)).natDegree :=
        Polynomial.natDegree_le_of_dvd (minpoly.dvd A β hrootA)
          (hg.map (algebraMap K A)).ne_zero
      _ = g.natDegree := Polynomial.natDegree_map (algebraMap K A)
      _ = (minpoly A α).natDegree := hdegree
  have heq : A⟮α⟯ = A⟮β⟯ := by
    apply IntermediateField.eq_of_le_of_finrank_le
      (IntermediateField.adjoin_simple_le_iff.mpr hαβ)
    rw [IntermediateField.adjoin.finrank hβA, IntermediateField.adjoin.finrank hα.isIntegral]
    exact hβdegree
  have hβAsep : IsSeparable A β := by
    apply mem_separableClosure_iff.mp
    have hle : A⟮α⟯ ≤ separableClosure A (AlgebraicClosure A) :=
      IntermediateField.adjoin_simple_le_iff.mpr (mem_separableClosure_iff.mpr hα)
    apply hle
    rw [heq]
    exact IntermediateField.mem_adjoin_simple_self A β
  have hdegreeA : (minpoly A β).natDegree = (minpoly A α).natDegree := by
    rw [← IntermediateField.adjoin.finrank hβA,
      ← IntermediateField.adjoin.finrank hα.isIntegral, heq]
  have hgmap : g.map (algebraMap K A) = minpoly A β := by
    apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hβA) (hg.map (algebraMap K A)) (minpoly.dvd A β hrootA)
    rw [Polynomial.natDegree_map, hdegree, hdegreeA]
  have hgsep : g.Separable := by
    apply (Polynomial.separable_map (algebraMap K A)).mp
    rw [hgmap]
    exact hβAsep
  have hminmap : (minpoly K β).map (algebraMap K A) = minpoly A β :=
    minpoly.map_algebraMap hβK ((Polynomial.mem_lifts (minpoly A β)).mpr ⟨g, hgmap⟩)
  refine ⟨β, hgsep.of_dvd (minpoly.dvd K β hroot), heq.symm, ?_⟩
  have hminDegree := congrArg Polynomial.natDegree hminmap
  rw [Polynomial.natDegree_map] at hminDegree
  exact hminDegree.trans hdegreeA

end ValuationTheory.Completion
