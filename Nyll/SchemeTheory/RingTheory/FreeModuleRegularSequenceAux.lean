/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_RingTheory_Sequence_isWeaklyRegular_of_free_aux.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Earlier source notices recorded for the cited upstream material:
Copyright (c) 2025 Andrew Yang. All rights reserved.
Authors: Andrew Yang, Kevin Buzzard, Michael Rothgang
https://github.com/ImperialCollegeLondon/FLT/blob/a7dbce8494c29858093974a612a72b6454fc5cba/FLT/Patching/Utils/Depth.lean

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.QuotSMulTop
import Nyll.SchemeTheory.RingTheory.FreeModuleRegularScalar
import Mathlib.RingTheory.TensorProduct.Free

/-!
# Weak regularity on a nontrivial free module

Weak regularity of a sequence on a nontrivial free module is equivalent to weak
regularity on the ring. This auxiliary proof compares quotient modules and proceeds by
induction on the sequence length.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace RingTheory_Sequence_isWeaklyRegular_of_free_aux

open scoped Pointwise TensorProduct

theorem _root_.RingTheory.Sequence.isWeaklyRegular_of_free_aux.{u, v}
    {R : Type u} {M : Type max u v} [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Free R M] [Nontrivial M] {s : List R} :
    RingTheory.Sequence.IsWeaklyRegular M s ↔ RingTheory.Sequence.IsWeaklyRegular R s := by
  generalize hn : s.length = n
  induction n generalizing R M with
  | zero => simp_all
  | succ n IH =>
    cases s with
    | nil => simp at hn
    | cons x xs =>
    let e : QuotSMulTop x R ≃ₗ[R] R ⧸ Ideal.span {x} := Submodule.quotEquivOfEq _ _
      (by rw [← Submodule.ideal_span_singleton_smul]; simp)
    let e' := QuotSMulTop.equivQuotTensor x M
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff,
      e.isWeaklyRegular_congr, e'.isWeaklyRegular_congr,
      ← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R ⧸ Ideal.span {x}),
      ← RingTheory.Sequence.isWeaklyRegular_map_algebraMap_iff (R := R) (R ⧸ Ideal.span {x})]
    refine and_congr isSMulRegular_iff_of_free ?_
    cases subsingleton_or_nontrivial (R ⧸ Ideal.span {x})
    · have : Subsingleton ((R ⧸ Ideal.span {x}) ⊗[R] M) :=
        Module.subsingleton (R ⧸ Ideal.span {x}) _
      exact iff_of_true
        ((RingTheory.Sequence.isWeaklyRegular_iff_Fin ..).mpr fun _ _ _ _ ↦ Subsingleton.elim _ _)
        ((RingTheory.Sequence.isWeaklyRegular_iff_Fin ..).mpr fun _ _ _ _ ↦ Subsingleton.elim _ _)
    exact IH (by simp_all)
end RingTheory_Sequence_isWeaklyRegular_of_free_aux
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
