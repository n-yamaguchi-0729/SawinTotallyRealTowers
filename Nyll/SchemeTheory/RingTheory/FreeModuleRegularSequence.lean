/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Nyll.SchemeTheory.RingTheory.FreeModuleRegularSequenceAux

/-!
# Weak regular sequences on free modules

Weak regularity of a sequence on a nontrivial free module is equivalent to weak
regularity on the ring. The public statement uses the free-module comparison proved in
the auxiliary module.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace RingTheory_Sequence_isWeaklyRegular_of_free

open scoped Pointwise TensorProduct

theorem _root_.RingTheory.Sequence.isWeaklyRegular_of_free {R M : Type*}
    [CommRing R] [AddCommGroup M] [Module R M] [Module.Free R M]
    [Nontrivial M] {s : List R} :
    RingTheory.Sequence.IsWeaklyRegular M s ↔ RingTheory.Sequence.IsWeaklyRegular R s := by
  let b := Module.Free.chooseBasis R M
  have : Nontrivial R := Module.nontrivial R M
  rw [b.repr.isWeaklyRegular_congr, RingTheory.Sequence.isWeaklyRegular_of_free_aux]
end RingTheory_Sequence_isWeaklyRegular_of_free
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
