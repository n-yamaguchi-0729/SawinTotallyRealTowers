/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Regular.SMul
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Tactic.Ext

/-!
# Regular scalar multiplication on a nontrivial free module

Scalar multiplication by a ring element is injective on a nontrivial free module exactly
when multiplication by that element is injective on the ring.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.Algebra.Proofs.isSMulRegular_iff_of_free

theorem _root_.isSMulRegular_iff_of_free {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Free R M] [Nontrivial M] {r : R} :
    IsSMulRegular M r ↔ IsSMulRegular R r := by
  let I := Module.Free.ChooseBasisIndex R M
  let b : Module.Basis I R M := Module.Free.chooseBasis R M
  constructor
  · intro H m n h
    have i : I := Nonempty.some inferInstance
    have := @H (m • b i) (n • b i) (by simp_all [← mul_smul])
    simpa using congr(b.repr $this i)
  · intro H m n h
    apply b.repr.injective
    ext i
    replace h := congr(b.repr $h i)
    simp only [map_smul] at h
    exact H h
end AlgebraicCurves.Foundations.Algebra.Proofs.isSMulRegular_iff_of_free
end ProofImplementation
