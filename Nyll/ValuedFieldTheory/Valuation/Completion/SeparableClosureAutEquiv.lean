/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Restriction from an algebraic closure to its separable closure

The algebraic closure is purely inseparable over the separable closure, so an
automorphism is uniquely determined by its restriction. Normality supplies
extensions of automorphisms, and restriction is continuous for the Krull topology.
-/

noncomputable section

namespace ValuationTheory.Completion

variable (K : Type*) [Field K]

/-- Restriction identifies the automorphism groups of the algebraic and
separable closures over an arbitrary field. -/
def separableClosureAutEquiv :
    Gal(AlgebraicClosure K/K) ≃* Gal(SeparableClosure K/K) :=
  MulEquiv.ofBijective (AlgEquiv.restrictNormalHom (SeparableClosure K))
    ⟨fun σ τ h ↦ by
      apply AlgEquiv.coe_toAlgHom_injective
      apply IsPurelyInseparable.injective_restrictDomain
        (SeparableClosure K) (AlgebraicClosure K) K (AlgebraicClosure K)
      apply AlgHom.ext
      intro s
      change σ (s : AlgebraicClosure K) = τ (s : AlgebraicClosure K)
      rw [← AlgEquiv.restrictNormalHom_apply
        (separableClosure K (AlgebraicClosure K)) σ s,
        ← AlgEquiv.restrictNormalHom_apply
          (separableClosure K (AlgebraicClosure K)) τ s, h],
      AlgEquiv.restrictNormalHom_surjective (F := K)
        (K₁ := SeparableClosure K) (E := AlgebraicClosure K)⟩

/-- Restriction preserves the action on every element of the separable closure. -/
theorem separableClosureAutEquiv_apply (σ : Gal(AlgebraicClosure K/K))
    (s : SeparableClosure K) :
    (separableClosureAutEquiv K σ s : AlgebraicClosure K) = σ (s : AlgebraicClosure K) :=
  AlgEquiv.restrictNormalHom_apply (separableClosure K (AlgebraicClosure K)) σ s

/-- Restriction to the separable closure is continuous for the Krull topologies. -/
theorem continuous_separableClosureAutEquiv : Continuous (separableClosureAutEquiv K) :=
  InfiniteGalois.restrictNormalHom_continuous (separableClosure K (AlgebraicClosure K))

end ValuationTheory.Completion
