/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianSeparableAutContinuous
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The Krull topology on separable closures across completion

Restriction is continuous. The source of restriction is the compact Galois
group of a separable closure, and the target is Hausdorff, so its inverse
is continuous as well. Both maps retain the chosen embedding.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField.HenselianDVF

variable {K : Type*} [Field K] (base : HenselianDVF K)
  {S E : Type*} [Field S] [Field E] [Algebra K S]
  [Algebra base.valuation.Completion E] [Algebra K E]
  [IsScalarTower K base.valuation.Completion E] [Algebra.IsSeparable K S]
  [IsSepClosed S] [Algebra.IsSeparable base.valuation.Completion E] [IsSepClosed E]

/-- Completing a Henselian DVF identifies the Krull topological groups of
the two separable closures, for the specified embedding between them. -/
def separableClosureAutContinuousEquiv (i : S →ₐ[K] E) :
    (S ≃ₐ[K] S) ≃ₜ* (E ≃ₐ[base.valuation.Completion] E) := by
  have : IsSepClosure base.valuation.Completion E :=
    ⟨‹IsSepClosed E›, ‹Algebra.IsSeparable base.valuation.Completion E›⟩
  have : IsGalois base.valuation.Completion E :=
    IsSepClosure.isGalois (k := base.valuation.Completion) (K := E)
  exact
    { base.separableClosedAutEquiv i with
      continuous_toFun :=
        (base.continuous_separableClosedAutEquiv_symm i).continuous_symm_of_equiv_compact_to_t2
          (f := (base.separableClosedAutEquiv i).symm.toEquiv)
      continuous_invFun := base.continuous_separableClosedAutEquiv_symm i }

/-- The continuous group isomorphism preserves the original action on
every element of the embedded separable closure. -/
@[simp] theorem separableClosureAutContinuousEquiv_apply
    (i : S →ₐ[K] E) (σ : S ≃ₐ[K] S) (s : S) :
    base.separableClosureAutContinuousEquiv i σ (i s) = i (σ s) :=
  base.separableClosedAutEquiv_apply i σ s

/-- The inverse homeomorphism is the same restriction of field actions. -/
@[simp] theorem separableClosureAutContinuousEquiv_symm_apply
    (i : S →ₐ[K] E) (σ : E ≃ₐ[base.valuation.Completion] E) (s : S) :
    i ((base.separableClosureAutContinuousEquiv i).symm σ s) = σ (i s) :=
  base.separableClosedAutEquiv_symm_apply i σ s

end ValuationTheory.DiscreteValuationField.HenselianDVF
