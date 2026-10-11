/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianSeparableClosureTopology
import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableClosureAutTopology
import Mathlib.FieldTheory.AbsoluteGaloisGroup

/-!
# The absolute Galois group of a Henselian DVF and its completion

The tensor comparison gives the isomorphism on separable closures. The
purely inseparable comparison with algebraic closures connects it to the
actual `Field.absoluteGaloisGroup`, with its Krull topology, in every
characteristic. The chosen separable-closure embedding records the choice.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField.HenselianDVF

variable {K : Type*} [Field K] (base : HenselianDVF K)

/-- Completion identifies the actual absolute Galois groups as topological
groups. The only choice is an embedding of the two separable closures,
which can always be supplied by `IsSepClosed.lift`. -/
def completionAbsoluteGaloisEquiv
    (i : SeparableClosure K →ₐ[K] SeparableClosure base.valuation.Completion) :
    Field.absoluteGaloisGroup K ≃ₜ* Field.absoluteGaloisGroup base.valuation.Completion := by
  let C : Type _ := base.valuation.Completion
  letI : Field C := inferInstance
  letI : Field (SeparableClosure C) := inferInstance
  letI : Algebra C (SeparableClosure C) := inferInstance
  let source : Field.absoluteGaloisGroup K ≃ₜ*
      (SeparableClosure K ≃ₐ[K] SeparableClosure K) :=
    Completion.separableClosureAutContinuousEquiv K
  let comparison : (SeparableClosure K ≃ₐ[K] SeparableClosure K) ≃ₜ*
      (SeparableClosure C ≃ₐ[C] SeparableClosure C) :=
    base.separableClosureAutContinuousEquiv
      (S := SeparableClosure K) (E := SeparableClosure base.valuation.Completion) i
  let target : Field.absoluteGaloisGroup C ≃ₜ*
      (SeparableClosure C ≃ₐ[C] SeparableClosure C) :=
    Completion.separableClosureAutContinuousEquiv base.valuation.Completion
  exact (source.trans comparison).trans target.symm

/-- The completed absolute Galois action agrees through the chosen
embedding with restriction of the original action to the separable closure. -/
@[simp] theorem completionAbsoluteGaloisEquiv_apply
    (i : SeparableClosure K →ₐ[K] SeparableClosure base.valuation.Completion)
    (σ : Field.absoluteGaloisGroup K) (s : SeparableClosure K) :
    AlgEquiv.toAlgHom (base.completionAbsoluteGaloisEquiv i σ)
      (i s : AlgebraicClosure base.valuation.Completion) =
      (i (Completion.separableClosureAutEquiv K σ s) :
        AlgebraicClosure base.valuation.Completion) := by
  let r := Completion.separableClosureAutContinuousEquiv base.valuation.Completion
  change r.symm (base.separableClosureAutContinuousEquiv i
    (Completion.separableClosureAutContinuousEquiv K σ))
      (i s : AlgebraicClosure base.valuation.Completion) = _
  rw [← Completion.separableClosureAutContinuousEquiv_apply, r.apply_symm_apply]
  exact congrArg (fun x : SeparableClosure base.valuation.Completion =>
    (x : AlgebraicClosure base.valuation.Completion))
      (base.separableClosureAutContinuousEquiv_apply i
        (Completion.separableClosureAutContinuousEquiv K σ) s)

end ValuationTheory.DiscreteValuationField.HenselianDVF
