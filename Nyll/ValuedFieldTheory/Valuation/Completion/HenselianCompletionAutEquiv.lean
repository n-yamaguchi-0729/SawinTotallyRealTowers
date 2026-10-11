/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.DVFHomFunctor
import Nyll.ValuedFieldTheory.Valuation.Completion.HenselianCompletionHomEquiv
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Group.Units.Equiv

/-!
# Automorphisms and Henselian completion

The correspondence of homomorphisms respects composition. Passing to units
therefore gives a group isomorphism of automorphisms, whose action extends
the original action on the finite separable extension.
-/

noncomputable section


namespace ValuationTheory.DiscreteValuationField.HenselianDVF

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  (base : HenselianDVF K) (target : DVF L)
  [base.toDVF.valuation.HasExtension target.valuation]
  [FiniteDimensional K L] [Algebra.IsSeparable K L]

local instance : Algebra base.valuation.Completion target.valuation.Completion :=
  DVF.completionAlgebra base.toDVF target

/-- Completion identifies the endomorphism monoids of a finite separable
extension of a Henselian DVF and its actual valuation completion. -/
def completionEndEquiv :
    (L →ₐ[K] L) ≃*
      @AlgHom base.valuation.Completion target.valuation.Completion
        target.valuation.Completion _ _ _
        (DVF.completionAlgebra base.toDVF target)
        (DVF.completionAlgebra base.toDVF target) where
  toEquiv := completionAlgHomEquiv base target target
  map_mul' f g :=
    DVF.extendCompletionAlgHom_comp base.toDVF target target target g f

/-- The endomorphism correspondence extends the original map on field elements. -/
@[simp] theorem completionEndEquiv_coe (f : L →ₐ[K] L) (x : L) :
    completionEndEquiv base target f (x : target.valuation.Completion) =
      (f x : target.valuation.Completion) :=
  DVF.extendCompletionAlgHom_coe base.toDVF target target f x

/-- Completion identifies the automorphism groups by transporting units of
the actual endomorphism monoids. -/
def completionAutEquiv :
    (L ≃ₐ[K] L) ≃*
      @AlgEquiv base.valuation.Completion target.valuation.Completion
        target.valuation.Completion _ _ _
        (DVF.completionAlgebra base.toDVF target)
        (DVF.completionAlgebra base.toDVF target) :=
  (AlgEquiv.algHomUnitsEquiv K L).symm.trans
    ((Units.mapEquiv (completionEndEquiv base target)).trans
      (AlgEquiv.algHomUnitsEquiv base.valuation.Completion target.valuation.Completion))

/-- The completed automorphism agrees with the original automorphism on
the embedded finite extension. -/
@[simp] theorem completionAutEquiv_coe (e : L ≃ₐ[K] L) (x : L) :
    completionAutEquiv base target e (x : target.valuation.Completion) =
      (e x : target.valuation.Completion) := by
  change completionEndEquiv base target e.toAlgHom
    (x : target.valuation.Completion) = (e x : target.valuation.Completion)
  exact completionEndEquiv_coe base target e.toAlgHom x

end ValuationTheory.DiscreteValuationField.HenselianDVF
