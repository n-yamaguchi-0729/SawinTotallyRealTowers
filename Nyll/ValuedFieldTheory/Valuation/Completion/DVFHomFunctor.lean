/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.DVFHomExtension
import Nyll.ValuedFieldTheory.Valuation.Completion.DVFHomExt

/-!
# Functoriality of homomorphisms on valuation completions

The extension formula on original field elements and extensionality over
the base completion imply preservation of identities and composition.
-/

noncomputable section


namespace ValuationTheory.DiscreteValuationField.DVF

variable {K L M N : Type*} [Field K] [Field L] [Field M] [Field N]
  [Algebra K L] [Algebra K M] [Algebra K N]
  (base : DVF K) (targetL : DVF L) (targetM : DVF M) (targetN : DVF N)
  [hL : base.valuation.HasExtension targetL.valuation]
  [hM : base.valuation.HasExtension targetM.valuation]
  [hN : base.valuation.HasExtension targetN.valuation]
  [HenselianRing base.valuationSubring base.maximalIdeal]

local instance : Algebra base.valuation.Completion targetL.valuation.Completion :=
  completionAlgebra base targetL

/-- Extending the identity on a finite separable extension gives the identity
on its actual valuation completion. -/
theorem extendCompletionAlgHom_id [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    extendCompletionAlgHom base targetL targetL (AlgHom.id K L) =
      AlgHom.id base.valuation.Completion targetL.valuation.Completion := by
  apply completionAlgHom_ext base targetL
  intro x
  simp only [extendCompletionAlgHom_coe, AlgHom.id_apply]

/-- Extending a composite is composition of the extended homomorphisms.
Only the two source extensions must be finite and separable. -/
theorem extendCompletionAlgHom_comp
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [FiniteDimensional K M] [Algebra.IsSeparable K M]
    (f : L →ₐ[K] M) (g : M →ₐ[K] N) :
    extendCompletionAlgHom base targetL targetN (g.comp f) =
      (extendCompletionAlgHom base targetM targetN g).comp
        (extendCompletionAlgHom base targetL targetM f) := by
  apply completionAlgHom_ext base targetL
  intro x
  simp only [extendCompletionAlgHom_coe, AlgHom.comp_apply]

end ValuationTheory.DiscreteValuationField.DVF
