/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionUniqueness
import Nyll.ValuedFieldTheory.Valuation.Henselian.UniqueAlgebraicExtensions

/-!
# Henselianity of algebraic extension valuation rings

Chevalley's theorem supplies an extension over every further algebraic field.
Uniqueness over the original Henselian base makes this extension unique.
The valuation-ring criterion then supplies Henselianity upstairs.
-/

namespace ValuationTheory.Henselian

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
  (V : ValuationSubring K) [HenselianRing V (IsLocalRing.maximalIdeal V)]
  (W : ValuationSubring L) [V.valuation.HasExtension W.valuation]

include V in
/-- An algebraic extension of a Henselian valuation ring is Henselian,
without rank, discreteness, completeness, or separability assumptions. -/
theorem henselianRing_of_algebraic_extension :
    HenselianRing W (IsLocalRing.maximalIdeal W) := by
  have hUnique :
      AlgebraicNumberTheory.Valuations.HasUniqueAlgebraicValuationSubringExtensions W := by
    intro M _ _ _
    let : Algebra K M := ((algebraMap L M).comp (algebraMap K L)).toAlgebra
    let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq (fun x => rfl)
    have : Algebra.IsAlgebraic K M := Algebra.IsAlgebraic.trans K L M
    obtain ⟨B, _, _, _, hWB⟩ :=
      (open _root_.ValuationTheory.DiscreteValuationField.Valuation in
        exists_extension_valuationSubring_with_hasExtension (L := M) W.valuation)
    have : W.valuation.HasExtension B.valuation := hWB
    have : V.valuation.HasExtension B.valuation :=
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_trans
        V.valuation W.valuation B.valuation
    refine ⟨B, hWB, ?_⟩
    intro C hWC
    have : W.valuation.HasExtension C.valuation := hWC
    have : V.valuation.HasExtension C.valuation :=
      ValuationTheory.DiscreteValuationField.Valuation.hasExtension_trans
        V.valuation W.valuation C.valuation
    simpa only [ValuationSubring.valuationSubring_valuation] using
      valuationSubring_eq_of_henselianRing V C.valuation B.valuation
  exact _root_.DiscreteValuationField.henselianRing_of_monicResidualCoprimeFactorLifting
    (open _root_.AlgebraicNumberTheory.Valuations in
      monicResidualCoprimeFactorLifting_of_unique_algebraic_extensions W hUnique)

end ValuationTheory.Henselian
