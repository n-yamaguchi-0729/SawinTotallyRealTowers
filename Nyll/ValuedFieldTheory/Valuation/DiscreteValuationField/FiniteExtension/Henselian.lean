/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteExtension.Localization
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.Henselian
import Nyll.ValuedFieldTheory.Valuation.Henselian.AlgebraicExtensionHenselian

/-!
# Actual Henselian discrete valuation extensions

The localized integral closure constructs a discrete extension valuation.
Henselianity follows from the simple-root condition on the base valuation
ring and uniqueness along algebraic field towers.
-/

namespace ValuationTheory.DiscreteValuationField

universe u v w x

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]

/-- Any discrete valuation extending a Henselian valuation across an
algebraic field extension has a Henselian valuation ring. -/
theorem HenselianDVF.henselianRing_of_hasExtension [Algebra.IsAlgebraic K L]
    (base : HenselianDVF.{u, v} K) (target : DVF.{w, x} L)
    [base.toDVF.valuation.HasExtension target.valuation] :
    HenselianRing target.valuationSubring target.maximalIdeal := by
  have : base.toDVF.valuation.valuationSubring.valuation.HasExtension
      target.valuation.valuationSubring.valuation := by
    apply _root_.Valuation.HasExtension.ofComapInteger
    ext a
    change target.valuation.valuationSubring.valuation (algebraMap K L a) ≤ 1 ↔
      base.toDVF.valuation.valuationSubring.valuation a ≤ 1
    rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff]
    exact _root_.Valuation.HasExtension.val_map_le_one_iff base.toDVF.valuation target.valuation a
  exact ValuationTheory.Henselian.henselianRing_of_algebraic_extension
    base.toDVF.valuation.valuationSubring target.valuation.valuationSubring

namespace FiniteExtensionLocalization

variable [FiniteDimensional K L] [Algebra.IsSeparable K L]

/-- A finite separable extension of a Henselian DVF has an actual Henselian
discrete valuation, obtained from its localized integral closure. -/
noncomputable def henselianDVF (base : HenselianDVF.{u, v} K) : HenselianDVF.{w, 0} L where
  toDVF := dvf base.toDVF
  instHenselian := by
    have : base.toDVF.valuation.HasExtension (dvf (L := L) base.toDVF).valuation :=
      dvf_hasExtension base.toDVF
    exact base.henselianRing_of_hasExtension (dvf base.toDVF)

/-- The constructed Henselian discrete valuation extends the base valuation. -/
theorem henselianDVF_hasExtension (base : HenselianDVF.{u, v} K) :
    base.toDVF.valuation.HasExtension (henselianDVF (L := L) base).toDVF.valuation :=
  dvf_hasExtension base.toDVF

end FiniteExtensionLocalization

end ValuationTheory.DiscreteValuationField
