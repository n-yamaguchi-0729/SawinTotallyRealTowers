/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationTransport
import Mathlib.RingTheory.Valuation.Discrete.RankOne
import Mathlib.Topology.Algebra.Valued.WithVal
import Mathlib.Topology.Algebra.Valued.NormedValued

/-!
# The normed model of a discrete valuation

Use the existing `WithVal` field with the rank-one embedding of base `2`.
The resulting norm has exactly the original valuation ring, transported by
`WithVal.equiv`. The normed structures below are local to this file.
-/

noncomputable section

namespace ValuationTheory.DiscreteValuationField.DVF

universe u v

variable {K : Type u} [Field K] (base : DVF.{u, v} K)

local instance :
    (Valued.v : _root_.Valuation (WithVal base.valuation) base.ValueGroup).IsRankOneDiscrete :=
  Valuation.isRankOneDiscrete_comap_ringEquiv base.valuation (WithVal.equiv base.valuation)

local instance :
    (Valued.v : _root_.Valuation (WithVal base.valuation) base.ValueGroup).RankOne :=
  _root_.Valuation.IsRankOneDiscrete.rankOne
    (Valued.v : _root_.Valuation (WithVal base.valuation) base.ValueGroup)
    (e := 2) (by norm_num)

local instance : NontriviallyNormedField (WithVal base.valuation) :=
  Valued.toNontriviallyNormedField (WithVal base.valuation) base.ValueGroup

private theorem normedWithVal_mem_valuationSubring_iff (x : WithVal base.valuation) :
    x ∈ (NormedField.valuation (K := WithVal base.valuation)).valuationSubring ↔
      WithVal.equiv base.valuation x ∈ base.valuation.valuationSubring := by
  rw [_root_.Valuation.mem_valuationSubring_iff,
    _root_.Valuation.mem_valuationSubring_iff, WithVal.val_apply_equiv,
    ← Valued.toNormedField.norm_le_one_iff]
  exact NNReal.coe_le_one.symm

/-- The normed `WithVal` model has the original valuation ring.

Its normed field structure is `Valued.toNontriviallyNormedField`, using
`Valuation.IsRankOneDiscrete.rankOne` with base `2`. -/
def normedWithValValuationSubringEquiv :
    (NormedField.valuation (K := WithVal base.valuation)).valuationSubring ≃+*
      base.valuationSubring where
  toFun x := ⟨WithVal.equiv base.valuation (x : WithVal base.valuation),
    (normedWithVal_mem_valuationSubring_iff base (x : WithVal base.valuation)).mp x.2⟩
  invFun y := ⟨(WithVal.equiv base.valuation).symm (y : K), by
    apply (normedWithVal_mem_valuationSubring_iff base
      ((WithVal.equiv base.valuation).symm (y : K))).mpr
    rw [RingEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv x := Subtype.ext ((WithVal.equiv base.valuation).symm_apply_apply
    (x : WithVal base.valuation))
  right_inv y := Subtype.ext ((WithVal.equiv base.valuation).apply_symm_apply (y : K))
  map_mul' x y := Subtype.ext ((WithVal.equiv base.valuation).map_mul
    (x : WithVal base.valuation) (y : WithVal base.valuation))
  map_add' x y := Subtype.ext ((WithVal.equiv base.valuation).map_add
    (x : WithVal base.valuation) (y : WithVal base.valuation))

/-- The valuation-ring equivalence is the restriction of `WithVal.equiv`. -/
@[simp] theorem normedWithValValuationSubringEquiv_apply
    (x : (NormedField.valuation (K := WithVal base.valuation)).valuationSubring) :
    (normedWithValValuationSubringEquiv base x : K) =
      WithVal.equiv base.valuation (x : WithVal base.valuation) := rfl

end ValuationTheory.DiscreteValuationField.DVF
