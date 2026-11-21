/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.AbsoluteNormCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap

/-!
# Absolute norms in restricted-product coordinates

The absolute norm is owned by the standard adele-unit carrier. This boundary
expresses that same map in the coordinate presentation used by older consumers.
-/

@[expose] public section

open scoped NumberField RestrictedProduct NNReal
open NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K]

namespace FiniteIdeleGroup

/-- The absolute norm of finite coordinates, evaluated by their valuation vector. -/
def absoluteNorm : FiniteIdeleGroup K →* ℝ≥0ˣ :=
  (NumberField.divisorAbsoluteNorm (K := K)).comp valuationVector

@[simp]
theorem absoluteNorm_apply (a : FiniteIdeleGroup K) :
    absoluteNorm a = (valuationVector a).toAdd.prod fun v n =>
      NumberField.finitePrimeNorm v ^ n := rfl

end FiniteIdeleGroup

namespace IdeleGroup

/-- The absolute norm of an idele. -/
abbrev absoluteNorm : IdeleGroup K →* ℝ≥0ˣ :=
  NumberField.IdeleGroup.absoluteNorm (K := K)

@[simp]
theorem absoluteNorm_apply (a : IdeleGroup K) :
    absoluteNorm a = FiniteIdeleGroup.absoluteNorm (finiteCoordinates a) *
      (NumberField.InfiniteAdeleRing.absoluteNorm (infinitePart a))⁻¹ := rfl

/-- The ideles of absolute norm one. -/
abbrev normOneSubgroup : Subgroup (IdeleGroup K) :=
  NumberField.IdeleGroup.normOneSubgroup (K := K)

end IdeleGroup
