/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationNormQuotient
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

/-!
# Common data for the finite global norm-residue symbol

The quotient group structure and finite abstract base are chosen once, for
both general Galois reciprocity and its abelian specialization.
-/

@[expose] public section

universe u v

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

open ClassFormation KummerTheory



variable
    (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L]

/-- A reducible presentation of the compatible finite abstract field.
Its field projection is definitionally the concrete tower subgroup, so
dependent norm-quotient types do not require opaque unfolding. -/
noncomputable abbrev numberFieldTowerReciprocityFiniteAbstractField :
    FiniteAbstractField
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ) where
  field := numberFieldTowerBaseSubgroup K L
  finite := numberFieldTowerBaseSubgroup_absoluteQuotient_finite K L

end GlobalClassFieldTheory.Reciprocity
