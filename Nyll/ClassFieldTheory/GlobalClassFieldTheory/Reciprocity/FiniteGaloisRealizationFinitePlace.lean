/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Ideal

/-!
# Finite places in the compatible Galois realization

This module extends a chosen finite place of `L` to the common rational
separable closure and compares its decomposition data with the corresponding
places and completions in the original number-field tower.
-/



@[expose] public section

open scoped NumberField
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open AlgebraicNumberTheory
open AlgebraicNumberTheory.Valuations
open IsDedekindDomain
open LocalClassFieldTheory
open RamificationTheory

variable
    (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]

/-- Extend a specified finite place of the compatible top number
field to the common rational separable closure.

Its restriction to `L` is definitionally the supplied exact extension,
so the resulting decomposition-group restriction lands at the
specified place rather than at an unrelated conjugate. -/
noncomputable def
    numberFieldTowerFinitePlaceExtensionToSeparableClosure
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    let : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    let : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (SeparableClosure ℚ) := by
  intro sharedOwner1 sharedOwner2 sharedOwner3
  letI : IsScalarTower ℚ L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopScalarTower L
  letI : Algebra.IsAlgebraic L (SeparableClosure ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) L
  exact
    w.extendToAlgebraicallyClosed
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v)

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The compatible separable-closure extension restricts to the
specified finite-place extension on `L`. -/
@[simp]
theorem
    numberFieldTowerFinitePlaceExtensionToSeparableClosure_algebraMap
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L)
    (x : L) :
    let : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    let : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    let : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    (numberFieldTowerFinitePlaceExtensionToSeparableClosure
      K L v w).1
        (algebraMap L (SeparableClosure ℚ) x) =
      w.1 x := by
  intro sharedOwner1 sharedOwner2 sharedOwner3
  let : IsScalarTower ℚ L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureTopScalarTower L
  let : Algebra.IsAlgebraic L (SeparableClosure ℚ) :=
    Algebra.IsAlgebraic.tower_top (K := ℚ) L
  exact
    AbsoluteValueExtension.extendToAlgebraicallyClosed_algebraMap
      (NumberField.HeightOneSpectrum.adicAbv K v)
      (RayClass.adicAbv_isNontrivial v) w x

omit [FiniteDimensional K L] [IsGalois K L] in
/-- Restricting the compatible separable-closure absolute value along
the chosen top-field embedding recovers the supplied exact extension. -/
theorem
    numberFieldTowerFinitePlaceExtensionToSeparableClosure_restrict
    (v : HeightOneSpectrum (𝓞 K))
    (w : AbsoluteValueExtension
      (NumberField.HeightOneSpectrum.adicAbv K v) L) :
    let : Algebra K (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureBaseAlgebra K L
    let : Algebra L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureTopAlgebra L
    let : IsScalarTower K L (SeparableClosure ℚ) :=
      numberFieldTowerSeparableClosureScalarTower K L
    (numberFieldTowerFinitePlaceExtensionToSeparableClosure
        K L v w).1.comp
        (f := algebraMap L (SeparableClosure ℚ))
        (algebraMap L (SeparableClosure ℚ)).injective =
      w.1 := by
  intro sharedOwner1 sharedOwner2 sharedOwner3
  ext x
  exact
    numberFieldTowerFinitePlaceExtensionToSeparableClosure_algebraMap
      K L v w x

end Reciprocity
end GlobalClassFieldTheory
