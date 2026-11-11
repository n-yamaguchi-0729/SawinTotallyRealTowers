/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SawinTotallyRealTowers.RealProTwoFrattiniField
public import Nyll.SawinTotallyRealTowers.FiveQuadraticDegree
public import Nyll.SawinTotallyRealTowers.MaximalRealProPGroup
public import Nyll.ProCGroups.ProP.ProfiniteFrattini
public import Nyll.ProCGroups.ProP.FrattiniQuotient
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Galois.Infinite
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Nyll.SawinTotallyRealTowers.MaximalRealProPOutside
public import Nyll.SawinTotallyRealTowers.SixPrimeSupport
public import Nyll.SawinTotallyRealTowers.SixPrimeQuadraticCompositum
public import Nyll.ProCGroups.ProP.FrattiniPowers
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.FieldTheory.Galois.Profinite
public import Mathlib.Topology.Algebra.Group.ClosedSubgroup

/-!
# The actual finite Frattini quotient of the initial real tower

The proved Frattini fixed-field comparison identifies the canonical
power--commutator quotient with the Galois group of the five quadratic
layers. Its cardinality is therefore thirty-two. No finite-generation,
quotient-finiteness, or rank hypothesis enters the construction.
-/

@[expose] public section

namespace ClassFieldTower.Sawin

open ClassFieldTower.ProP

attribute [local instance] closedPowerCommutator_normal

/-- The canonical power--commutator quotient acts as the full Galois group
of the actual five-generator multiquadratic field. -/
noncomputable def maximalRealProTwo_powerCommutatorQuotientEquiv :
    powerCommutatorQuotient 2
      (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
        maximalRealProPOutside 2 sawinRationalPrimeSupport) ≃*
      (sawinQuadraticCompositum ≃ₐ[ℚ] sawinQuadraticCompositum) := by
  let M : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    maximalRealProPOutside 2 sawinRationalPrimeSupport
  let : IsGalois ℚ M := maximalRealProPOutside_isGalois 2 sawinRationalPrimeSupport
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : ClosedSubgroup (M ≃ₐ[ℚ] M) :=
    ⟨closedPowerCommutator 2 (M ≃ₐ[ℚ] M),
      isClosed_closedPowerCommutator 2 (M ≃ₐ[ℚ] M)⟩
  letI : N.toSubgroup.Normal := closedPowerCommutator_normal 2 (M ≃ₐ[ℚ] M)
  let L : IntermediateField ℚ M := IntermediateField.fixedField N.toSubgroup
  have hFrattini : profiniteFrattini (M ≃ₐ[ℚ] M) =
      closedPowerCommutator 2 (M ≃ₐ[ℚ] M) :=
    profiniteFrattini_eq_closedPowerCommutator
      (maximalRealProPOutside_galoisGroup_hasPGroupOpenNormalBasis
        2 sawinRationalPrimeSupport)
  have hField : IntermediateField.lift L =
      sawinQuadraticCompositum.toIntermediateField := by
    change IntermediateField.lift (IntermediateField.fixedField
      (closedPowerCommutator 2 (M ≃ₐ[ℚ] M))) =
        sawinQuadraticCompositum.toIntermediateField
    rw [← hFrattini]
    exact maximalRealProTwo_frattini_fixedField
  let eField : L ≃ₐ[ℚ] sawinQuadraticCompositum :=
    (IntermediateField.liftAlgEquiv L).trans (IntermediateField.equivOfEq hField)
  exact (InfiniteGalois.normalAutEquivQuotient (k := ℚ) (K := M) N).trans
    (AlgEquiv.autCongr eField)

/-- The canonical Frattini quotient of the constructed real pro-two group
has exactly thirty-two elements. -/
theorem maximalRealProTwo_powerCommutatorQuotient_card :
    Nat.card (powerCommutatorQuotient 2
      (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
        maximalRealProPOutside 2 sawinRationalPrimeSupport)) = 32 := by
  let : IsGalois ℚ sawinQuadraticCompositum.toIntermediateField :=
    sawinQuadraticCompositum.isGalois
  calc
    Nat.card (powerCommutatorQuotient 2
        (maximalRealProPOutside 2 sawinRationalPrimeSupport ≃ₐ[ℚ]
          maximalRealProPOutside 2 sawinRationalPrimeSupport)) =
        Nat.card (sawinQuadraticCompositum ≃ₐ[ℚ] sawinQuadraticCompositum) :=
      Nat.card_congr maximalRealProTwo_powerCommutatorQuotientEquiv.toEquiv
    _ = Module.finrank ℚ sawinQuadraticCompositum :=
      IsGalois.card_aut_eq_finrank ℚ sawinQuadraticCompositum
    _ = 32 := sawinQuadraticCompositum_finrank

end ClassFieldTower.Sawin
