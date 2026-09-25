/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.PClassGroup
import ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.SUnitPowerQuotient
import Mathlib.LinearAlgebra.Dimension.Finite

set_option autoImplicit false
/-!
# Finite Kummer and class-group parameters

The arithmetic obstruction space used in the Shafarevich relation-rank
argument has two finite pieces: an `S`-unit Kummer quotient and the elementary
ideal class quotient.  This file packages those pieces as one finite-dimensional
`ZMod p`-module without installing noncanonical global module instances.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Martinet
open KummerTheory

variable (F : Type*) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

private def pPositive : ℕ+ := (p.toPNat (Fact.out : p.Prime).pos)

/-- The Kummer and ideal-class parameter space attached to a finite set of
finite places. -/
noncomputable def kummerClassParameter
    (S : Finset (HeightOneSpectrum (𝓞 F))) : ModuleCat (ZMod p) := by
  let n : ℕ+ := pPositive p
  let R := RestrictedRadicalQuotient n
    (fullSUnitKummerSubgroup (K := F) n S)
  let C := PClassGroup F p
  let _ : Module (ZMod p) (Additive R) :=
    AddCommGroup.zmodModule (fun x => by
      change (Additive.toMul x) ^ p = 1
      exact restrictedRadicalQuotient_pow_eq_one n
        (fullSUnitKummerSubgroup (K := F) n S) (Additive.toMul x))
  let _ : Module (ZMod p) (Additive C) :=
    AddCommGroup.zmodModule (fun x => by
      change (Additive.toMul x) ^ p = 1
      exact pClassGroup_pow_eq_one F p (Additive.toMul x))
  exact ModuleCat.of (ZMod p) (Additive R × Additive C)

/-- The Kummer/class-group parameter is finite-dimensional over `ZMod p`. -/
theorem kummerClassParameter_finiteDimensional
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    FiniteDimensional (ZMod p) (kummerClassParameter F p S) := by
  let n : ℕ+ := pPositive p
  let R := RestrictedRadicalQuotient n
    (fullSUnitKummerSubgroup (K := F) n S)
  let C := PClassGroup F p
  let _ : Module (ZMod p) (Additive R) :=
    AddCommGroup.zmodModule (fun x => by
      change (Additive.toMul x) ^ p = 1
      exact restrictedRadicalQuotient_pow_eq_one n
        (fullSUnitKummerSubgroup (K := F) n S) (Additive.toMul x))
  let _ : Module (ZMod p) (Additive C) :=
    AddCommGroup.zmodModule (fun x => by
      change (Additive.toMul x) ^ p = 1
      exact pClassGroup_pow_eq_one F p (Additive.toMul x))
  change Module.Finite (ZMod p) (Additive R × Additive C)
  exact Module.Finite.of_finite

end ClassFieldTower.Martinet.Shafarevich
