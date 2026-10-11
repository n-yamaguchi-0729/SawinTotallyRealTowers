/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitPadicPow
import Nyll.ValuedFieldTheory.LocalField.Analytic.PrincipalUnitPadicContinuity
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicLinearOfContinuous
import Mathlib.Topology.Algebra.Constructions
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismEquiv
import Nyll.ValuedFieldTheory.Valuation.DiscreteValuationField.ValuationPreservingContinuous

/-!
# Automorphisms commute with p-adic powers of principal units

The field automorphism restricts continuously to valuation-ring units and
principal units. The density theorem for continuous additive maps then
supplies compatibility with the actual p-adic scalars.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u

variable {K : Type u} [Field K]

open CompleteDVF.higherPrincipalUnitGroup

/-- Restrict a continuous field automorphism to any principal-unit level.
This argument needs only the ambient topology and preservation of the ring. -/
private theorem continuous_restrictedAutomorphism [TopologicalSpace K]
    (F : ValuationTheory.DiscreteValuationField.CompleteDVF K)
    (f : K ≃+* K)
    (hmem : ∀ z : K, z ∈ F.valuation.valuationSubring ↔ f z ∈ F.valuation.valuationSubring)
    (hf : Continuous f) (n : ℕ) : Continuous (equivOfPreserves F f hmem n) := by
  have hr : Continuous (valuationSubringRingEquivOfPreserves F f hmem) :=
    continuous_induced_rng.2 (hf.comp continuous_subtype_val)
  apply continuous_induced_rng.2
  change Continuous fun z : CompleteDVF.higherPrincipalUnitGroup F n =>
    Units.map (valuationSubringRingEquivOfPreserves F f hmem).toMonoidHom
      (z : F.valuationSubringˣ)
  exact (Units.continuous_map hr).comp continuous_subtype_val

/-- A valuation-preserving automorphism commutes with the actual p-adic powers. -/
theorem principalUnitPadicPowOfMixedChar_equivOfPreserves
    (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
    [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
    (f : K ≃+* K) (hval : ∀ x : K, v (f x) = v x)
    (a : ℤ_[p]) (x : CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1) :
    equivOfPreserves (completeDVFOfWithZeroValuation v) f
        (fun z => by change v z ≤ 1 ↔ v (f z) ≤ 1; rw [hval z]) 1
        (principalUnitPadicPowOfMixedChar v p a x) =
      principalUnitPadicPowOfMixedChar v p a
        (equivOfPreserves (completeDVFOfWithZeroValuation v) f
          (fun z => by change v z ≤ 1 ↔ v (f z) ≤ 1; rw [hval z]) 1 x) := by
  let : Valued K (WithZero (Multiplicative ℤ)) := Valued.mk' v
  let F := completeDVFOfWithZeroValuation v
  let e := equivOfPreserves F f
    (fun z => by change v z ≤ 1 ↔ v (f z) ≤ 1; rw [hval z]) 1
  let : Module ℤ_[p] (Additive (CompleteDVF.higherPrincipalUnitGroup F 1)) :=
    principalUnitPadicModuleOfMixedChar v p
  have : ContinuousSMul ℤ_[p] (Additive (CompleteDVF.higherPrincipalUnitGroup F 1)) :=
    principalUnitPadicContinuousSMul (K := K) p
      (hres := by change CharP (IsLocalRing.ResidueField v.valuationSubring) p; infer_instance)
  have hf : Continuous f :=
    ValuationTheory.DiscreteValuationField.Valuation.continuous_ringEquiv_of_preserves v f hval
  have he : Continuous e := continuous_restrictedAutomorphism F f
    (fun z => by change v z ≤ 1 ↔ v (f z) ≤ 1; rw [hval z]) hf 1
  have : T2Space (Additive (CompleteDVF.higherPrincipalUnitGroup F 1)) :=
    (principalUnitAdicContinuousAddEquiv (K := K)).toHomeomorph.t2Space
  have h := map_padicInt_smul_of_continuous e.toAdditive.toAddMonoidHom he a (Additive.ofMul x)
  exact congrArg Additive.toMul h

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
