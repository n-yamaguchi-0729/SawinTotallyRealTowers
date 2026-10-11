/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.QuotientPadicModule
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.PadicReductionContinuous
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.QuotientTransition
import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicLinearOfContinuous

/-!
# Continuity and compatibility of the principal-unit quotient actions

Reduction of scalars to `ZMod (p^n)` makes each coordinate action continuous.
Density of natural scalars then proves compatibility with quotient reduction.
-/

namespace LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
namespace DiscretePrincipalUnitQuotient

universe u v

variable {K : Type u} [Field K]
variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)
variable (p : ℕ) [Fact p.Prime] [CharP F.residueField p]

/-- The explicitly constructed action is jointly continuous. -/
theorem padicContinuousSMul (n : ℕ) :
    @ContinuousSMul ℤ_[p] (DiscretePrincipalUnitQuotient F n)
      (padicModule F p n).toSMul inferInstance inferInstance := by
  let : Module ℤ_[p] (DiscretePrincipalUnitQuotient F n) := padicModule F p n
  let : TopologicalSpace (ZMod (p ^ n)) := ⊥
  let : DiscreteTopology (ZMod (p ^ n)) := ⟨rfl⟩
  have hred : Continuous fun z : ℤ_[p] × DiscretePrincipalUnitQuotient F n =>
      PadicInt.toZModPow n z.1 :=
    (Internal.continuous_padicIntToZModPow p n).comp continuous_fst
  have hact : Continuous fun z : ZMod (p ^ n) × DiscretePrincipalUnitQuotient F n =>
      z.1.val • z.2 := continuous_of_discreteTopology
  refine ⟨?_⟩
  exact (hact.comp (hred.prodMk continuous_snd)).congr
    (fun z => (padic_smul_eq_val_nsmul F p n z.1 z.2).symm)

/-- Quotient reduction respects the actual p-adic actions. -/
theorem transition_padic_smul {m n : ℕ} (hmn : m ≤ n) (a : ℤ_[p])
    (x : DiscretePrincipalUnitQuotient F n) :
    transition F hmn ((padicModule F p n).toSMul.smul a x) =
      (padicModule F p m).toSMul.smul a (transition F hmn x) := by
  let : Module ℤ_[p] (DiscretePrincipalUnitQuotient F n) := padicModule F p n
  let : Module ℤ_[p] (DiscretePrincipalUnitQuotient F m) := padicModule F p m
  have : ContinuousSMul ℤ_[p] (DiscretePrincipalUnitQuotient F n) := padicContinuousSMul F p n
  have : ContinuousSMul ℤ_[p] (DiscretePrincipalUnitQuotient F m) := padicContinuousSMul F p m
  exact map_padicInt_smul_of_continuous (transition F hmn) continuous_of_discreteTopology a x

end DiscretePrincipalUnitQuotient
end LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
