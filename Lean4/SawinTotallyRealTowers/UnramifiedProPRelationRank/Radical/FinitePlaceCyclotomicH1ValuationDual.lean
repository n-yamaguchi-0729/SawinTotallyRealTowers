/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceCyclotomicKummerH1
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
/-!
# The cyclotomic local H¹ valuation line

At a finite place of the cyclotomic base, transport the normalized valuation
functional from local power classes to intrinsic continuous `H¹`.  Its image
is exactly the annihilator of the valuation-zero subspace.
-/

open NumberField IsDedekindDomain
open scoped NumberField Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.ProP KummerTheory

variable (F : Type) [Field F] [NumberField F]
variable (p : ℕ) [Fact p.Prime]

local instance finitePlaceCyclotomicH1ValuationDualFiniteDimensional :
    FiniteDimensional F (FinitePlaceCyclotomicBase F p) :=
  finiteDimensional_idealRadicalCyclotomicBase
    F p (Fact.out : p.Prime)

local instance finitePlaceCyclotomicH1ValuationDualNumberField :
    NumberField (FinitePlaceCyclotomicBase F p) :=
  NumberField.of_module_finite F (FinitePlaceCyclotomicBase F p)

local instance finitePlaceCyclotomicH1ValuationDualTopology (q : ℕ) :
    TopologicalSpace (ZMod q) := ⊥

local instance finitePlaceCyclotomicH1ValuationDualDiscreteTopology (q : ℕ) :
    DiscreteTopology (ZMod q) :=
  discreteTopology_bot _

local instance finitePlaceCyclotomicH1ValuationDualModule
    {q : ℕ} {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := G)) :=
  continuousH1ZModModule

/-- The dual of the intrinsic-local Kummer valuation coordinate. -/
noncomputable def finitePlaceCyclotomicCompletionH1ValuationDualEmbedding
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p))) :
    ZMod p →ₗ[ZMod p]
      Module.Dual (ZMod p)
        (ContinuousH1ZMod
          (p := p)
          (G := Field.absoluteGaloisGroup
            (v.adicCompletion (FinitePlaceCyclotomicBase F p)))) :=
  (finitePlaceCyclotomicCompletionH1Valuation F p v).dualMap.comp
    (LinearMap.lsmul (ZMod p) (ZMod p))

@[simp]
theorem finitePlaceCyclotomicCompletionH1ValuationDualEmbedding_apply
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p)))
    (a : ZMod p)
    (chi : ContinuousH1ZMod
      (p := p)
      (G := Field.absoluteGaloisGroup
        (v.adicCompletion (FinitePlaceCyclotomicBase F p)))) :
    finitePlaceCyclotomicCompletionH1ValuationDualEmbedding F p v a chi =
      a * finitePlaceCyclotomicCompletionH1Valuation F p v chi :=
  rfl

/-- The intrinsic `H¹` valuation line is the old valuation-defect line
transported through local Kummer theory. -/
theorem finitePlaceCyclotomicCompletionH1ValuationDualEmbedding_eq_transport
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p))) :
    finitePlaceCyclotomicCompletionH1ValuationDualEmbedding F p v =
      (finitePlaceCyclotomicCompletionKummerH1LinearEquiv F p v).symm.toLinearMap.dualMap.comp
        (finitePlaceValuationDefectDualEmbedding
          (FinitePlaceCyclotomicBase F p) p v) :=
  rfl

/-- The transported valuation line is exactly the annihilator of local
power classes of valuation zero. -/
theorem finitePlaceCyclotomicCompletionH1ValuationDualEmbedding_range
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p))) :
    LinearMap.range
        (finitePlaceCyclotomicCompletionH1ValuationDualEmbedding F p v) =
      (LinearMap.ker
        (finitePlaceCyclotomicCompletionH1Valuation F p v)).dualAnnihilator := by
  rw [finitePlaceCyclotomicCompletionH1ValuationDualEmbedding,
    LinearMap.range_comp_of_range_eq_top,
    LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  rw [LinearMap.range_eq_top]
  intro phi
  refine ⟨phi 1, ?_⟩
  apply LinearMap.ext
  intro x
  change phi 1 * x = phi x
  rw [mul_comm]
  change x • phi 1 = phi x
  rw [← phi.map_smul x 1]
  simp

/-- The transported valuation line remains injectively parametrized by
`ZMod p`. -/
theorem finitePlaceCyclotomicCompletionH1ValuationDualEmbedding_injective
    (v : HeightOneSpectrum
      (NumberField.RingOfIntegers (FinitePlaceCyclotomicBase F p))) :
    Function.Injective
      (finitePlaceCyclotomicCompletionH1ValuationDualEmbedding F p v) := by
  rw [finitePlaceCyclotomicCompletionH1ValuationDualEmbedding_eq_transport]
  exact (LinearMap.dualMap_injective_of_surjective
      (finitePlaceCyclotomicCompletionKummerH1LinearEquiv F p v).symm.surjective).comp
    (finitePlaceValuationDefectDualEmbedding_injective
      (FinitePlaceCyclotomicBase F p) p v)

end ClassFieldTower.Martinet.Shafarevich
