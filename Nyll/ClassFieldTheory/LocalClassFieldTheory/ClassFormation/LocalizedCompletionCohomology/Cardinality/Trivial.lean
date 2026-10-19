/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.HMinusOne
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Induced
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization
import Nyll.ValuedFieldTheory.Valuation.Completion.FiniteLocalization
import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core
import Nyll.GaloisCohomology.Cyclic.Herbrand.Induced
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Finite

/-!
# Triviality of localized degree-minus-one Herbrand cohomology
-/



open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open CyclicCohomology
open CyclicCohomology.ProfiniteCohomology.Herbrand
open scoped TensorProduct

noncomputable section

namespace LocalClassFieldTheory

section LocalTateComparison

variable {k ell : Type}
    [Field k] [Field ell] [Algebra k ell]
    [FiniteDimensional k ell] [IsGalois k ell]

theorem localHerbrandHMinusOne_eq_one
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell)
    (σ : ell ≃ₐ[k] ell)
    (hgen : ∀ τ : ell ≃ₐ[k] ell,
      τ ∈ Subgroup.zpowers σ)
    [ValuativeRel vK.Completion]
    [IsNonarchimedeanLocalField vK.Completion] :
    let hK : Algebra k w.1.Completion :=
      AbsoluteValue.extensionCompletionAlgebra
        (K := k) w.1
    let _ : SMul k w.1.Completion := hK.toSMul
    let _ : Algebra vK.Completion w.1.Completion :=
      AbsoluteValue.completionAlgebra vK w.1 w.2
    let _ : Algebra k (LocalizedCompletion vK w) :=
      localizedCompletionGlobalAlgebra vK w
    let _ : IsScalarTower k vK.Completion (LocalizedCompletion vK w) :=
      localizedCompletionIsScalarTower vK w
    let _ : FiniteDimensional vK.Completion
        (LocalizedCompletion vK w) :=
      localizedCompletionModuleFinite vK hvK w
    let _ : IsGalois vK.Completion
        (LocalizedCompletion vK w) :=
      HilbertRamification.algebraicLocalization_isGalois vK w
    let _ : Fintype (absoluteValueDecompositionGroup k w.1) :=
      Fintype.ofFinite _
    let _ : MulDistribMulAction (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ :=
      decompositionGroupLocalUnitsAction vK hvK w
    ∀ c : HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1)
          σ hgen),
      c = 1 := by
  intro hK hSMulK hCompletion hGlobal hTower hFinite hGalois hFintype hAction
  let _ : Finite
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1)
          σ hgen)) :=
    localHerbrandHMinusOneFinite
      vK hvK w σ hgen
  have hcard :
      Nat.card
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup k w.1)
            σ hgen)) = 1 := by
    exact localHerbrandHMinusOne_card_eq_one
      vK hvK w σ hgen
  let _ : Subsingleton
      (HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1)
          σ hgen)) :=
    (Nat.card_eq_one_iff_unique.mp hcard).1
  intro c
  exact Subsingleton.elim c 1


end LocalTateComparison

end LocalClassFieldTheory
