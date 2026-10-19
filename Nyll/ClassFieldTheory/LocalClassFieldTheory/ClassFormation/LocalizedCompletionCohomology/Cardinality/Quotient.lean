/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.Trivial
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Induced
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization
import Nyll.ValuedFieldTheory.Valuation.Completion.FiniteLocalization
import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core
import Nyll.GaloisCohomology.Cyclic.Herbrand.Induced
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Finite
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.H0
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Cardinality.HMinusOne

/-!
# Localized-units Herbrand quotient
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

theorem localUnits_herbrandQuotient_eq_localDegree
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
    let _ : Finite
        (HerbrandH0
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ) :=
      localHerbrandH0Finite vK hvK w σ hgen
    let _ : Finite
        (HerbrandHMinusOne
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ
          (subgroupGeneratorOfGenerator
            (absoluteValueDecompositionGroup k w.1)
            σ hgen)) :=
      localHerbrandHMinusOneFinite
        vK hvK w σ hgen
    herbrandQuotient
        (G := absoluteValueDecompositionGroup k w.1)
        (A := (LocalizedCompletion vK w)ˣ)
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1)
          σ hgen) =
      (Module.finrank vK.Completion
        (LocalizedCompletion vK w) : ℚ) := by
  intro hK hSMulK hCompletion hGlobal hTower hFinite hGalois hFintype hAction
    hFiniteH0 hFiniteHMinusOne
  rw [herbrandQuotient_eq_card_ratio,
    localHerbrandH0_card_eq_localDegree
      vK hvK w σ hgen,
    localHerbrandHMinusOne_card_eq_one
      vK hvK w σ hgen, Nat.cast_one, div_one]


end LocalTateComparison

end LocalClassFieldTheory
