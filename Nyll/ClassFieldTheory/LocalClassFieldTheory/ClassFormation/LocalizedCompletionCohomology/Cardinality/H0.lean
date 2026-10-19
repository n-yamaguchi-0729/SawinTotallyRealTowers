/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Finite
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Induced
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization
import Nyll.ValuedFieldTheory.Valuation.Completion.FiniteLocalization
import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core
import Nyll.GaloisCohomology.Cyclic.Herbrand.Induced
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Generator
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.HerbrandEquiv
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteExtensionClassFieldAxiom

/-!
# Degree-zero localized Herbrand cardinality
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

theorem localHerbrandH0_card_eq_localDegree
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
    Nat.card
        (HerbrandH0
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ) =
      Module.finrank vK.Completion
        (LocalizedCompletion vK w) := by
  intro hK hSMulK hCompletion hGlobal hTower hFinite hGalois hFintype hAction hFiniteH0
  let g :=
    localizedCompletionGaloisGenerator
      vK hvK w σ hgen
  let hg :=
    localizedCompletionGaloisGenerator_generates
      vK hvK w σ hgen
  let hcard :=
    finiteExtensionUnits_tate_card_of_generator
      vK.Completion (LocalizedCompletion vK w)
      g hg
  let : Finite
      (tateCohomology
        (Rep.ofAlgebraAutOnUnits vK.Completion
          (LocalizedCompletion vK w)) 0) :=
    hcard.finiteH0
  calc
    Nat.card
        (HerbrandH0
          (absoluteValueDecompositionGroup k w.1)
          (LocalizedCompletion vK w)ˣ) =
      Nat.card
        (Multiplicative
          (tateCohomology
            (Rep.ofAlgebraAutOnUnits vK.Completion
              (LocalizedCompletion vK w)) 0)) :=
      Nat.card_congr
        (localHerbrandH0EquivUnitsTateH0
          vK hvK w).toEquiv
    _ = Nat.card
        (tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) 0) := rfl
    _ = Module.finrank vK.Completion
        (LocalizedCompletion vK w) :=
      hcard.cardH0


end LocalTateComparison

end LocalClassFieldTheory
