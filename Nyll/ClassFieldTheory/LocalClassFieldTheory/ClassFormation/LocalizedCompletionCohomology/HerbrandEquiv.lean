/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Generator
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.Algebra
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.CompMulEquiv
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalBlocks.Induced
import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.CohomologyBridge
import Nyll.GaloisCohomology.Cyclic.TateH0.Invariants
import Nyll.GaloisCohomology.Cyclic.TateH0.NormImage
import Nyll.GaloisCohomology.Cyclic.TateH0.Main
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.AlgebraicLocalization
import Nyll.ValuedFieldTheory.Valuation.Completion.FiniteLocalization

/-!
# Low-degree Herbrand equivalences for a localized completion
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

/-- Degree-zero multiplicative Herbrand cohomology for a decomposition group
identified with degree-zero Tate cohomology of the localized field units. -/
noncomputable def localHerbrandH0EquivUnitsTateH0
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell) :
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
    HerbrandH0 (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ ≃*
      Multiplicative
        (tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) 0) := by
  intro hK hSMulK hCompletion hGlobal hTower hFinite hGalois hFintype hAction
  let e :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let eTate :
      (unitsInvariantSubmodule vK.Completion
          (LocalizedCompletion vK w) ⧸
        unitsTateH0NormSubmodule vK.Completion
          (LocalizedCompletion vK w)) ≃+
        tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) 0 :=
    (tateUnitsH0IsoInvariantsQuotient
      vK.Completion
      (LocalizedCompletion vK w)).symm.toLinearEquiv.toAddEquiv
  exact
    (herbrandH0CompMulEquiv
      (A := (LocalizedCompletion vK w)ˣ) e).trans
      ((herbrandH0MulEquivInvariantsNormQuotient
        vK.Completion (LocalizedCompletion vK w)).trans
          eTate.toMultiplicative)

/-- Degree-minus-one multiplicative Herbrand cohomology for a decomposition
group identified with degree-minus-one Tate cohomology of localized units. -/
noncomputable def localHerbrandHMinusOneEquivUnitsTateHminusOne
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell)
    (σ : ell ≃ₐ[k] ell)
    (hgen : ∀ τ : ell ≃ₐ[k] ell,
      τ ∈ Subgroup.zpowers σ) :
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
    HerbrandHMinusOne
        (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ
        (subgroupGeneratorOfGenerator
          (absoluteValueDecompositionGroup k w.1) σ hgen) ≃
      tateCohomology
        (Rep.ofAlgebraAutOnUnits vK.Completion
          (LocalizedCompletion vK w)) (-1) := by
  intro hK hSMulK hCompletion hGlobal hTower hFinite hGalois hFintype hAction
  let e :=
    decompositionGroupEquivAlgebraicLocalizationAut
      vK hvK w
  let δ :=
    subgroupGeneratorOfGenerator
      (absoluteValueDecompositionGroup k w.1) σ hgen
  let g :=
    localizedCompletionGaloisGenerator
      vK hvK w σ hgen
  let hg :=
    localizedCompletionGaloisGenerator_generates
      vK hvK w σ hgen
  exact
    (herbrandHMinusOneCompMulEquiv
      (A := (LocalizedCompletion vK w)ˣ)
      e δ).toEquiv.trans
      (herbrandHminusOneEquivUnitsTateHminusOne
        vK.Completion (LocalizedCompletion vK w)
        g hg)

/-- Degree-zero Herbrand cohomology for a decomposition group identified with
the norm quotient of the localized field extension. -/
noncomputable def localHerbrandH0EquivNormQuotient
    (vK : AbsoluteValue k ℝ) (hvK : vK.IsNontrivial)
    (w : AbsoluteValueExtension vK ell) :
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
    HerbrandH0 (absoluteValueDecompositionGroup k w.1)
        (LocalizedCompletion vK w)ˣ ≃*
      NormQuotient vK.Completion
        (LocalizedCompletion vK w) := by
  intro hK hSMulK hCompletion hGlobal hTower hFinite hGalois hFintype hAction
  let e0 :=
    localHerbrandH0EquivUnitsTateH0 vK hvK w
  let eAdd :
      tateCohomology
          (Rep.ofAlgebraAutOnUnits vK.Completion
            (LocalizedCompletion vK w)) 0 ≃+
        Additive
          (NormQuotient vK.Completion
            (LocalizedCompletion vK w)) :=
    (H0TateUnitsIsoNormQuotient
      vK.Completion
      (LocalizedCompletion vK w)).toLinearEquiv.toAddEquiv
  exact e0.trans <|
    eAdd.toMultiplicative.trans <|
      MulEquiv.multiplicativeAdditive
        (NormQuotient vK.Completion
          (LocalizedCompletion vK w))


end LocalTateComparison

end LocalClassFieldTheory
