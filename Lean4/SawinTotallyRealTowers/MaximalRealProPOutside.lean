/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.FiniteRealPExtension
import SawinTotallyRealTowers.FiniteRealPExtensionSupport
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.SeparableClosure

set_option autoImplicit false

/-!
# The maximal real compositum with prescribed ramification support

The field is formed from the concrete directed family of finite layers.
Galoisness and total reality follow from the corresponding properties of
those layers. The pro-p property and arithmetic rank estimates are separate
theorems, not inputs to this construction.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Sawin

/-- The compositum of all admissible finite real p-extensions of ℚ inside
its fixed algebraic closure. -/
def maximalRealProPOutside (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    IntermediateField ℚ (AlgebraicClosure ℚ) :=
  ⨆ E : FiniteRealPExtension p T, E.val.toIntermediateField

/-- Every admissible finite layer is contained in the maximal compositum. -/
theorem le_maximalRealProPOutside {p : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 ℚ))}
    (E : FiniteRealPExtension p T) :
    E.val.toIntermediateField ≤ maximalRealProPOutside p T :=
  le_iSup (fun F : FiniteRealPExtension p T ↦ F.val.toIntermediateField) E

/-- The constructed maximal compositum is Galois over ℚ. -/
theorem maximalRealProPOutside_isGalois (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    IsGalois ℚ (maximalRealProPOutside p T) := by
  change IsGalois ℚ
    ((⨆ E : FiniteRealPExtension p T, E.val.toIntermediateField) :
      IntermediateField ℚ (AlgebraicClosure ℚ))
  exact
    { to_isSeparable := IntermediateField.isSeparable_iSup ℚ (AlgebraicClosure ℚ)
        (h := fun E : FiniteRealPExtension p T ↦ E.val.isGalois.to_isSeparable)
      to_normal := IntermediateField.normal_iSup ℚ (AlgebraicClosure ℚ)
        (fun E : FiniteRealPExtension p T ↦ E.val.toIntermediateField)
        (h := fun E : FiniteRealPExtension p T ↦ E.val.isGalois.to_normal) }

/-- Total reality is preserved by the full, possibly infinite compositum. -/
theorem maximalRealProPOutside_isTotallyReal (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    IsTotallyReal (maximalRealProPOutside p T) := by
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  let : Nonempty (FiniteRealPExtension p T) := ⟨FiniteRealPExtension.bot p T⟩
  let : ∀ E : FiniteRealPExtension p T,
      IsTotallyReal E.val.toIntermediateField.toSubfield := fun E ↦
    (isUnramifiedAtInfinitePlaces_rat_iff_isTotallyReal E.val).mp E.property.2.2
  have hReal : IsTotallyReal
      (⨆ E : FiniteRealPExtension p T,
        E.val.toIntermediateField.toSubfield : Subfield (AlgebraicClosure ℚ)) :=
    NumberField.isTotallyReal_iSup
  rw [← IntermediateField.iSup_toSubfield
    (fun E : FiniteRealPExtension p T ↦ E.val.toIntermediateField)] at hReal
  exact hReal

/-- A finite Galois intermediate field lies in the maximal compositum
exactly when it satisfies the original arithmetic conditions. Directed
finite support and descent rule out additional inadmissible finite layers. -/
theorem isAdmissibleFiniteLayer_iff_le_maximalRealProPOutside
    (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) :
    IsAdmissibleFiniteLayer p T E ↔
      E.toIntermediateField ≤ maximalRealProPOutside p T := by
  constructor
  · intro hE
    exact le_maximalRealProPOutside ⟨E, hE⟩
  · intro hE
    obtain ⟨C, hEC⟩ := finiteDimensional_le_iSup_realPExtension_exists_extension
      p T E.toIntermediateField hE
    exact IsAdmissibleFiniteLayer.of_le hEC C.property

end ClassFieldTower.Sawin
