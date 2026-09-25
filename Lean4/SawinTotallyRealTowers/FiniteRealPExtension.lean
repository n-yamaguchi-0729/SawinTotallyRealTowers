/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.GaloisPCompositum
import SawinTotallyRealTowers.RamificationSupportCompositum
import SawinTotallyRealTowers.RealCompositum
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

/-!
# Finite layers of the real tower with prescribed ramification

We select actual finite Galois intermediate fields of the fixed algebraic
closure of ℚ. The base field is a member and binary composita remain in the
family. These constructors provide the directed family used to form the
maximal tower; no infiniteness or presentation is assumed.
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Sawin

private local instance finiteGaloisNumberField
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) : NumberField E :=
  NumberField.of_module_finite ℚ E

/-- The finite layers permitted in the initial real pro-p tower. -/
def IsAdmissibleFiniteLayer (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ)))
    (E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)) : Prop :=
  IsPGroup p (E ≃ₐ[ℚ] E) ∧
    IsUnramifiedAtFinitePlacesOutside ℚ E T ∧
      IsUnramifiedAtInfinitePlaces ℚ E

/-- The identity layer satisfies the arithmetic conditions for every prime
parameter and every permitted support. -/
theorem isAdmissibleFiniteLayer_bot (p : ℕ)
    (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    IsAdmissibleFiniteLayer p T ⊥ := by
  let : IsGalois ℚ (⊥ : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)).toIntermediateField :=
    (⊥ : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)).isGalois
  refine ⟨?_, ?_, ?_⟩
  · apply IsPGroup.of_card (n := 0)
    rw [IsGalois.card_aut_eq_finrank ℚ
      (⊥ : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ))]
    change Module.finrank ℚ (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ)) = p ^ 0
    rw [IntermediateField.finrank_bot, pow_zero]
  · exact IsUnramifiedAtFinitePlacesOutside.congrTop
      (M := (⊥ : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)))
      (IntermediateField.botEquiv ℚ (AlgebraicClosure ℚ)).symm
      (IsUnramifiedAtFinitePlacesOutside.refl ℚ T)
  · apply (isUnramifiedAtInfinitePlaces_rat_iff_isTotallyReal
      (⊥ : IntermediateField ℚ (AlgebraicClosure ℚ))).mpr
    exact IsTotallyReal.ofRingEquiv
      (IntermediateField.botEquiv ℚ (AlgebraicClosure ℚ)).symm.toRingEquiv

/-- Binary composita preserve all three finite-layer conditions, including
when the prime parameter is two. -/
theorem IsAdmissibleFiniteLayer.sup {p : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 ℚ))}
    {E F : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    (hE : IsAdmissibleFiniteLayer p T E)
    (hF : IsAdmissibleFiniteLayer p T F) :
    IsAdmissibleFiniteLayer p T (E ⊔ F) := by
  let : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  exact ⟨isPGroup_galois_sup E.toIntermediateField F.toIntermediateField hE.1 hF.1,
    IsUnramifiedAtFinitePlacesOutside.sup
      E.toIntermediateField F.toIntermediateField T hE.2.1 hF.2.1,
    isUnramifiedAtInfinitePlaces_rat_sup
      E.toIntermediateField F.toIntermediateField hE.2.2 hF.2.2⟩

/-- A finite Galois subextension of an admissible layer remains admissible.
The restriction map supplies its p-group structure, and the tower descent
theorems supply both local conditions. -/
theorem IsAdmissibleFiniteLayer.of_le {p : ℕ}
    {T : Set (HeightOneSpectrum (𝓞 ℚ))}
    {E F : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ)}
    (hEF : E ≤ F) (hF : IsAdmissibleFiniteLayer p T F) :
    IsAdmissibleFiniteLayer p T E := by
  let : Algebra E F :=
    (IntermediateField.inclusion hEF).toRingHom.toAlgebra
  let : IsScalarTower ℚ E F := IsScalarTower.of_algebraMap_eq' rfl
  let : Normal ℚ E.toIntermediateField := E.isGalois.to_normal
  let : Normal ℚ F.toIntermediateField := F.isGalois.to_normal
  refine ⟨?_, IsUnramifiedAtFinitePlacesOutside.bot T hF.2.1, ?_⟩
  · exact hF.1.of_surjective (AlgEquiv.restrictNormalHom E)
      (AlgEquiv.restrictNormalHom_surjective F)
  · let : IsUnramifiedAtInfinitePlaces ℚ F := hF.2.2
    exact IsUnramifiedAtInfinitePlaces.bot ℚ E F

/-- Actual admissible finite layers, indexed without duplicating Mathlib's
finite Galois intermediate-field structure. -/
def FiniteRealPExtension (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ))) : Type :=
  {E : FiniteGaloisIntermediateField ℚ (AlgebraicClosure ℚ) //
    IsAdmissibleFiniteLayer p T E}

namespace FiniteRealPExtension

/-- The bottom layer of the directed family. -/
def bot (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    FiniteRealPExtension p T :=
  ⟨⊥, isAdmissibleFiniteLayer_bot p T⟩

/-- The concrete compositum of two admissible finite layers. -/
def sup {p : ℕ} {T : Set (HeightOneSpectrum (𝓞 ℚ))}
    (E F : FiniteRealPExtension p T) : FiniteRealPExtension p T :=
  ⟨E.val ⊔ F.val, E.property.sup F.property⟩

/-- Every pair of finite layers is contained in their admissible compositum. -/
theorem directed (p : ℕ) (T : Set (HeightOneSpectrum (𝓞 ℚ))) :
    Directed (· ≤ ·)
      (fun E : FiniteRealPExtension p T ↦ E.val.toIntermediateField) := by
  intro E F
  exact ⟨sup E F, le_sup_left, le_sup_right⟩

end FiniteRealPExtension

end ClassFieldTower.Sawin
