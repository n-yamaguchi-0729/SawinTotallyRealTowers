/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitAction

/-!
# Comparing the standard idèle-class limits along a closure embedding

An embedding of the chosen closure into the rational closure takes a finite
class to the same class of the image field. Finite transition maps and
compatible absolute automorphisms commute with this comparison.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

universe u

variable (K : Type u) [Field K] [NumberField K]
    (i : SeparableClosure K →ₐ[ℚ] SeparableClosure ℚ)

/-- The image of an intermediate field under an actual closure embedding. -/
abbrev rationalIntermediateFieldImage (F : IntermediateField K (SeparableClosure K)) :
    IntermediateField ℚ (SeparableClosure ℚ) :=
  (i.comp (F.val.restrictScalars ℚ)).fieldRange

/-- The original field is rationally isomorphic to its embedded image. -/
def rationalIntermediateFieldImageEquiv (F : IntermediateField K (SeparableClosure K)) :
    F ≃ₐ[ℚ] rationalIntermediateFieldImage K i F :=
  (i.comp (F.val.restrictScalars ℚ)).equivFieldRange

instance rationalIntermediateFieldImage_finiteDimensional
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F] :
    FiniteDimensional ℚ (rationalIntermediateFieldImage K i F) :=
  (rationalIntermediateFieldImageEquiv K i F).toLinearEquiv.finiteDimensional

private theorem rationalIntermediateFieldImage_mono
    {E F : IntermediateField K (SeparableClosure K)} (h : E ≤ F) :
    rationalIntermediateFieldImage K i E ≤ rationalIntermediateFieldImage K i F := by
  rintro _ ⟨x, rfl⟩
  exact ⟨IntermediateField.inclusion h x, rfl⟩

/-- Transport a finite original idèle class to the class of its embedded field. -/
def rationalStageMap
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F] :
    NumberField.IdeleClassGroup (𝓞 F) F →* ideleClassDirectLimit ℚ :=
  (intermediateIdeleClassToDirectLimit ℚ (rationalIntermediateFieldImage K i F)).comp
    (NumberField.IdeleClassGroup.congr (rationalIntermediateFieldImageEquiv K i F)).toMonoidHom

/-- The image-field map commutes with the original finite transition. -/
theorem rationalStageMap_transition
    {E F : IntermediateField K (SeparableClosure K)}
    [FiniteDimensional K E] [FiniteDimensional K F] (h : E ≤ F)
    (c : NumberField.IdeleClassGroup (𝓞 E) E) :
    rationalStageMap K i F (finiteIdeleClassEmbedding K h c) = rationalStageMap K i E c := by
  let E' := rationalIntermediateFieldImage K i E
  let F' := rationalIntermediateFieldImage K i F
  let h' : E' ≤ F' := rationalIntermediateFieldImage_mono K i h
  let e := rationalIntermediateFieldImageEquiv K i E
  let f := rationalIntermediateFieldImageEquiv K i F
  let : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let : Algebra E' F' := (IntermediateField.inclusion h').toRingHom.toAlgebra
  have hSquare (x : E) : f (algebraMap E F x) = algebraMap E' F' (e x) :=
    Subtype.ext rfl
  change intermediateIdeleClassToDirectLimit ℚ F'
    (NumberField.IdeleClassGroup.congr f (NumberField.IdeleClassGroup.fieldInclusion E F c)) = _
  rw [NumberField.IdeleClassGroup.congr_fieldInclusion e f hSquare]
  exact intermediateIdeleClassToDirectLimit_embedding ℚ h' (NumberField.IdeleClassGroup.congr e c)

/-- The closure embedding induces the comparison of the two standard class
limits by transporting actual finite idèle classes. -/
def ideleClassDirectLimitToRational : ideleClassDirectLimit K →* ideleClassDirectLimit ℚ := by
  let t := fun (E F : FiniteGaloisIntermediateField K (SeparableClosure K)) (h : E ≤ F) =>
    finiteIdeleClassTransition K h
  let g := fun E : FiniteGaloisIntermediateField K (SeparableClosure K) =>
    rationalStageMap K i E.toIntermediateField
  have hG : ∀ E F h c, g E c = g F (t E F h c) :=
    fun _ _ h c => (rationalStageMap_transition K i h c).symm
  exact { toFun := DirectLimit.lift t (fun E => g E) hG
          map_one' := DirectLimit.lift_one g hG
          map_mul' := DirectLimit.lift_mul g hG }

/-- On a finite Galois stage the map sends the original representative to
the same standard class of its image field. -/
theorem ideleClassDirectLimitToRational_finite
    (F : FiniteGaloisIntermediateField K (SeparableClosure K))
    (c : NumberField.IdeleClassGroup (𝓞 F) F) :
    ideleClassDirectLimitToRational K i (finiteIdeleClassToDirectLimit K F c) =
      intermediateIdeleClassToDirectLimit ℚ
        (rationalIntermediateFieldImage K i F.toIntermediateField)
        ((NumberField.IdeleClassGroup.congr
          (rationalIntermediateFieldImageEquiv K i F.toIntermediateField)) c) :=
  rfl

/-- The finite-class formula applies to every finite intermediate field. -/
theorem ideleClassDirectLimitToRational_intermediate
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
    (c : NumberField.IdeleClassGroup (𝓞 F) F) :
    ideleClassDirectLimitToRational K i (intermediateIdeleClassToDirectLimit K F c) =
      intermediateIdeleClassToDirectLimit ℚ (rationalIntermediateFieldImage K i F)
        (NumberField.IdeleClassGroup.congr (rationalIntermediateFieldImageEquiv K i F) c) := by
  let M := finiteIdeleClassNormalClosure K F
  let hFM : F ≤ M.toIntermediateField := IntermediateField.le_normalClosure F
  rw [intermediateIdeleClassToDirectLimit_of_le K M hFM, ideleClassDirectLimitToRational_finite]
  exact rationalStageMap_transition K i hFM c

/-- The comparison reflects equality because the finite-stage maps are
injective on the actual idèle classes. -/
theorem ideleClassDirectLimitToRational_injective :
    Function.Injective (ideleClassDirectLimitToRational K i) := by
  intro x y hxy
  obtain ⟨E, c, d, hx, hy⟩ := DirectLimit.exists_eq_mk₂
    (F := fun E : FiniteGaloisIntermediateField K (SeparableClosure K) =>
      NumberField.IdeleClassGroup (𝓞 E) E)
    (fun _ _ h => finiteIdeleClassTransition K h) x y
  let F := E.toIntermediateField
  let F' := rationalIntermediateFieldImage K i F
  let e := NumberField.IdeleClassGroup.congr (rationalIntermediateFieldImageEquiv K i F)
  change x = finiteIdeleClassToDirectLimit K E c at hx
  change y = finiteIdeleClassToDirectLimit K E d at hy
  have hEq : intermediateIdeleClassToDirectLimit ℚ F' (e c) =
      intermediateIdeleClassToDirectLimit ℚ F' (e d) := by
    rw [hx, hy, ideleClassDirectLimitToRational_finite,
      ideleClassDirectLimitToRational_finite] at hxy
    exact hxy
  have hcd : c = d := e.injective (intermediateIdeleClassToDirectLimit_injective ℚ F' hEq)
  exact hx.trans ((congrArg (finiteIdeleClassToDirectLimit K E) hcd).trans hy.symm)

/-- Compatible absolute Galois automorphisms act the same way on the
transported class representative. -/
theorem ideleClassDirectLimitToRational_smul
    (σ : Gal(SeparableClosure K/K)) (τ : Gal(SeparableClosure ℚ/ℚ))
    (h : ∀ x : SeparableClosure K, i (σ x) = τ (i x)) (c : ideleClassDirectLimit K) :
    ideleClassDirectLimitToRational K i ((ideleClassDirectLimitSMul K).smul σ c) =
      (ideleClassDirectLimitSMul ℚ).smul τ (ideleClassDirectLimitToRational K i c) := by
  obtain ⟨F, d, hd⟩ := DirectLimit.exists_eq_mk
    (F := fun E : FiniteGaloisIntermediateField K (SeparableClosure K) =>
      NumberField.IdeleClassGroup (𝓞 E) E)
    (f := fun _ _ h => finiteIdeleClassTransition K h) c
  change c = finiteIdeleClassToDirectLimit K F d at hd
  let F' := rationalIntermediateFieldImage K i F.toIntermediateField
  let e := rationalIntermediateFieldImageEquiv K i F.toIntermediateField
  let α := finiteIdeleClassAutomorphism K F σ
  let β : F' ≃ₐ[ℚ] F' := (e.symm.trans α).trans e
  have hβ (y : F') : (β y : SeparableClosure ℚ) = τ (y : SeparableClosure ℚ) := by
    obtain ⟨x, rfl⟩ := e.surjective y
    change (e (α (e.symm (e x))) : SeparableClosure ℚ) = τ (e x : SeparableClosure ℚ)
    rw [e.symm_apply_apply]
    change i (α x : SeparableClosure K) = τ (i (x : SeparableClosure K))
    rw [show (α x : SeparableClosure K) = σ (x : SeparableClosure K) from
      AlgEquiv.restrictNormal_commutes σ F x]
    exact h (x : SeparableClosure K)
  rw [hd, finiteIdeleClassToDirectLimit_smul, ideleClassDirectLimitToRational_finite,
    ideleClassDirectLimitToRational_finite,
    intermediateIdeleClassToDirectLimit_ambientAlgEquiv ℚ τ β hβ]
  change intermediateIdeleClassToDirectLimit ℚ F'
      (NumberField.IdeleClassGroup.congr e (NumberField.IdeleClassGroup.congr α d)) =
    intermediateIdeleClassToDirectLimit ℚ F'
      (NumberField.IdeleClassGroup.congr β (NumberField.IdeleClassGroup.congr e d))
  apply congrArg (intermediateIdeleClassToDirectLimit ℚ F')
  rw [NumberField.IdeleClassGroup.congr_trans, NumberField.IdeleClassGroup.congr_trans]
  have hComp : α.trans e = e.trans β := by
    apply AlgEquiv.ext
    intro x
    change e (α x) = e (α (e.symm (e x)))
    rw [e.symm_apply_apply]
  rw [hComp]

end GlobalClassFieldTheory.Reciprocity
