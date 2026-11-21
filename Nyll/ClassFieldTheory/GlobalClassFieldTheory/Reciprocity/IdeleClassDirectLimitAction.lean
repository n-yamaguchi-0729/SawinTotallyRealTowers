/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteEmbedding
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.FieldEquivNaturality

/-!
# Finite automorphisms and the absolute idele-class action

The standard class inclusion intertwines a finite-field automorphism with
any compatible absolute lift. All maps preserve the actual field embedding.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- A compatible ambient automorphism and a finite-field equivalence give
the same map into the standard absolute limit. -/
theorem intermediateIdeleClassToDirectLimit_ambientAlgEquiv
    {E F : IntermediateField K (SeparableClosure K)}
    [FiniteDimensional K E] [FiniteDimensional K F]
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (e : E ≃ₐ[K] F)
    (hσe : ∀ x : E, ((e x : F) : SeparableClosure K) = σ (x : SeparableClosure K))
    (c : NumberField.IdeleClassGroup (𝓞 E) E) :
    (ideleClassDirectLimitSMul K).smul σ (intermediateIdeleClassToDirectLimit K E c) =
      intermediateIdeleClassToDirectLimit K F
        (NumberField.IdeleClassGroup.congr (e.restrictScalars ℚ) c) := by
  let U : FiniteGaloisIntermediateField K (SeparableClosure K) :=
    finiteIdeleClassNormalClosure K E ⊔ finiteIdeleClassNormalClosure K F
  let hEU : E ≤ U.toIntermediateField := (IntermediateField.le_normalClosure E).trans le_sup_left
  let hFU : F ≤ U.toIntermediateField := (IntermediateField.le_normalClosure F).trans le_sup_right
  let : Algebra E U := (IntermediateField.inclusion hEU).toRingHom.toAlgebra
  let : Algebra F U := (IntermediateField.inclusion hFU).toRingHom.toAlgebra
  have hcommute (x : E) :
      finiteIdeleClassAutomorphism K U σ (algebraMap E U x) =
        algebraMap F U ((e.restrictScalars ℚ) x) := by
    apply Subtype.ext
    exact (AlgEquiv.restrictNormal_commutes σ U (IntermediateField.inclusion hEU x)).trans
      (hσe x).symm
  rw [intermediateIdeleClassToDirectLimit_of_le K U hEU c,
    intermediateIdeleClassToDirectLimit_of_le K U hFU,
    finiteIdeleClassToDirectLimit_smul]
  apply congrArg (finiteIdeleClassToDirectLimit K U)
  exact NumberField.IdeleClassGroup.congr_fieldInclusion
    (e.restrictScalars ℚ) (finiteIdeleClassAutomorphism K U σ) hcommute c

/-- A finite-field automorphism and any compatible absolute lift induce the
same action after inclusion into the one standard idele-class limit. -/
theorem intermediateIdeleClassToDirectLimit_conjugation
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (τ : F ≃ₐ[K] F)
    (hστ : ∀ x : F, ((τ x : F) : SeparableClosure K) = σ (x : SeparableClosure K))
    (c : NumberField.IdeleClassGroup (𝓞 F) F) :
    (ideleClassDirectLimitSMul K).smul σ (intermediateIdeleClassToDirectLimit K F c) =
      intermediateIdeleClassToDirectLimit K F
        (NumberField.IdeleClassGroup.congr (τ.restrictScalars ℚ) c) :=
  intermediateIdeleClassToDirectLimit_ambientAlgEquiv K σ τ hστ c

end GlobalClassFieldTheory.Reciprocity
