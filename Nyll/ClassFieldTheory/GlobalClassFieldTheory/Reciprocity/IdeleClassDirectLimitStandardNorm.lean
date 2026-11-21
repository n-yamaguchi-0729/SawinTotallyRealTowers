/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitAbstractFixed
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitAction
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardGaloisNorm
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormComparison

/-!
# Actual class norms in the number-field coefficient representation

The class-formation norm and the canonical standard idele-class norm agree
under the fixed-field equivalences. The proof uses the actual quotient Galois
group, its action on field elements, and the product formula for the norm.
-/

@[expose] public section

open scoped NumberField
open ClassFormation CyclicCohomology LocalClassFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

universe u

variable (K : Type u) [Field K] [NumberField K]

attribute [local instance] abstractRelativeFixedFieldNumberField

/-- The quotient action on an upper fixed coefficient is the conjugation of its
representative on the standard idele class group. -/
theorem abstractRelativeFixedFieldIdeleClassEquivFixed_cosetAction
    (H J : ClosedSubgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K))
    (hJH : J.toSubgroup ≤ H.toSubgroup)
    (hnormal : (extensionSubgroup H J hJH).Normal)
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) J)]
    (q : H.toSubgroup ⧸ extensionSubgroup H J hJH)
    (c : NumberField.IdeleClassGroup
      (𝓞 (abstractRelativeFixedField K (SeparableClosure K) hJH))
      (abstractRelativeFixedField K (SeparableClosure K) hJH)) :
    let _ := hnormal
    relativeCosetAction (ideleClassRepresentation K) H J hJH
        (abstractRelativeFixedFieldIdeleClassEquivFixed K H J hJH (Additive.ofMul c)) q =
      (abstractRelativeFixedFieldIdeleClassEquivFixed K H J hJH (Additive.ofMul
        (NumberField.IdeleClassGroup.congr
          ((abstractExtensionQuotientEquivGaloisGroup K (SeparableClosure K)
            H J hJH hnormal q).restrictScalars ℚ) c))).1 := by
  intro normality
  let F := abstractFixedField K (SeparableClosure K) H
  let E := abstractRelativeFixedField K (SeparableClosure K) hJH
  let E₀ : IntermediateField K (SeparableClosure K) :=
    abstractFixedField K (SeparableClosure K) J
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq' rfl
  let eQ : (H.toSubgroup ⧸ extensionSubgroup H J hJH) ≃* (E ≃ₐ[F] E) :=
    abstractExtensionQuotientEquivGaloisGroup K (SeparableClosure K) H J hJH hnormal
  refine Quotient.inductionOn' q ?_
  intro σ
  rw [relativeCosetAction_mk]
  change Additive.ofMul
      ((ideleClassDirectLimitSMul K).smul σ.1 (intermediateIdeleClassToDirectLimit K E₀ c)) =
    Additive.ofMul (intermediateIdeleClassToDirectLimit K E₀
      (NumberField.IdeleClassGroup.congr
        ((eQ (QuotientGroup.mk' (extensionSubgroup H J hJH) σ)).restrictScalars ℚ) c))
  apply congrArg Additive.ofMul
  apply intermediateIdeleClassToDirectLimit_conjugation K E₀ σ.1
    ((eQ (QuotientGroup.mk' (extensionSubgroup H J hJH) σ)).restrictScalars K)
  intro y
  exact (abstractExtensionQuotientEquivGaloisGroup_mk_apply_val
    K (SeparableClosure K) H J hJH hnormal σ y).symm

/-- The cohomological relative norm is the actual standard idele-class norm
on the same finite extension of fixed fields. -/
theorem abstractFixedFieldIdeleClassEquivFixed_norm
    (H J : ClosedSubgroup (SeparableClosure K ≃ₐ[K] SeparableClosure K))
    (hJH : J.toSubgroup ≤ H.toSubgroup)
    (hnormal : (extensionSubgroup H J hJH).Normal)
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) H)]
    [FiniteDimensional K (abstractFixedField K (SeparableClosure K) J)]
    [Finite (H.toSubgroup ⧸ extensionSubgroup H J hJH)]
    (c : NumberField.IdeleClassGroup
      (𝓞 (abstractRelativeFixedField K (SeparableClosure K) hJH))
      (abstractRelativeFixedField K (SeparableClosure K) hJH)) :
    relativeNorm (ideleClassRepresentation K) H J hJH
        (abstractRelativeFixedFieldIdeleClassEquivFixed K H J hJH (Additive.ofMul c)) =
      abstractFixedFieldIdeleClassEquivFixed K H
        (Additive.ofMul (NumberField.IdeleClassGroup.norm
          (abstractFixedField K (SeparableClosure K) H)
          (abstractRelativeFixedField K (SeparableClosure K) hJH) c)) := by
  classical
  let F := abstractFixedField K (SeparableClosure K) H
  let E := abstractRelativeFixedField K (SeparableClosure K) hJH
  let E₀ : IntermediateField K (SeparableClosure K) :=
    abstractFixedField K (SeparableClosure K) J
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional F E := FiniteDimensional.right ℚ F E
  let : IsGalois F E :=
    abstractRelativeFixedField_isGalois K (SeparableClosure K) H J hJH hnormal
  let : (extensionSubgroup H J hJH).Normal := hnormal
  let Q := H.toSubgroup ⧸ extensionSubgroup H J hJH
  let : Fintype Q := Fintype.ofFinite Q
  let eQ : Q ≃* (E ≃ₐ[F] E) :=
    abstractExtensionQuotientEquivGaloisGroup K (SeparableClosure K) H J hJH hnormal
  let i : Additive (NumberField.IdeleClassGroup (𝓞 E) E) →+
      Additive (ideleClassDirectLimit K) :=
    MonoidHom.toAdditive (intermediateIdeleClassToDirectLimit K E₀)
  let x := abstractRelativeFixedFieldIdeleClassEquivFixed K H J hJH (Additive.ofMul c)
  have haction (q : Q) :
      relativeCosetAction (ideleClassRepresentation K) H J hJH x q =
        i (Additive.ofMul (NumberField.IdeleClassGroup.congr
          ((eQ q).restrictScalars ℚ) c)) := by
    exact abstractRelativeFixedFieldIdeleClassEquivFixed_cosetAction K H J hJH hnormal q c
  have hnorm := relativeNorm_eq_mapped_sum (ideleClassRepresentation K) H J hJH
    x i eQ.toEquiv
    (fun σ : E ≃ₐ[F] E => Additive.ofMul
      (NumberField.IdeleClassGroup.congr (σ.restrictScalars ℚ) c)) haction
  have hprod := NumberField.IdeleClassGroup.fieldInclusion_norm_eq_prod_congr F E c
  have hsum :
      (∑ σ : E ≃ₐ[F] E, Additive.ofMul
        (NumberField.IdeleClassGroup.congr (σ.restrictScalars ℚ) c)) =
        Additive.ofMul (NumberField.IdeleClassGroup.fieldInclusion F E
          (NumberField.IdeleClassGroup.norm F E c)) := by
    apply Additive.toMul.injective
    rw [toMul_sum]
    exact hprod.symm
  let b := NumberField.IdeleClassGroup.norm F E c
  let F₀ := abstractFixedField K (SeparableClosure K) H
  let h : F₀ ≤ E₀ := abstractFixedField_le K (SeparableClosure K) hJH
  have hlast : i (Additive.ofMul (NumberField.IdeleClassGroup.fieldInclusion F E b)) =
      (abstractFixedFieldIdeleClassEquivFixed K H (Additive.ofMul b)).1 := by
    change Additive.ofMul
      (intermediateIdeleClassToDirectLimit K E₀ (finiteIdeleClassEmbedding K h b)) =
      Additive.ofMul (intermediateIdeleClassToDirectLimit K F₀ b)
    exact congrArg (fun y : ideleClassDirectLimit K => Additive.ofMul y)
      (intermediateIdeleClassToDirectLimit_embedding K h b)
  apply Subtype.ext
  exact hnorm.trans ((congrArg i hsum).trans hlast)

end GlobalClassFieldTheory.Reciprocity
