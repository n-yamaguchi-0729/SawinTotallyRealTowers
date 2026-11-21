/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FieldRepresentation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.StandardIdeleClassTate
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitCore
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitStandardNorm
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport

/-!
# The number-field idele-class formation

The standard class group of the actual upper fixed field supplies the coefficients of
each finite cyclic subextension. The quotient action is restriction of absolute Galois
automorphisms and the arithmetic low-degree calculation uses the same cyclic generator.
-/

@[expose] public section

open scoped NumberField
open CategoryTheory ClassFormation CyclicCohomology LocalClassFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

universe u

private def fixedIdeleClassRepIso (K : Type u) [Field K] [NumberField K]
    (B : FiniteAbstractField Gal(SeparableClosure K/K)) (C : FiniteCyclicSubextension B) :
    let H := B.field
    let J := C.field
    let hJH := C.below
    have hJfinite := FiniteGaloisSubextension.finite_extension_trans hJH (le_baseField H)
    let F := abstractFixedField K (SeparableClosure K) H
    let E := abstractRelativeFixedField K (SeparableClosure K) hJH
    let : FiniteDimensional K F :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) H B.finite
    let : FiniteDimensional K (abstractFixedField K (SeparableClosure K) J) :=
      abstractFixedField_finiteDimensional K (SeparableClosure K) J hJfinite
    let : FiniteDimensional F E :=
      abstractRelativeFixedField_finiteDimensional K (SeparableClosure K) H J hJH B.finite C.finite
    let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq' rfl
    let : NumberField E := abstractRelativeFixedFieldNumberField K hJH
    let : IsGalois F E :=
      abstractRelativeFixedField_isGalois K (SeparableClosure K) H J hJH C.normal
    let Q := H.toSubgroup ⧸ extensionSubgroup H J hJH
    let eQ : Q ≃* Gal(E/F) :=
      abstractExtensionQuotientEquivGaloisGroup K (SeparableClosure K) H J hJH C.normal
    let CE := NumberField.IdeleClassGroup (𝓞 E) E
    let _ := NumberField.IdeleClassGroup.relativeGaloisAction F E
    let U : Rep.{u} ℤ Gal(E/F) := Rep.ofMulDistribMulAction Gal(E/F) CE
    let M : Rep.{u} ℤ Q := C.fixedRepresentation (ideleClassRepresentation K)
    M ≅ Rep.res eQ.toMonoidHom U := by
  intro H J hJH hJfinite F E hF hJ hFE hTower hNF hGal Q eQ CE action U M
  let eAmbient := extensionFixedRepresentationEquiv (ideleClassRepresentation K) H J hJH C.normal
  let eFixed := abstractRelativeFixedFieldIdeleClassEquivFixed K H J hJH
  let e : M.V ≃+ Additive CE := eAmbient.trans eFixed.symm
  have he (x : M.V) : eFixed (e x) = eAmbient x := eFixed.apply_symm_apply _
  let Y : Rep.{u} ℤ Q := Rep.res eQ.toMonoidHom U
  let : Module ℤ M := M.hV2
  let : Module ℤ Y := Y.hV2
  let eₗ : M ≃ₗ[ℤ] Y := e.toIntLinearEquiv (modM := M.hV2) (modM₂ := Y.hV2)
  refine Rep.mkIso (Representation.Equiv.mk eₗ ?_)
  intro q
  apply LinearMap.ext
  intro x
  let c := NumberField.IdeleClassGroup.congr ((eQ q).restrictScalars ℚ) (e x).toMul
  change e (M.ρ q x) = Additive.ofMul c
  apply eFixed.injective
  apply Subtype.ext
  have hact := extensionFixedRepresentation_action_coe
    (ideleClassRepresentation K) H J hJH C.normal q x
  have hconj := abstractRelativeFixedFieldIdeleClassEquivFixed_cosetAction
    K H J hJH C.normal q (e x).toMul
  change relativeCosetAction (ideleClassRepresentation K) H J hJH
    (eFixed (e x)) q = (eFixed (Additive.ofMul c)).val at hconj
  exact (congrArg Subtype.val (he (M.ρ q x))).trans
    (hact.trans ((congrArg
      (fun a => relativeCosetAction (ideleClassRepresentation K) H J hJH a q)
      (he x).symm).trans hconj))

/-- The actual standard idele-class representation of any number field satisfies
the abstract class-field axiom. -/
theorem ideleClassRepresentation_satisfiesClassFieldAxiom
    (K : Type u) [Field K] [NumberField K] :
    SatisfiesClassFieldAxiom (ideleClassRepresentation K) := by
  intro B C
  let H := B.field
  let J := C.field
  let hJH := C.below
  have hJfinite : Finite ((baseField (SeparableClosure K ≃ₐ[K] SeparableClosure K)).toSubgroup ⧸
      extensionSubgroup (baseField (SeparableClosure K ≃ₐ[K] SeparableClosure K)) J
        (le_baseField J)) :=
    FiniteGaloisSubextension.finite_extension_trans hJH (le_baseField H)
  let F := abstractFixedField K (SeparableClosure K) H
  let E := abstractRelativeFixedField K (SeparableClosure K) hJH
  let : FiniteDimensional K F :=
    abstractFixedField_finiteDimensional K (SeparableClosure K) H B.finite
  let : FiniteDimensional K (abstractFixedField K (SeparableClosure K) J) :=
    abstractFixedField_finiteDimensional K (SeparableClosure K) J hJfinite
  let : FiniteDimensional F E :=
    abstractRelativeFixedField_finiteDimensional K (SeparableClosure K) H J hJH B.finite C.finite
  let : IsScalarTower K F E := IsScalarTower.of_algebraMap_eq' rfl
  let : NumberField E := abstractRelativeFixedFieldNumberField K hJH
  let : IsGalois F E := abstractRelativeFixedField_isGalois K (SeparableClosure K) H J hJH C.normal
  let Q := H.toSubgroup ⧸ extensionSubgroup H J hJH
  let P := Gal(E/F)
  let : Fintype P := inferInstanceAs (Fintype Gal(E/F))
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
  let eQ : Q ≃* P :=
    abstractExtensionQuotientEquivGaloisGroup K (SeparableClosure K) H J hJH C.normal
  have hg' : ∀ σ : P, σ ∈ Subgroup.zpowers (eQ g) :=
    map_cyclicGenerator eQ g hg
  let CE := NumberField.IdeleClassGroup (𝓞 E) E
  let _ := NumberField.IdeleClassGroup.relativeGaloisAction F E
  let U : Rep.{u} ℤ P := Rep.ofMulDistribMulAction P CE
  let M : Rep.{u} ℤ Q := C.fixedRepresentation (ideleClassRepresentation K)
  let eM : M ≅ Rep.res eQ.toMonoidHom U := fixedIdeleClassRepIso K B C
  have hTate := ClassFieldAxiom.standardIdeleClass_integral_tate_lowDegree_finite_card_eq_finrank
    F E (eQ g) hg'
  have hdegree : Module.finrank F E = Nat.card (E ≃ₐ[F] E) :=
    (IsGalois.card_aut_eq_finrank F E).symm
  let T₀ := IntegralGroupCohomology.Universe.tate U 0
  let T₁ := IntegralGroupCohomology.Universe.tate U (-1)
  have hfin : Finite T₀ := hTate.1
  have hcard : Nat.card T₀ = Nat.card P := hTate.2.2.1.trans hdegree
  have hone : Nat.card T₁ = 1 := hTate.2.2.2
  exact ClassFieldAxiomCohomologyData.of_repIso (P := P)
    (ideleClassRepresentation K) B C g hg eQ hg' U eM hfin hcard hone

end GlobalClassFieldTheory.Reciprocity
