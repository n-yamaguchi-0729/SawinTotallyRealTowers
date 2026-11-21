/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFormationPGroupH1
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Cohomology.StandardIdeleClassRepresentation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitAction
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ConcreteReciprocityCanonical
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FiniteGaloisPresentation

/-! # First cohomology of standard idele classes over a finite p-extension -/

@[expose] public section

open CategoryTheory ClassFormation CyclicCohomology GlobalClassFieldTheory.Cohomology
open GlobalClassFieldTheory.Reciprocity LocalClassFieldTheory
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem ideleClassToFixed_conjugation
    (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
    (j : L ≃ₐ[K] F) (σ : Gal(SeparableClosure K/K)) (τ : Gal(L/K))
    (h : ∀ x : L, (j (τ x) : SeparableClosure K) = σ (j x : SeparableClosure K))
    (c : NumberField.IdeleClassGroup (𝓞 L) L) :
    (ideleClassDirectLimitSMul K).smul σ (intermediateIdeleClassToDirectLimit K F
        (NumberField.IdeleClassGroup.congr (j.restrictScalars ℚ) c)) =
      intermediateIdeleClassToDirectLimit K F
        (NumberField.IdeleClassGroup.congr (j.restrictScalars ℚ)
          (NumberField.IdeleClassGroup.congr (τ.restrictScalars ℚ) c)) := by
  let τF : Gal(F/K) := AlgEquiv.autCongr j τ
  have hF (y : F) : (τF y : SeparableClosure K) = σ (y : SeparableClosure K) := by
    obtain ⟨x, rfl⟩ := j.surjective y
    change (j (τ (j.symm (j x))) : SeparableClosure K) = σ (j x : SeparableClosure K)
    rw [j.symm_apply_apply]
    exact h x
  have hj : (j.restrictScalars ℚ).trans (τF.restrictScalars ℚ) =
      (τ.restrictScalars ℚ).trans (j.restrictScalars ℚ) := by
    apply AlgEquiv.ext
    intro x
    change j (τ (j.symm (j x))) = j (τ x)
    rw [j.symm_apply_apply]
  rw [intermediateIdeleClassToDirectLimit_conjugation K F σ τF hF,
    NumberField.IdeleClassGroup.congr_trans, NumberField.IdeleClassGroup.congr_trans, hj]

/-- The standard idele-class module has vanishing first cohomology over
an actual p-extension, using the class formation of the original base. -/
theorem standardIdeleClassH1_subsingleton_of_isPGroup
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p Gal(L/K)) :
    Subsingleton (groupCohomology.H1 (standardIdeleClassRep K L)) := by
  let i : L →ₐ[K] SeparableClosure K :=
    AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L
  let B := intrinsicFiniteAbstractBase K
  let T := finiteGaloisAbstractExtensionOfEmbedding K L i
  let H := B.field
  let J := T.field
  let Q := T.extensionQuotient
  let F := abstractFixedField K (SeparableClosure K) J
  let j : L ≃ₐ[K] F := FunctionField.finiteGaloisEmbeddedFixedFieldEquiv K L i
  let : FiniteDimensional K F := j.toLinearEquiv.finiteDimensional
  let eG : Q ≃* Gal(L/K) := finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding K L i
  let C := standardIdeleClassRep K L
  let A := ideleClassRepresentation K
  let M := extensionFixedRepresentation A H J T.below T.normal
  let eAmbient := extensionFixedRepresentationEquiv A H J T.below T.normal
  let eFixed : C ≃+ KummerTheory.ambientFixedAddSubgroup A J :=
    (NumberField.IdeleClassGroup.congr (j.restrictScalars ℚ)).toAdditive.trans
      (abstractFixedFieldIdeleClassEquivFixed K J)
  have hAction (q : Q) (c : C) :
      relativeCosetAction A H J T.below (eFixed c) q = (eFixed (C.ρ (eG q) c)).val := by
    let : (extensionSubgroup H J T.below).Normal := T.normal
    refine QuotientGroup.induction_on q fun σ => ?_
    rw [relativeCosetAction_mk]
    let τ := eG (QuotientGroup.mk σ)
    have hτσ (x : L) : (j (τ x) : SeparableClosure K) = σ.val (j x : SeparableClosure K) := by
      change i (τ x) = σ.val (i x)
      exact finiteGaloisAbstractQuotientEquivGaloisGroupOfEmbedding_mk_apply K L i σ x
    have h := ideleClassToFixed_conjugation K L F j σ.val τ hτσ c.toMul
    exact congrArg Additive.ofMul h
  let : Module ℤ M := M.hV2
  let : Module ℤ C := C.hV2
  let eC : M ≃ₗ[ℤ] C := (eAmbient.trans eFixed.symm).toIntLinearEquiv
  have he (q : Q) : eC.toLinearMap ∘ₗ M.ρ q = C.ρ (eG q) ∘ₗ eC.toLinearMap := by
    apply LinearMap.ext
    intro x
    let c : C := eC x
    have hc : eFixed c = eAmbient x := eFixed.apply_symm_apply _
    change eC (M.ρ q x) = C.ρ (eG q) c
    apply eFixed.injective
    apply Subtype.ext
    calc
      (eFixed (eC (M.ρ q x))).val = (eAmbient (M.ρ q x)).val :=
        congrArg Subtype.val (eFixed.apply_symm_apply _)
      _ = relativeCosetAction A H J T.below (eAmbient x) q :=
        extensionFixedRepresentation_action_coe A H J T.below T.normal q x
      _ = relativeCosetAction A H J T.below (eFixed c) q :=
        congrArg (fun d => relativeCosetAction A H J T.below d q) hc.symm
      _ = (eFixed (C.ρ (eG q) c)).val := hAction q c
  let eH := groupCohomology.mapIso (A := C) (B := M) eG eC he 1
  have hM : Subsingleton (groupCohomology.H1 M) :=
    ClassFieldTower.Cohomology.pClassFormationH1_subsingleton A
      (ideleClassRepresentation_satisfiesClassFieldAxiom K) B T (hP.of_equiv eG.symm)
  refine ⟨fun x y => eH.symm.toLinearEquiv.injective ?_⟩
  exact @Subsingleton.elim _ hM _ _

end ClassFieldTower.Martinet.Shafarevich
