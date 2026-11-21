/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.Algebra.ShrinkFiniteExtension
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.SmallModel
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardClassComparison
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.CyclicIdeleClassNormIndex
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.LocalizedCompletionCohomology.CompMulEquiv
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.EquivariantEquiv
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.IntegralTateComparison

/-!
# Integral Tate cohomology of standard idele classes

For a cyclic number-field extension, the arithmetic Herbrand calculation on compatible
small fields computes the integral Tate groups of the original standard idele class group.
-/

@[expose] public section

open scoped NumberField
open CyclicCohomology CyclicCohomology.ProfiniteCohomology.Herbrand
open IntegralGroupCohomology.Universe LocalClassFieldTheory

noncomputable section

namespace GlobalClassFieldTheory.ClassFieldAxiom

universe u v

variable (F : Type u) (E : Type v)
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [FiniteDimensional F E] [IsGalois F E]

/-- The ordinary class action and the specified cyclic generator yield the arithmetic
Herbrand cardinalities on the original fields. -/
theorem standardIdeleClass_lowDegree_card_eq_finrank_cyclic
    (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) :
    let _ := NumberField.IdeleClassGroup.relativeGaloisAction F E
    Nat.card (HerbrandH0 (E ≃ₐ[F] E) (NumberField.IdeleClassGroup (𝓞 E) E)) =
        Module.finrank F E ∧
      Nat.card (HerbrandHMinusOne (E ≃ₐ[F] E) (NumberField.IdeleClassGroup (𝓞 E) E) σ) =
        1 := by
  intro originalAction
  let : Small.{0} F := ClassFieldTheory.numberField_small F
  let : Small.{0} E := ClassFieldTheory.numberField_small E
  let F₀ := Shrink.{0} F
  let E₀ := Shrink.{0} E
  let : NumberField F₀ := ClassFieldTheory.numberField_shrink F
  let : NumberField E₀ := ClassFieldTheory.numberField_shrink E
  let : Algebra F₀ E₀ := HasseArf.shrinkAlgebra F E
  let : FiniteDimensional F₀ E₀ := HasseArf.shrink_finiteDimensional F E
  let : IsGalois F₀ E₀ :=
    IsGalois.of_equiv_equiv (f := (Shrink.ringEquiv F).symm)
      (g := (Shrink.ringEquiv E).symm) (HasseArf.shrinkAlgebra_commutes F E)
  let eG : (E₀ ≃ₐ[F₀] E₀) ≃* (E ≃ₐ[F] E) := HasseArf.shrinkGalMulEquiv F E
  let σ₀ : E₀ ≃ₐ[F₀] E₀ := eG.symm σ
  have hσ₀ : ∀ τ : E₀ ≃ₐ[F₀] E₀, τ ∈ Subgroup.zpowers σ₀ :=
    map_cyclicGenerator eG.symm σ hσ
  let _ := RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction F₀ E₀
  let C := NumberField.IdeleClassGroup (𝓞 E) E
  let _ : MulDistribMulAction (E₀ ≃ₐ[F₀] E₀) C :=
    MulDistribMulAction.compHom C eG.toMonoidHom
  let eField : E₀ ≃ₐ[ℚ] E := (Shrink.ringEquiv E).toRatAlgEquiv
  let eClass : RelativeIdeleGroup.ClassGroup F₀ E₀ ≃* C :=
    (NumberField.IdeleClassGroup.relativeClassComparison F₀ E₀).trans
      (NumberField.IdeleClassGroup.congr eField)
  have heClass (τ : E₀ ≃ₐ[F₀] E₀) (c : RelativeIdeleGroup.ClassGroup F₀ E₀) :
      eClass (τ • c) = τ • eClass c := by
    change NumberField.IdeleClassGroup.congr eField
        (NumberField.IdeleClassGroup.relativeClassComparison F₀ E₀ (τ • c)) =
      NumberField.IdeleClassGroup.congr ((eG τ).restrictScalars ℚ)
        (NumberField.IdeleClassGroup.congr eField
          (NumberField.IdeleClassGroup.relativeClassComparison F₀ E₀ c))
    have htransport : (τ.restrictScalars ℚ).trans eField =
        eField.trans ((eG τ).restrictScalars ℚ) := by
      apply AlgEquiv.ext
      intro x
      exact (HasseArf.shrinkGalEquiv_apply F E τ x).symm
    rw [NumberField.IdeleClassGroup.relativeClassComparison_conjugation,
      NumberField.IdeleClassGroup.congr_trans, NumberField.IdeleClassGroup.congr_trans,
      htransport]
  let e0 := (herbrandH0EquivariantMulEquiv (G := Gal(E₀/F₀))
      (A := RelativeIdeleGroup.ClassGroup F₀ E₀) (B := C) eClass heClass).trans
    (herbrandH0CompMulEquiv (A := C) eG)
  let em := (herbrandHMinusOneEquivariantMulEquiv (G := Gal(E₀/F₀))
      (A := RelativeIdeleGroup.ClassGroup F₀ E₀) (B := C) eClass heClass σ₀).trans
    (herbrandHMinusOneCompMulEquiv (A := C) eG σ₀)
  have hNative := ideleClass_lowDegree_card_eq_finrank_cyclic F₀ E₀ σ₀ hσ₀
  have hdegree : Module.finrank F₀ E₀ = Module.finrank F E := by
    rw [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank]
    exact Nat.card_congr eG.toEquiv
  refine ⟨(Nat.card_congr e0.toEquiv).symm.trans (hNative.1.trans hdegree), ?_⟩
  have hminus := (Nat.card_congr em.toEquiv).symm.trans hNative.2
  change Nat.card (HerbrandHMinusOne (E ≃ₐ[F] E) C (eG (eG.symm σ))) = 1 at hminus
  rw [eG.apply_symm_apply] at hminus
  exact hminus

/-- The standard idele-class representation has the actual integral Tate cardinalities,
with the group action given by relative field automorphisms. -/
theorem standardIdeleClass_integral_tate_lowDegree_finite_card_eq_finrank
    (σ : E ≃ₐ[F] E) (hσ : ∀ τ : E ≃ₐ[F] E, τ ∈ Subgroup.zpowers σ) :
    let _ := NumberField.IdeleClassGroup.relativeGaloisAction F E
    let U := Rep.ofMulDistribMulAction (E ≃ₐ[F] E) (NumberField.IdeleClassGroup (𝓞 E) E)
    Finite (tate U 0) ∧ Finite (tate U (-1)) ∧
      Nat.card (tate U 0) = Module.finrank F E ∧ Nat.card (tate U (-1)) = 1 := by
  intro originalAction U
  let e0 := integralTateH0EquivHerbrandH0
    (A := NumberField.IdeleClassGroup (𝓞 E) E) σ hσ
  let em := integralTateHMinusOneEquivHerbrandHMinusOne
    (A := NumberField.IdeleClassGroup (𝓞 E) E) σ hσ
  have h := standardIdeleClass_lowDegree_card_eq_finrank_cyclic F E σ hσ
  have h0 : Nat.card (tate U 0) = Module.finrank F E :=
    (Nat.card_congr e0.toEquiv).trans h.1
  have hm : Nat.card (tate U (-1)) = 1 :=
    (Nat.card_congr em.toEquiv).trans h.2
  exact ⟨Nat.finite_of_card_ne_zero (h0.trans_ne Module.finrank_pos.ne'),
    Nat.finite_of_card_ne_zero (hm.trans_ne one_ne_zero), h0, hm⟩

end GlobalClassFieldTheory.ClassFieldAxiom
