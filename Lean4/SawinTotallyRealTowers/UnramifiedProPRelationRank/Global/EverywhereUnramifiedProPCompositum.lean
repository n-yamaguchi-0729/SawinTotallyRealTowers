import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.MaximalEverywhereUnramifiedProP
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.BinaryUnramifiedCompositum
import Mathlib.FieldTheory.Galois.GaloisClosure

set_option autoImplicit false
/-!
# Finite everywhere-unramified pro-p composita

This file bundles the finite Galois everywhere-unramified `p`-extensions
inside the chosen algebraic closure. For odd `p`, the bundle is closed under
binary composita.
-/

open scoped NumberField

noncomputable section

universe u

namespace ClassFieldTower.Martinet

/-- A finite Galois everywhere-unramified `p`-extension inside the chosen
algebraic closure. -/
structure FiniteEverywhereUnramifiedProPExtension
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) where
  /-- The intermediate field inside the chosen algebraic closure. -/
  field : IntermediateField F (AlgebraicClosure F)
  /-- Finiteness of the extension over the base field. -/
  [finiteDimensional : FiniteDimensional F field]
  /-- The extension is Galois over the base field. -/
  [isGalois : IsGalois F field]
  /-- The intermediate field is itself a number field. -/
  [numberField : NumberField field]
  /-- Its finite Galois group is a `p`-group. -/
  isPGroup : IsPGroup p (field ≃ₐ[F] field)
  /-- The extension is unramified at every finite and infinite place. -/
  everywhereUnramified : IsEverywhereUnramified F field

namespace FiniteEverywhereUnramifiedProPExtension

variable {F : Type u} [Field F] [NumberField F]
variable {p : ℕ}

attribute [instance] finiteDimensional isGalois numberField

/-- The base field, as the bottom intermediate field, is a candidate. -/
def bot : FiniteEverywhereUnramifiedProPExtension F p where
  field := ⊥
  finiteDimensional := inferInstance
  isGalois := inferInstance
  numberField := NumberField.of_module_finite F ↥(⊥ :
    IntermediateField F (AlgebraicClosure F))
  isPGroup := by
    apply IsPGroup.of_card (n := 0)
    rw [IsGalois.card_aut_eq_finrank F
      (⊥ : IntermediateField F (AlgebraicClosure F)),
      IntermediateField.finrank_bot, pow_zero]
  everywhereUnramified := by
    let hNumber : NumberField ↥(⊥ :
        IntermediateField F (AlgebraicClosure F)) :=
      NumberField.of_module_finite F ↥(⊥ :
        IntermediateField F (AlgebraicClosure F))
    let _ := hNumber
    exact everywhereUnramified_congrTop
      (IntermediateField.botEquiv F (AlgebraicClosure F)).symm
      (IsEverywhereUnramified.refl F)

/-- A product of two `p`-groups is a `p`-group. -/
private theorem isPGroup_prod
    {G H : Type*} [Group G] [Group H]
    (hG : IsPGroup p G) (hH : IsPGroup p H) :
    IsPGroup p (G × H) := by
  rintro ⟨g, h⟩
  obtain ⟨a, ha⟩ := hG g
  obtain ⟨b, hb⟩ := hH h
  refine ⟨a + b, Prod.ext ?_ ?_⟩
  · simp [pow_add, pow_mul, ha]
  · change h ^ p ^ (a + b) = 1
    rw [Nat.add_comm, pow_add, pow_mul, hb, one_pow]

/-- The Galois group of a binary compositum embeds into the product of the
Galois groups of its two factors, so it is a `p`-group. -/
private theorem isPGroup_sup
    (E₁ E₂ : FiniteEverywhereUnramifiedProPExtension F p) :
    IsPGroup p
      (↥(E₁.field ⊔ E₂.field) ≃ₐ[F]
        ↥(E₁.field ⊔ E₂.field)) := by
  let S : IntermediateField F (AlgebraicClosure F) :=
    E₁.field ⊔ E₂.field
  let A : IntermediateField F S :=
    IntermediateField.restrict
      (show E₁.field ≤ E₁.field ⊔ E₂.field from le_sup_left)
  let B : IntermediateField F S :=
    IntermediateField.restrict
      (show E₂.field ≤ E₁.field ⊔ E₂.field from le_sup_right)
  let eA : E₁.field ≃ₐ[F] A :=
    IntermediateField.restrictAlgEquiv
      (show E₁.field ≤ E₁.field ⊔ E₂.field from le_sup_left)
  let eB : E₂.field ≃ₐ[F] B :=
    IntermediateField.restrictAlgEquiv
      (show E₂.field ≤ E₁.field ⊔ E₂.field from le_sup_right)
  let hFiniteS : FiniteDimensional F S :=
    IntermediateField.finiteDimensional_sup E₁.field E₂.field
  let _ := hFiniteS
  let hGaloisS : IsGalois F S := inferInstance
  let _ := hGaloisS
  let hGaloisA : IsGalois F A := IsGalois.of_algEquiv eA
  let _ := hGaloisA
  let hGaloisB : IsGalois F B := IsGalois.of_algEquiv eB
  let _ := hGaloisB
  let rA : (S ≃ₐ[F] S) →* (A ≃ₐ[F] A) :=
    AlgEquiv.restrictNormalHom A
  let rB : (S ≃ₐ[F] S) →* (B ≃ₐ[F] B) :=
    AlgEquiv.restrictNormalHom B
  have hA : IsPGroup p (A ≃ₐ[F] A) :=
    E₁.isPGroup.of_equiv (AlgEquiv.autCongr eA)
  have hB : IsPGroup p (B ≃ₐ[F] B) :=
    E₂.isPGroup.of_equiv (AlgEquiv.autCongr eB)
  apply (isPGroup_prod hA hB).of_injective (rA.prod rB)
  apply (MonoidHom.ker_eq_bot_iff _).mp
  rw [MonoidHom.ker_prod]
  change (AlgEquiv.restrictNormalHom A).ker ⊓
      (AlgEquiv.restrictNormalHom B).ker = ⊥
  rw [IntermediateField.restrictNormalHom_ker,
    IntermediateField.restrictNormalHom_ker,
    ← IntermediateField.fixingSubgroup_sup]
  have hSup : A ⊔ B = ⊤ := by
    apply IntermediateField.lift_injective S
    rw [IntermediateField.lift_sup,
      IntermediateField.lift_restrict,
      IntermediateField.lift_restrict,
      IntermediateField.lift_top]
  rw [hSup, IntermediateField.fixingSubgroup_top]

/-- For odd `p`, the binary compositum of two bundled candidates is again a
bundled candidate. -/
def sup [Fact p.Prime] (hpOdd : Odd p)
    (E₁ E₂ : FiniteEverywhereUnramifiedProPExtension F p) :
    FiniteEverywhereUnramifiedProPExtension F p := by
  let S : IntermediateField F (AlgebraicClosure F) :=
    E₁.field ⊔ E₂.field
  letI hFiniteS : FiniteDimensional F S :=
    IntermediateField.finiteDimensional_sup E₁.field E₂.field
  letI hGaloisS : IsGalois F S := inferInstance
  letI hNumberS : NumberField S :=
    NumberField.of_module_finite F S
  have hPS : IsPGroup p (S ≃ₐ[F] S) :=
    isPGroup_sup E₁ E₂
  have hOddDegree : Odd (Module.finrank F S) := by
    obtain ⟨n, hn⟩ := hPS.exists_card_eq
    rw [← IsGalois.card_aut_eq_finrank F S, hn]
    exact hpOdd.pow
  exact
    { field := S
      finiteDimensional := hFiniteS
      isGalois := hGaloisS
      numberField := hNumberS
      isPGroup := hPS
      everywhereUnramified :=
        everywhereUnramified_sup_of_odd_finrank E₁.field E₂.field
          E₁.everywhereUnramified E₂.everywhereUnramified hOddDegree }

end FiniteEverywhereUnramifiedProPExtension

/-- The raw maximal compositum is the supremum of the canonically bundled
finite everywhere-unramified Galois `p`-extensions. -/
theorem maximalEverywhereUnramifiedProP_eq_iSup_extension
    (F : Type u) [Field F] [NumberField F]
    (p : ℕ) [Fact p.Prime] :
    maximalEverywhereUnramifiedProP F p =
      ⨆ E : FiniteEverywhereUnramifiedProPExtension F p, E.field := by
  apply le_antisymm
  · apply maximalEverywhereUnramifiedProP_le_of_forall_le F p
    intro M hFinite hGalois hP hNumber hEverywhere
    let E : FiniteEverywhereUnramifiedProPExtension F p :=
      { field := M
        finiteDimensional := hFinite
        isGalois := hGalois
        numberField := hNumber
        isPGroup := hP
        everywhereUnramified := hEverywhere }
    exact le_iSup (fun E : FiniteEverywhereUnramifiedProPExtension F p ↦
      E.field) E
  · apply iSup_le
    intro E
    exact le_maximalEverywhereUnramifiedProP F p E.field
      E.isPGroup E.everywhereUnramified

end ClassFieldTower.Martinet
