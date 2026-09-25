/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.EverywhereUnramifiedBridge
import ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.CompositumUnramified
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.PGroup

set_option autoImplicit false
/-!
# Unramified composita over a changed base

If the images of A and B generate M over K, restriction embeds Gal(M/B)
into Gal(A/K). Inertia restricts into the inertia of A/K. Consequently
unramifiedness of A/K gives unramifiedness of M/B; B/K need not be
unramified. The same injection preserves the p-group condition, and odd
p supplies the infinite-place condition. The generating-range equality
is supplied by the concrete compositum construction at the application.
-/

open NumberField
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet

variable (K A B M : Type) [Field K] [Field A] [Field B] [Field M]
variable [Algebra K A] [Algebra K B] [Algebra K M] [Algebra A M] [Algebra B M]
variable [IsScalarTower K A M] [IsScalarTower K B M] [IsGalois K A]

local notation "RA" => AlgHom.fieldRange (IsScalarTower.toAlgHom K A M)
local notation "RB" => AlgHom.fieldRange (IsScalarTower.toAlgHom K B M)

/-- Restriction is injective when the two field images generate the top. -/
theorem compositumBaseChange_restriction_injective (hsup : RA ⊔ RB = ⊤) :
    Function.Injective (IntermediateField.restrictRestrictAlgEquivMapHom K A B M) := by
  apply (injective_iff_map_eq_one _).2
  intro σ hσ
  have hA : σ.restrictScalars K ∈ (RA).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro x ⟨y, rfl⟩
    have heq := AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) A y
    change algebraMap A M
      (IntermediateField.restrictRestrictAlgEquivMapHom K A B M σ y) = _ at heq
    rw [hσ] at heq
    exact heq.symm
  have hB : σ.restrictScalars K ∈ (RB).fixingSubgroup := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro x ⟨y, rfl⟩
    exact σ.commutes y
  have hfix : σ.restrictScalars K ∈ (RA ⊔ RB).fixingSubgroup := by
    rw [IntermediateField.fixingSubgroup_sup]
    exact ⟨hA, hB⟩
  rw [hsup, IntermediateField.fixingSubgroup_top, Subgroup.mem_bot] at hfix
  ext x
  exact congrArg (fun τ : Gal(M / K) ↦ τ x) hfix

/-- A p-group Galois extension remains a p-group extension under base change. -/
theorem compositumBaseChange_isPGroup {p : ℕ}
    (hsup : RA ⊔ RB = ⊤) (hP : IsPGroup p Gal(A / K)) :
    IsPGroup p Gal(M / B) :=
  hP.of_injective (IntermediateField.restrictRestrictAlgEquivMapHom K A B M)
    (compositumBaseChange_restriction_injective K A B M hsup)

variable [NumberField K] [NumberField A] [NumberField B] [NumberField M]
variable [FiniteDimensional K A] [FiniteDimensional B M] [IsGalois B M]

/-- Finite-place unramifiedness survives base change, by restriction of
actual ideal inertia. No unramifiedness of the new base is assumed. -/
theorem compositumBaseChange_finitePlaceUnramifiedness
    (hsup : RA ⊔ RB = ⊤) (hA : IsUnramifiedAtFinitePlaces K A) :
    IsUnramifiedAtFinitePlaces B M := by
  let r := IntermediateField.restrictRestrictAlgEquivMapHom K A B M
  have hr : Function.Injective r :=
    compositumBaseChange_restriction_injective K A B M hsup
  intro Q
  let _ : Q.asIdeal.IsPrime := Q.isPrime
  let _ : Q.asIdeal.IsMaximal := Q.isPrime.isMaximal Q.ne_bot
  apply HilbertRamification.Dedekind.isUnramifiedAt_of_inertiaGroup_eq_bot (K := B) Q.asIdeal
  apply bot_unique
  intro σ hσ
  change σ = 1
  apply hr
  rw [map_one]
  let QA : Ideal (𝓞 A) := Q.asIdeal.under (𝓞 A)
  have hQA0 : QA ≠ ⊥ := Ideal.under_ne_bot (𝓞 A) Q.ne_bot
  let _ : QA.IsMaximal := (inferInstance : QA.IsPrime).isMaximal hQA0
  have hI : HilbertRamification.Dedekind.inertiaGroup QA Gal(A / K) = ⊥ :=
    HilbertRamification.Dedekind.inertiaGroup_eq_bot_of_isUnramifiedAt QA
      (hA ⟨QA, inferInstance, hQA0⟩)
  rw [← Subgroup.mem_bot, ← hI]
  rw [HilbertRamification.Dedekind.mem_inertiaGroup_iff]
  intro x
  change algebraMap (𝓞 A) (𝓞 M) (r σ • x - x) ∈ Q.asIdeal
  rw [map_sub]
  have hcompat : algebraMap (𝓞 A) (𝓞 M) (r σ • x) =
      σ • algebraMap (𝓞 A) (𝓞 M) x := by
    apply RingOfIntegers.coe_injective
    change algebraMap A M (((σ.restrictScalars K).restrictNormal A) x.1) =
      σ (algebraMap A M x.1)
    exact AlgEquiv.restrictNormal_commutes (σ.restrictScalars K) A x.1
  rw [hcompat]
  exact (HilbertRamification.Dedekind.mem_inertiaGroup_iff.mp hσ)
    (algebraMap (𝓞 A) (𝓞 M) x)

/-- The base change of an unramified odd-p Galois extension is everywhere
unramified, including at infinity. -/
theorem compositumBaseChange_everywhereUnramified
    {p : ℕ} [Fact p.Prime] (hpOdd : Odd p)
    (hsup : RA ⊔ RB = ⊤) (hP : IsPGroup p Gal(A / K))
    (hA : IsUnramifiedAtFinitePlaces K A) : IsEverywhereUnramified B M := by
  refine ⟨compositumBaseChange_finitePlaceUnramifiedness K A B M hsup hA, ?_⟩
  have hPB := compositumBaseChange_isPGroup K A B M hsup hP
  obtain ⟨e, he⟩ := hPB.exists_card_eq
  apply IsUnramifiedAtInfinitePlaces_of_odd_card_aut
  rw [he]
  exact hpOdd.pow

end ClassFieldTower.Martinet
