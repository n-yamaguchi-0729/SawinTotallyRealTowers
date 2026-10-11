/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProfiniteIntegers.PadicInverseLimit
import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
import Nyll.ProCGroups.FiniteGroups.StandardClasses

/-! # P-adic characters factor through the maximal pro-p quotient -/

namespace ProCGroups.ProC

universe u

private theorem finite_pGroup_basis
    {p : ℕ} [Fact p.Prime]
    {B : Type u} [Group B] [TopologicalSpace B] [IsTopologicalGroup B]
    [Finite B] [DiscreteTopology B] (hB : IsPGroup p B) :
    HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p) B := by
  apply HasOpenNormalBasisInClass.of_allOpenNormalQuotients
  intro U
  exact ⟨inferInstance, hB.of_surjective (QuotientGroup.mk' (U : Subgroup B))
    (QuotientGroup.mk'_surjective _)⟩

/-- Every continuous p-adic character kills the pro-p residual core. -/
theorem proPResidualCore_le_ker_padicCharacter
    {p : ℕ} [Fact p.Prime]
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] (f : A →ₜ* Multiplicative (PadicInt p)) :
    proCResidualCore (FiniteGroupClass.pGroup p) A ≤ f.toMonoidHom.ker := by
  intro a ha
  change (f a).toAdd = 0
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  have : NeZero (p ^ n) := ⟨pow_ne_zero n (Fact.out : p.Prime).ne_zero⟩
  let ψ : A →ₜ* ULift.{u} (Multiplicative (ZMod (p ^ n))) :=
    { toFun := fun a => ULift.up (Multiplicative.ofAdd
        (PadicInt.toZModPow n (f a).toAdd))
      map_one' := by
        change ULift.up (Multiplicative.ofAdd (PadicInt.toZModPow n (f 1).toAdd)) = 1
        rw [map_one]
        apply ULift.ext
        change PadicInt.toZModPow n 0 = 0
        exact map_zero _
      map_mul' := by
        intro a b
        apply ULift.ext
        change PadicInt.toZModPow n (f (a * b)).toAdd =
          PadicInt.toZModPow n (f a).toAdd + PadicInt.toZModPow n (f b).toAdd
        rw [map_mul]; exact map_add _ _ _
      continuous_toFun := continuous_uliftUp.comp
        ((PadicInt.continuous_toZModPow n).comp f.continuous) }
  have hP : IsPGroup p (ULift.{u} (Multiplicative (ZMod (p ^ n)))) := by
    apply IsPGroup.of_card (n := n)
    simp only [Nat.card_eq_fintype_card, Fintype.card_ulift,
      Fintype.card_multiplicative, ZMod.card]
  have hB : HasOpenNormalBasisInClass (FiniteGroupClass.pGroup p)
      (ULift.{u} (Multiplicative (ZMod (p ^ n)))) := finite_pGroup_basis hP
  have hzero := proCResidualCore_le_ker_of_continuousMonoidHom_to_proC
    (FiniteGroupClass.pGroup_hereditary p) ψ hB ha
  have hz := congrArg (fun x : ULift.{u} (Multiplicative (ZMod (p ^ n))) =>
    x.down.toAdd) hzero
  exact hz.trans (map_zero _).symm

/-- The induced p-adic character on the maximal pro-p quotient. -/
noncomputable def liftPadicCharacter
    {p : ℕ} [Fact p.Prime]
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] (f : A →ₜ* Multiplicative (PadicInt p)) :
    A ⧸ proCResidualCore (FiniteGroupClass.pGroup p) A →ₜ* Multiplicative (PadicInt p) :=
  ProCGroups.QuotientGroup.liftₜ _ f (proPResidualCore_le_ker_padicCharacter f)

@[simp] theorem liftPadicCharacter_mk
    {p : ℕ} [Fact p.Prime]
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] (f : A →ₜ* Multiplicative (PadicInt p)) (a : A) :
    liftPadicCharacter f (QuotientGroup.mk' _ a) = f a := rfl

end ProCGroups.ProC
