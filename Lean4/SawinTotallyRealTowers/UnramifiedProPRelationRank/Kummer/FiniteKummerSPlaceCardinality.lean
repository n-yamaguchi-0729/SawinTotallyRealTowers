/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteKummerSPlaceLocalization
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceFieldUnitsH2
import ClassFieldTheory.AlgebraicNumberTheory.Adele.RestrictedAction
import GaloisCohomology.Kummer.FiniteKummerCoefficientH2
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.Data.ZMod.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit false

/-!
# Cardinal bounds for finite-support Kummer images

Degree-two cohomology of the Kummer coefficient module is annihilated by
its exponent. Its localized image embeds in the product of the actual
local torsion groups. The proved kernel containment then gives a
surjection from that image to the field-unit coefficient image.
-/

open CategoryTheory NumberField IsDedekindDomain
open scoped NumberField TensorProduct BigOperators

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

private theorem kummerH2_nsmul_eq_zero
    (G : Type) [Group G] (n : ℕ)
    (x : groupCohomology (Rep.trivial ℤ G (ULift (ZMod n))) 2) : n • x = 0 := by
  refine groupCohomology.H2_induction_on
    (A := Rep.trivial ℤ G (ULift (ZMod n))) (C := fun y => n • y = 0) x ?_
  intro c
  have hc : n • c = 0 := by
    apply Subtype.ext
    funext a
    apply ULift.ext
    change n • (c.1 a).down = 0
    simp only [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [← map_nsmul, hc, map_zero]

private theorem range_finite_card_le_of_nsmul
    {A : Type} [AddCommGroup A] {ι : Type} [Fintype ι]
    (B : ι → Type) [∀ i, AddCommGroup (B i)]
    (f : A →+ ∀ i, B i) (n : ℕ) (hA : ∀ x : A, n • x = 0)
    (hFinite : ∀ i, Finite (B i))
    (hCard : ∀ i, Nat.card {x : B i // n • x = 0} ≤ n) :
    Finite f.range ∧ Nat.card f.range ≤ n ^ Fintype.card ι := by
  classical
  let _ (i : ι) : Finite (B i) := hFinite i
  let q : f.range → ∀ i, {x : B i // n • x = 0} := fun x i => ⟨x.1 i, by
    have hx : n • x.1 = 0 := by
      obtain ⟨a, ha⟩ := x.2
      rw [← ha, ← map_nsmul, hA, map_zero]
    exact congrFun hx i⟩
  have hq : Function.Injective q := by
    intro x y h
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun h i)
  have hprod : Nat.card (∀ i, {x : B i // n • x = 0}) ≤ n ^ Fintype.card ι := by
    rw [Nat.card_pi]
    calc
      (∏ i, Nat.card {x : B i // n • x = 0}) ≤ ∏ _i : ι, n :=
        Finset.prod_le_prod (fun i _ => hCard i)
      _ = n ^ Fintype.card ι := by rw [Finset.prod_const, Finset.card_univ]
  exact ⟨Finite.of_injective q hq, (Nat.card_le_card_of_injective q hq).trans hprod⟩

private theorem range_finite_card_le_of_ker_le
    {A B C : Type} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (f : A →+ B) (g : A →+ C) (hker : f.ker ≤ g.ker) [Finite f.range] :
    Finite g.range ∧ Nat.card g.range ≤ Nat.card f.range := by
  have hk : f.ker ≤ g.rangeRestrict.ker := by
    simpa only [AddMonoidHom.ker_rangeRestrict] using hker
  let q : A ⧸ f.ker →+ g.range := QuotientAddGroup.lift f.ker g.rangeRestrict hk
  have hq : Function.Surjective q :=
    QuotientAddGroup.lift_surjective_of_surjective f.ker g.rangeRestrict
      g.rangeRestrict_surjective hk
  let e := (QuotientAddGroup.quotientKerEquivRange f).symm
  have hsurj : Function.Surjective (fun x : f.range => q (e x)) := hq.comp e.surjective
  exact ⟨Finite.of_surjective _ hsurj, Nat.card_le_card_of_surjective _ hsurj⟩


open CyclicCohomology

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

local instance finiteKummerSPlaceCardinalityTensorAction
    (v : HeightOneSpectrum (𝓞 K)) :
    MulDistribMulAction Gal(L / K) (v.adicCompletion K ⊗[K] L)ˣ :=
  scalarTensorUnitsAction (K := K) (L := L) (A := v.adicCompletion K)

/-- The actual localized Kummer image lies in the product of the local
n-torsion groups, so it is finite with at most `n ^ S.card` elements. -/
theorem finiteKummerSPlaceH2Localization_range_finite_natCard_le
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+) [Fact (n : ℕ).Prime]
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hP : IsPGroup (n : ℕ) Gal(L / K)) :
    Finite (finiteKummerSPlaceH2Localization K L S n hmu).range ∧
      Nat.card (finiteKummerSPlaceH2Localization K L S n hmu).range ≤
        (n : ℕ) ^ S.card := by
  classical
  let B : {v : HeightOneSpectrum (𝓞 K) // v ∈ S} → Type := fun v =>
    groupCohomology
      (Rep.ofMulDistribMulAction Gal(L / K) (v.1.adicCompletion K ⊗[K] L)ˣ) 2
  have hFinite : ∀ v, Finite (B v) := fun v =>
    (finitePGroupFinitePlaceFieldUnitsH2_finite_isAddCyclic K L n hP v.1).1
  have hCard : ∀ v, Nat.card {x : B v // (n : ℕ) • x = 0} ≤ (n : ℕ) := fun v =>
    finitePGroupFinitePlaceFieldUnitsH2_torsion_natCard_le K L n hP v.1 n n.pos
  have h := range_finite_card_le_of_nsmul B
    (finiteKummerSPlaceH2Localization K L S n hmu) n
    (kummerH2_nsmul_eq_zero Gal(L / K) n) hFinite hCard
  simpa only [Fintype.card_coe] using h

/-- The field-unit Kummer image is a quotient of the localized image
under the proved kernel containment, and obeys the same finite bound. -/
theorem finiteKummerCoefficientH2Map_range_finite_natCard_le_of_unramified_outside
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ+) [Fact (n : ℕ).Prime]
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty)
    (hP : IsPGroup (n : ℕ) Gal(L / K))
    (hfin : ∀ v : HeightOneSpectrum (𝓞 K), v ∉ S →
      ChosenFinitePlaceIsUnramified (K := K) (L := L) v)
    (hinf : ∀ v : InfinitePlace K, (chosenInfinitePlaceAbove (L := L) v).IsUnramified K) :
    Finite (finiteKummerCoefficientH2Map K L n hmu).hom.toAddMonoidHom.range ∧
      Nat.card (finiteKummerCoefficientH2Map K L n hmu).hom.toAddMonoidHom.range ≤
        (n : ℕ) ^ S.card := by
  have hlocal := finiteKummerSPlaceH2Localization_range_finite_natCard_le K L S n hmu hP
  have : Finite (finiteKummerSPlaceH2Localization K L S n hmu).range := hlocal.1
  have hfield := range_finite_card_le_of_ker_le
    (finiteKummerSPlaceH2Localization K L S n hmu)
    (finiteKummerCoefficientH2Map K L n hmu).hom.toAddMonoidHom
    (finiteKummerSPlaceH2Localization_ker_le K L S n hmu hP hfin hinf)
  exact ⟨hfield.1, hfield.2.trans hlocal.2⟩

end ClassFieldTower.Martinet.Shafarevich
end
