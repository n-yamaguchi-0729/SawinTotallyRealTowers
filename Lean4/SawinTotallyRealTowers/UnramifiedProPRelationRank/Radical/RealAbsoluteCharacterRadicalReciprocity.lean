/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.InfiniteArtinCompatibility
import SawinTotallyRealTowers.AbsoluteRealKernelField
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.GlobalReciprocityCharacter
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteKummerH1Linear
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceH2Localization
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FinitePlaceUnramifiedH1
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.AbsoluteCharacterRadicalReciprocity
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.EmptySupportKummerCokernel
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceH1AdicRestriction
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportGlobalReciprocity
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportLocalReciprocityIdeleCharacter
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadical
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadicalAbsoluteKummerLinear
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.RealSignedIdeleCharacter
import ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Data.PNat.Basic
import Mathlib.GroupTheory.Coset.Defs
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.ZMod

set_option autoImplicit false

/-!
# Real-split quadratic characters annihilate the finite-support radical

The quotient of a principal-trivial idele character by its finite restriction
has the same real signs, since that restriction has only finite coordinates.
The real-signed quadratic idele theorem therefore annihilates its ideal-square
radical. Actual real and finite Artin comparisons give this reciprocity
statement for a real-split absolute quadratic character.
-/

open NumberField IsDedekindDomain
open scoped NumberField BigOperators Classical

namespace ClassFieldTower.Martinet.Shafarevich
open ClassFieldTower.ProP KummerTheory

variable (F : Type) [Field F] [NumberField F]

private theorem two_finite_restriction_principal_radical
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (psi : IdeleGroup F →ₜ* Multiplicative (ZMod 2))
    (hprincipal : ∀ a : Fˣ, psi (IdeleGroup.principalIdele F a) = 1)
    (hsign : ∀ v : InfinitePlace F, v.IsReal →
      psi (IdeleGroup.infinitePlaceIdele v (-1)) = 1)
    (houtside : ∀ (v : HeightOneSpectrum (𝓞 F)), v ∉ S →
      ∀ a : (v.adicCompletion F)ˣ, a ∈ (v.adicCompletionIntegers F).units →
        psi (IdeleGroup.finitePlaceIdele v a) = 1)
    (a : (idealNthPowerRadicalKummerSubgroup F (2 : ℕ+)).1) :
    (∏ v : ↥S, psi (IdeleGroup.finitePlaceIdele v.1
      (Units.map (algebraMap F (v.1.adicCompletion F)).toMonoidHom a.1))) = 1 := by
  let r : IdeleGroup F →ₜ* Multiplicative (ZMod 2) :=
    finiteSupportIdeleRestrictionCharacter F (2 : ℕ+) S psi
  let d : IdeleGroup F →ₜ* Multiplicative (ZMod 2) :=
    psi / r
  have hd : ∀ (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ),
      u ∈ (v.adicCompletionIntegers F).units → d (IdeleGroup.finitePlaceIdele v u) = 1 := by
    intro v u hu
    change psi (IdeleGroup.finitePlaceIdele v u) / r (IdeleGroup.finitePlaceIdele v u) = 1
    have hr : r (IdeleGroup.finitePlaceIdele v u) =
        if v ∈ S then psi (IdeleGroup.finitePlaceIdele v u) else 1 :=
      finiteSupportIdeleRestrictionCharacter_finitePlace F (2 : ℕ+) S psi v u
    rw [hr]
    by_cases hv : v ∈ S
    · rw [ite_eq_left hv, div_self']
    · rw [ite_eq_right hv, houtside v hv u hu, div_one]
  have hdSign : ∀ v : InfinitePlace F, v.IsReal →
      d (IdeleGroup.infinitePlaceIdele v (-1)) = 1 := by
    intro v hv
    have hr : r (IdeleGroup.infinitePlaceIdele v (-1)) = 1 := by
      change (∏ w : ↥S, psi (IdeleGroup.finitePlaceIdele w.1
        (IdeleGroup.finiteComponent w.1 (IdeleGroup.infinitePlaceIdele v (-1))))) = 1
      apply Finset.prod_eq_one
      intro w hw
      rw [IdeleGroup.infinitePlaceIdele_finiteComponent, map_one, map_one]
    change psi (IdeleGroup.infinitePlaceIdele v (-1)) /
      r (IdeleGroup.infinitePlaceIdele v (-1)) = 1
    rw [hsign v hv, hr, div_one]
  have h := ideleCharacter_two_principal_radical_eq_one_of_integral_local
    F d hdSign hd a
  change psi (IdeleGroup.principalIdele F a.1) /
    r (IdeleGroup.principalIdele F a.1) = 1 at h
  have hr : r (IdeleGroup.principalIdele F a.1) = 1 :=
    (div_eq_one.mp h).symm.trans (hprincipal a.1)
  exact hr

private theorem finiteSupport_absolute_eq_restriction
    (n : ℕ+) [Fact (n : ℕ).Prime]
    (chi : Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod (n : ℕ)))
    (S : Finset (HeightOneSpectrum (𝓞 F))) :
    finiteSupportLocalReciprocityIdeleCharacter F (n : ℕ) S
      (fun v ↦ finitePlaceAbsoluteH1AdicRestriction F (n : ℕ) v.1 (Additive.ofMul chi)) =
      finiteSupportIdeleRestrictionCharacter F n S (globalReciprocityIdeleCharacter F (n : ℕ) chi) := by
  ext z
  rw [finiteSupportLocalReciprocityIdeleCharacter_apply]
  change _ = ∏ v : ↥S, globalReciprocityIdeleCharacter F (n : ℕ) chi
    (IdeleGroup.finitePlaceIdele v.1 (IdeleGroup.finiteComponent v.1 z))
  apply Finset.prod_congr rfl
  intro v hv
  exact localReciprocityUnitCharacter_absoluteCharacter F n chi v.1
    (IdeleGroup.finiteComponent v.1 z)

/-- A real-split absolute quadratic character unramified outside S has a
finite-support reciprocity functional annihilating the actual ideal-square radical. -/
theorem absoluteCharacter_two_finiteSupport_radical_annihilator
    [IsTotallyReal F]
    (chi : Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod 2))
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (hreal : ∀ v : InfinitePlace F,
      chi (ClassFieldTower.Sawin.absoluteInfinitePlaceArtinNegOne F v) = 1)
    (houtside : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ∀ sigma : finitePlaceAbsoluteInertiaSubgroup F v,
        chi (finitePlaceAbsoluteDecompositionInclusion F v sigma.1) = 1) :
    absolutePowerClassDualRestriction F 2
      (finiteSupportLocalReciprocityPowerClassFunctional F 2 S
        (fun v ↦ finitePlaceAbsoluteH1AdicRestriction F 2 v.1 (Additive.ofMul chi))) = 0 := by
  ext x
  change finiteSupportLocalReciprocityPowerClassFunctional F 2 S
    (fun v ↦ finitePlaceAbsoluteH1AdicRestriction F 2 v.1 (Additive.ofMul chi))
    (idealPowerRadicalToAbsolutePowerClassLinearMap F 2 x) = 0
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  have hx : Additive.ofMul (QuotientGroup.mk a) = x := congrArg Additive.ofMul ha
  rw [← hx]
  let qa : absolutePowerClassModP F 2 :=
    Additive.ofMul (QuotientGroup.mk' (powMonoidHom 2 : Fˣ →* Fˣ).range a.1)
  change finiteSupportLocalReciprocityPowerClassFunctional F 2 S
    (fun v ↦ finitePlaceAbsoluteH1AdicRestriction F 2 v.1 (Additive.ofMul chi)) qa = 0
  have hprincipal :
      (finiteSupportLocalReciprocityIdeleCharacter F 2 S
        (fun v ↦ finitePlaceAbsoluteH1AdicRestriction F 2 v.1 (Additive.ofMul chi))
        (IdeleGroup.principalIdele F a.1)).toAdd =
        finiteSupportLocalReciprocityPowerClassFunctional F 2 S
          (fun v ↦ finitePlaceAbsoluteH1AdicRestriction F 2 v.1 (Additive.ofMul chi)) qa :=
    finiteSupportLocalReciprocityIdeleCharacter_principal_functional F 2 S
      (fun v ↦ finitePlaceAbsoluteH1AdicRestriction F 2 v.1 (Additive.ofMul chi)) a.1
  rw [← hprincipal]
  have hsign : ∀ v : InfinitePlace F, v.IsReal →
      globalReciprocityIdeleCharacter F 2 chi (IdeleGroup.infinitePlaceIdele v (-1)) = 1 := by
    intro v hv
    exact (ClassFieldTower.Sawin.globalReciprocityIdeleCharacter_infinite_neg_one F 2 chi v).trans
      (hreal v)
  have hprod := two_finite_restriction_principal_radical F S
    (globalReciprocityIdeleCharacter F 2 chi)
    (globalReciprocityIdeleCharacter_principal F 2 chi) hsign
    (fun v hv u hu ↦ globalReciprocityIdeleCharacter_integral_eq_one_of_inertia
      F (2 : ℕ+) chi v (houtside v hv) u hu) a
  have heq : finiteSupportLocalReciprocityIdeleCharacter F 2 S
      (fun v ↦ finitePlaceAbsoluteH1AdicRestriction F 2 v.1 (Additive.ofMul chi))
      (IdeleGroup.principalIdele F a.1) = 1 := by
    have hchar := finiteSupport_absolute_eq_restriction F (2 : ℕ+) chi S
    simp only [PNat.val_ofNat] at hchar
    have heval := congrArg (fun f : IdeleGroup F →ₜ* Multiplicative (ZMod 2) ↦
      f (IdeleGroup.principalIdele F a.1)) hchar
    exact heval.trans hprod
  exact congrArg Multiplicative.toAdd heq

end ClassFieldTower.Martinet.Shafarevich
