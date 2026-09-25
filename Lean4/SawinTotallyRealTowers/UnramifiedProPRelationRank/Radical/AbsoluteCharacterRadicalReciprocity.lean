/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.GlobalReciprocityCharacter
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceAbsoluteArtinCompatibility
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceAdicInertiaTransport
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FinitePlaceReciprocityUnramifiedUnits
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportGlobalReciprocity
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportLocalReciprocityIdeleCharacter
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.EmptySupportKummerCokernel

set_option autoImplicit false
/-!
# Reciprocity annihilates global-character ramification on the ideal radical

An absolute finite character supplies an actual principal-trivial idele
character. Outside a finite support, inertia-triviality kills integral units.
Global reciprocity then proves that the sum of its local pairings on that
support annihilates the ideal-power radical. This is the choice-independence
input for the Shafarevich obstruction functional.
-/

open NumberField IsDedekindDomain
open scoped NumberField Topology BigOperators
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich
open ClassFieldTower.ProP KummerTheory

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime]

local instance absoluteRadicalReciprocityTopology : TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance absoluteRadicalReciprocityDiscrete : DiscreteTopology (ZMod (n : ℕ)) :=
  discreteTopology_bot _
local instance absoluteRadicalReciprocityValuative (v : HeightOneSpectrum (𝓞 F)) :
    ValuativeRel (v.adicCompletion F) := finitePlaceAdicCompletionValuativeRel F v
local instance absoluteRadicalReciprocityLocalField (v : HeightOneSpectrum (𝓞 F)) :
    IsNonarchimedeanLocalField (v.adicCompletion F) :=
  finitePlaceAdicCompletionIsNonarchimedeanLocalField F v
local instance absoluteRadicalReciprocityModule
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod (n : ℕ)) (ContinuousH1ZMod (p := (n : ℕ)) (G := G)) :=
  continuousH1ZModModule

variable (chi : Field.absoluteGaloisGroup F →ₜ* Multiplicative (ZMod (n : ℕ)))

/-- Actual local reciprocity evaluates a restricted absolute character by
the associated global idele character. -/
theorem localReciprocityUnitCharacter_absoluteCharacter
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) :
    localReciprocityUnitCharacter (v.adicCompletion F) (n : ℕ)
      (finitePlaceAbsoluteH1AdicRestriction F (n : ℕ) v (Additive.ofMul chi)) a =
    globalReciprocityIdeleCharacter F (n : ℕ) chi (IdeleGroup.finitePlaceIdele v a) := by
  conv_lhs => rw [← globalReciprocityMaximalAbelianCharacter_comp_restriction F (n : ℕ) chi]
  exact localReciprocityUnitCharacter_globalMaximalAbelian F v (n : ℕ)
    (globalReciprocityMaximalAbelianCharacter F (n : ℕ) chi) a

/-- Killing actual absolute inertia kills the actual adic integral units
under the associated global idele character. -/
theorem globalReciprocityIdeleCharacter_integral_eq_one_of_inertia
    (v : HeightOneSpectrum (𝓞 F))
    (hchi : ∀ sigma : finitePlaceAbsoluteInertiaSubgroup F v,
      chi (finitePlaceAbsoluteDecompositionInclusion F v sigma.1) = 1)
    (a : (v.adicCompletion F)ˣ) (ha : a ∈ (v.adicCompletionIntegers F).units) :
    globalReciprocityIdeleCharacter F (n : ℕ) chi (IdeleGroup.finitePlaceIdele v a) = 1 := by
  rw [← localReciprocityUnitCharacter_absoluteCharacter]
  apply (finitePlaceLocalReciprocityUnitCharacter_integralUnits_iff_unramified
    F n v _).2 ?_ a ha
  change finitePlaceDecompositionH1ToAdic F (n : ℕ) v
    (finitePlaceAbsoluteH1DecompositionRestriction F (n : ℕ) v (Additive.ofMul chi)) ∈ _
  rw [finitePlaceDecompositionH1ToAdic_mem_unramified_iff,
    mem_finitePlaceUnramifiedH1_iff]
  intro sigma
  exact congrArg Multiplicative.toAdd (hchi sigma)

/-- The finite-support reciprocity functional of a global character is zero
on the ideal radical whenever all ramification is contained in the support. -/
theorem absoluteCharacter_finiteSupport_radical_annihilator
    (hpOdd : Odd (n : ℕ)) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (houtside : ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S →
      ∀ sigma : finitePlaceAbsoluteInertiaSubgroup F v,
        chi (finitePlaceAbsoluteDecompositionInclusion F v sigma.1) = 1) :
    absolutePowerClassDualRestriction F (n : ℕ)
      (finiteSupportLocalReciprocityPowerClassFunctional F (n : ℕ) S
        (fun v => finitePlaceAbsoluteH1AdicRestriction F (n : ℕ) v.1 (Additive.ofMul chi))) = 0 := by
  ext x
  change finiteSupportLocalReciprocityPowerClassFunctional F (n : ℕ) S
    (fun v => finitePlaceAbsoluteH1AdicRestriction F (n : ℕ) v.1 (Additive.ofMul chi))
    (idealPowerRadicalToAbsolutePowerClassLinearMap F (n : ℕ) x) = 0
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
  have hx : Additive.ofMul (QuotientGroup.mk a) = x := congrArg Additive.ofMul ha
  rw [← hx]
  let qa : absolutePowerClassModP F (n : ℕ) :=
    Additive.ofMul
      (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Fˣ →* Fˣ).range a.1)
  change finiteSupportLocalReciprocityPowerClassFunctional F (n : ℕ) S
    (fun v => finitePlaceAbsoluteH1AdicRestriction F (n : ℕ) v.1 (Additive.ofMul chi))
    qa = 0
  have hprincipal :
      (finiteSupportLocalReciprocityIdeleCharacter F (n : ℕ) S
        (fun v => finitePlaceAbsoluteH1AdicRestriction F (n : ℕ) v.1 (Additive.ofMul chi))
        (IdeleGroup.principalIdele F a.1)).toAdd =
        finiteSupportLocalReciprocityPowerClassFunctional F (n : ℕ) S
          (fun v => finitePlaceAbsoluteH1AdicRestriction F (n : ℕ) v.1 (Additive.ofMul chi))
          qa :=
    finiteSupportLocalReciprocityIdeleCharacter_principal_functional
      F (n : ℕ) S
        (fun v => finitePlaceAbsoluteH1AdicRestriction F (n : ℕ) v.1 (Additive.ofMul chi))
        a.1
  rw [← hprincipal]
  have hprod := principalTrivialIdeleCharacter_finite_product_radical F n hpOdd S
    (globalReciprocityIdeleCharacter F (n : ℕ) chi)
    (globalReciprocityIdeleCharacter_principal F (n : ℕ) chi)
    (fun v hv a ha => globalReciprocityIdeleCharacter_integral_eq_one_of_inertia
      F n chi v (houtside v hv) a ha) a
  have heq : finiteSupportLocalReciprocityIdeleCharacter F (n : ℕ) S
      (fun v => finitePlaceAbsoluteH1AdicRestriction F (n : ℕ) v.1 (Additive.ofMul chi))
      (IdeleGroup.principalIdele F a.1) = 1 := by
    rw [finiteSupportLocalReciprocityIdeleCharacter_apply]
    convert hprod using 1
    apply Finset.prod_congr rfl
    intro v _
    rw [localReciprocityUnitCharacter_absoluteCharacter]
    rfl
  exact congrArg Multiplicative.toAdd heq

end ClassFieldTower.Martinet.Shafarevich
