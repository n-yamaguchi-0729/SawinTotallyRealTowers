/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdeleIntegralCharacterRadical

set_option autoImplicit false
/-!
# Finite local products of global characters annihilate the radical

Restrict a principal-trivial continuous idele character to finitely many
one-place factors. If the original character kills integral units outside
that set, the quotient of the original and restricted characters kills
every local integral unit. The integral-character radical theorem then
shows that the finite local product is one on every ideal-power radical
representative.

The comparison is built directly from the same idele character on both
sides; no local-global Artin comparison hypothesis is introduced. This is
the reciprocity input for independence of a chosen global lift and for
additivity of the obstruction functional.
-/

open NumberField IsDedekindDomain
open scoped NumberField Topology BigOperators Classical RestrictedProduct
noncomputable section
namespace ClassFieldTower.Martinet.Shafarevich

variable (F : Type) [Field F] [NumberField F]

/-- Inserting a finite-place unit is continuous for the actual restricted-
product idele topology. -/
theorem finitePlaceIdele_continuous (v : HeightOneSpectrum (𝓞 F)) :
    Continuous (IdeleGroup.finitePlaceIdele v) := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v}ᶜ
  have hS : Filter.cofinite ≤ Filter.principal S := by
    rw [Filter.le_principal_iff, Filter.mem_cofinite]
    simpa only [S, compl_compl] using Set.finite_singleton v
  let f : (v.adicCompletion F)ˣ →
      Πʳ w : HeightOneSpectrum (𝓞 F),
        [(w.adicCompletion F)ˣ, (w.adicCompletionIntegers F).units]_[Filter.principal S] :=
    fun x => ⟨fun w => IdeleGroup.finiteComponent w (IdeleGroup.finitePlaceIdele v x), by
      intro w hw
      change IdeleGroup.finiteComponent w (IdeleGroup.finitePlaceIdele v x) ∈
        (w.adicCompletionIntegers F).units
      rw [IdeleGroup.finitePlaceIdele_finiteComponent_of_ne v w x hw]
      exact Subgroup.one_mem _⟩
  have hf : Continuous f := by
    apply RestrictedProduct.continuous_rng_of_principal_iff_forall.2
    intro w
    change Continuous (fun x => IdeleGroup.finiteComponent w (IdeleGroup.finitePlaceIdele v x))
    by_cases hw : w = v
    · subst w
      simp_rw [IdeleGroup.finitePlaceIdele_finiteComponent_same]
      exact continuous_id
    · simp_rw [IdeleGroup.finitePlaceIdele_finiteComponent_of_ne v w _ hw]
      exact continuous_const
  exact continuous_const.prodMk ((RestrictedProduct.continuous_inclusion hS).comp hf)

variable (n : ℕ+) [Fact (n : ℕ).Prime] (hpOdd : Odd (n : ℕ))

local instance finiteRestrictionZModAddCommGroup : AddCommGroup (ZMod (n : ℕ)) :=
  (ZMod.instField (n : ℕ)).toDivisionRing.toAddCommGroup

local instance finiteRestrictionTopology : TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance finiteRestrictionDiscrete : DiscreteTopology (ZMod (n : ℕ)) :=
  discreteTopology_bot _

variable (S : Finset (HeightOneSpectrum (𝓞 F)))
variable (psi : IdeleGroup F →ₜ* Multiplicative (ZMod (n : ℕ)))

/-- The finite product of the given idele character's one-place restrictions. -/
def finiteSupportIdeleRestrictionCharacter :
    IdeleGroup F →ₜ* Multiplicative (ZMod (n : ℕ)) where
  toFun x := ∏ v : ↥S, psi (IdeleGroup.finitePlaceIdele v.1 (IdeleGroup.finiteComponent v.1 x))
  map_one' := by simp only [map_one, Finset.prod_const_one]
  map_mul' x y := by simp only [map_mul, Finset.prod_mul_distrib]
  continuous_toFun := continuous_finsetProd Finset.univ fun v _ =>
    psi.continuous.comp ((finitePlaceIdele_continuous F v.1).comp
      (IdeleGroup.finiteComponentContinuous v.1).continuous)

/-- A one-place restriction is retained exactly when its place is in the set. -/
theorem finiteSupportIdeleRestrictionCharacter_finitePlace
    (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ) :
    finiteSupportIdeleRestrictionCharacter F n S psi (IdeleGroup.finitePlaceIdele v a) =
      if v ∈ S then psi (IdeleGroup.finitePlaceIdele v a) else 1 := by
  by_cases hv : v ∈ S
  · rw [ite_eq_left hv]
    change (∏ w : ↥S, psi (IdeleGroup.finitePlaceIdele w.1
      (IdeleGroup.finiteComponent w.1 (IdeleGroup.finitePlaceIdele v a)))) = _
    rw [Finset.prod_eq_single (⟨v, hv⟩ : ↥S)]
    · rw [IdeleGroup.finitePlaceIdele_finiteComponent_same]
    · intro w _ hw
      rw [IdeleGroup.finitePlaceIdele_finiteComponent_of_ne v w.1 a
        (fun h => hw (Subtype.ext h)), map_one, map_one]
    · intro h
      exact (h (Finset.mem_univ _)).elim
  · rw [ite_eq_right hv]
    apply Finset.prod_eq_one
    intro w _
    rw [IdeleGroup.finitePlaceIdele_finiteComponent_of_ne v w.1 a
      (fun h => hv (h ▸ w.2)), map_one, map_one]

include hpOdd

/-- Principal triviality and unramifiedness outside the finite set force
the restricted character to annihilate principal radical representatives. -/
theorem finiteSupportIdeleRestrictionCharacter_principal_radical
    (hprincipal : ∀ a : Fˣ, psi (IdeleGroup.principalIdele F a) = 1)
    (houtside : ∀ (v : HeightOneSpectrum (𝓞 F)), v ∉ S →
      ∀ a : (v.adicCompletion F)ˣ, a ∈ (v.adicCompletionIntegers F).units →
        psi (IdeleGroup.finitePlaceIdele v a) = 1)
    (a : (idealNthPowerRadicalKummerSubgroup F n).1) :
    finiteSupportIdeleRestrictionCharacter F n S psi
      (IdeleGroup.principalIdele F a.1) = 1 := by
  let d := psi / finiteSupportIdeleRestrictionCharacter F n S psi
  have hd : ∀ (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletion F)ˣ),
      u ∈ (v.adicCompletionIntegers F).units → d (IdeleGroup.finitePlaceIdele v u) = 1 := by
    intro v u hu
    change psi (IdeleGroup.finitePlaceIdele v u) /
      finiteSupportIdeleRestrictionCharacter F n S psi (IdeleGroup.finitePlaceIdele v u) = 1
    rw [finiteSupportIdeleRestrictionCharacter_finitePlace]
    by_cases hv : v ∈ S
    · rw [ite_eq_left hv, div_self']
    · rw [ite_eq_right hv, houtside v hv u hu, div_one]
  have h := ideleCharacter_principal_radical_eq_one_of_integral_local F n hpOdd d hd a
  change psi (IdeleGroup.principalIdele F a.1) /
    finiteSupportIdeleRestrictionCharacter F n S psi (IdeleGroup.principalIdele F a.1) = 1 at h
  exact (div_eq_one.mp h).symm.trans (hprincipal a.1)

/-- The finite local evaluation product of a principal-trivial character
is one on the ideal-power radical when it is unramified outside that set. -/
theorem principalTrivialIdeleCharacter_finite_product_radical
    (hprincipal : ∀ a : Fˣ, psi (IdeleGroup.principalIdele F a) = 1)
    (houtside : ∀ (v : HeightOneSpectrum (𝓞 F)), v ∉ S →
      ∀ a : (v.adicCompletion F)ˣ, a ∈ (v.adicCompletionIntegers F).units →
        psi (IdeleGroup.finitePlaceIdele v a) = 1)
    (a : (idealNthPowerRadicalKummerSubgroup F n).1) :
    (∏ v : ↥S, psi (IdeleGroup.finitePlaceIdele v.1
      (Units.map (algebraMap F (v.1.adicCompletion F)).toMonoidHom a.1))) = 1 :=
  finiteSupportIdeleRestrictionCharacter_principal_radical F n hpOdd S psi hprincipal houtside a

end ClassFieldTower.Martinet.Shafarevich
