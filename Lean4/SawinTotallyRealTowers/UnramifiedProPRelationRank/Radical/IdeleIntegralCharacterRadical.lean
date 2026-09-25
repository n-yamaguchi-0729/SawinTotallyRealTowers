/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadical
import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
import ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.ArchimedeanPowerIndex
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

set_option autoImplicit false
/-!
# Integral idele characters annihilate the ideal-power radical

A continuous character trivial on each finite integral one-place idele
is trivial on their entire product, by convergence of the finite partial
products. Odd powers are surjective on the archimedean factors. Thus an
odd mod-p character with these local triviality conditions kills the
whole integral-idele subgroup.

The fractional-ideal map is surjective and has this integral subgroup as
kernel. Lifting the ideal root of a radical element therefore writes its
principal idele as a p-th power times an integral idele. The character
annihilates it. No global reciprocity comparison is an extra hypothesis.
-/

open NumberField IsDedekindDomain
open scoped NumberField Topology BigOperators Classical
noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime] (hpOdd : Odd (n : ℕ))

local instance integralCharacterTopology : TopologicalSpace (ZMod (n : ℕ)) := ⊥
local instance integralCharacterDiscrete : DiscreteTopology (ZMod (n : ℕ)) :=
  discreteTopology_bot _

/-- Every multiplicative mod-p coefficient has p-th power one. -/
theorem multiplicativeZMod_pow_eq_one (a : Multiplicative (ZMod (n : ℕ))) :
    a ^ (n : ℕ) = 1 := by
  apply Multiplicative.toAdd.injective
  change (n : ℕ) • a.toAdd = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- The actual product of finite integral units, with archimedean part one. -/
def integralFiniteIdeleContinuousHom :
    (∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F).units) →ₜ* IdeleGroup F where
  toFun a := (1, FiniteIdeleGroup.integralStructureMap a)
  map_one' := rfl
  map_mul' a b := by
    apply Prod.ext
    · exact (one_mul 1).symm
    · rfl
  continuous_toFun := continuous_const.prodMk
    RestrictedProduct.isEmbedding_structureMap.continuous

/-- Pointwise triviality on integral units implies triviality on their product. -/
theorem ideleCharacter_integralFinite_eq_one
    (chi : IdeleGroup F →ₜ* Multiplicative (ZMod (n : ℕ)))
    (hchi : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ),
      a ∈ (v.adicCompletionIntegers F).units → chi (IdeleGroup.finitePlaceIdele v a) = 1)
    (a : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F).units) :
    chi (integralFiniteIdeleContinuousHom F a) = 1 := by
  have ha : HasProd (fun v => Pi.mulSingle v (a v)) a := by
    apply Pi.hasProd.2
    intro w
    have hw : (fun v => (Pi.mulSingle v (a v) :
        ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletionIntegers F).units) w) =
        (Pi.mulSingle w (a w) : HeightOneSpectrum (𝓞 F) →
          (w.adicCompletionIntegers F).units) := by
      funext v
      by_cases h : v = w
      · subst v
        simp only [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne (Ne.symm h), Pi.mulSingle_eq_of_ne h]
    rw [hw]
    exact hasProd_pi_single w (a w)
  let f := chi.comp (integralFiniteIdeleContinuousHom F)
  have hf := ha.map f.toMonoidHom f.continuous
  have hf1 : ∀ v, f (Pi.mulSingle v (a v)) = 1 := by
    intro v
    have he : integralFiniteIdeleContinuousHom F (Pi.mulSingle v (a v)) =
        IdeleGroup.finitePlaceIdele v (a v).1 := by
      apply Prod.ext
      · rfl
      apply Subtype.ext
      funext w
      change ((Pi.mulSingle v (a v) :
        ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletionIntegers F).units) w).1 =
        (Pi.mulSingle v (a v).1 :
          ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletion F)ˣ) w
      by_cases h : w = v
      · subst w
        simp only [Pi.mulSingle_eq_same]
      · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h]
        rfl
    change chi (integralFiniteIdeleContinuousHom F _) = 1
    rw [he]
    exact hchi v (a v).1 (a v).2
  change HasProd (fun v => f (Pi.mulSingle v (a v))) (f a) at hf
  simp only [hf1] at hf
  exact hf.unique hasProd_one

include hpOdd

omit [NumberField F] [Fact (n : ℕ).Prime] in
/-- Odd powers are surjective on all archimedean idele factors. -/
theorem infiniteIdele_pow_surjective_of_odd :
    Function.Surjective (fun a : InfiniteIdeleGroup F => a ^ (n : ℕ)) := by
  intro a
  let e : InfiniteIdeleGroup F ≃ₜ* (∀ w : InfinitePlace F, w.Completionˣ) :=
    ContinuousMulEquiv.piUnits
  have hroot : ∀ w : InfinitePlace F, ∃ b : w.Completionˣ, b ^ (n : ℕ) = e a w := by
    intro w
    by_cases hw : w.IsReal
    · have hmem : e a w ∈ (powMonoidHom (n : ℕ) : w.Completionˣ →* w.Completionˣ).range := by
        rw [GlobalClassFieldTheory.ClassFieldAxiom.nthPowerSubgroup_eq_top_of_real_odd n w hw hpOdd]
        exact Subgroup.mem_top _
      exact hmem
    · apply exists_infinitePositiveSubgroup_nthRoot w (n : ℕ) n.pos
      rw [RayClass.mem_infinitePositiveSubgroup_iff]
      intro hreal
      exact (hw hreal).elim
  choose b hb using hroot
  refine ⟨e.symm b, ?_⟩
  apply e.injective
  rw [map_pow, e.apply_symm_apply]
  exact funext hb

/-- An odd mod-p character trivial on local integral units kills integral ideles. -/
theorem ideleCharacter_integral_eq_one
    (chi : IdeleGroup F →ₜ* Multiplicative (ZMod (n : ℕ)))
    (hchi : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ),
      a ∈ (v.adicCompletionIntegers F).units → chi (IdeleGroup.finitePlaceIdele v a) = 1)
    (a : IdeleGroup F) (ha : a ∈ IdeleGroup.integralAtFinitePlaces (K := F)) :
    chi a = 1 := by
  obtain ⟨b, hb⟩ := infiniteIdele_pow_surjective_of_odd F n hpOdd a.1
  have hinf : chi (a.1, 1) = 1 := by
    rw [← hb]
    have hp : (b ^ (n : ℕ), (1 : FiniteIdeleGroup F)) = (b, 1) ^ (n : ℕ) := by simp
    rw [hp, map_pow, multiplicativeZMod_pow_eq_one]
  let u : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F).units :=
    fun v => ⟨a.2 v, ha v⟩
  have hfin := ideleCharacter_integralFinite_eq_one F n chi hchi u
  have hsplit : a = (a.1, 1) * integralFiniteIdeleContinuousHom F u := by
    apply Prod.ext
    · exact (mul_one _).symm
    · exact (one_mul _).symm
  rw [hsplit, map_mul, hinf, hfin, one_mul]

/-- Such a character kills principal ideles of ideal-power radical elements. -/
theorem ideleCharacter_principal_radical_eq_one_of_integral_local
    (chi : IdeleGroup F →ₜ* Multiplicative (ZMod (n : ℕ)))
    (hchi : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ),
      a ∈ (v.adicCompletionIntegers F).units → chi (IdeleGroup.finitePlaceIdele v a) = 1)
    (a : (idealNthPowerRadicalKummerSubgroup F n).1) :
    chi (IdeleGroup.principalIdele F a.1) = 1 := by
  obtain ⟨b, hb⟩ := IdeleGroup.fractionalIdeal_surjective (K := F)
    (idealNthRoot F n a)
  have hint : IdeleGroup.principalIdele F a.1 / b ^ (n : ℕ) ∈
      IdeleGroup.integralAtFinitePlaces (K := F) := by
    rw [← IdeleGroup.fractionalIdeal_ker, MonoidHom.mem_ker, map_div, map_pow,
      IdeleGroup.fractionalIdeal_principalIdele, hb, idealNthRoot_pow, div_self']
  have h := ideleCharacter_integral_eq_one F n hpOdd chi hchi _ hint
  rw [map_div, map_pow, multiplicativeZMod_pow_eq_one, div_one] at h
  exact h

end ClassFieldTower.Martinet.Shafarevich
