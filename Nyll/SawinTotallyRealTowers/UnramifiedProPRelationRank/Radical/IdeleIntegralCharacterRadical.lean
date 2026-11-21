/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Topology.Instances.ZMod
public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadical
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.ArchimedeanPowerIndex
public import Mathlib.Topology.Algebra.InfiniteSum.Constructions
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.IdealMap
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.Basic

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

@[expose] public section

open NumberField IsDedekindDomain
open scoped NumberField Topology BigOperators
noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

variable (F : Type) [Field F] [NumberField F]
variable (n : ℕ+) [Fact (n : ℕ).Prime] (hpOdd : Odd (n : ℕ))


/-- Every multiplicative mod-p coefficient has p-th power one. -/
theorem multiplicativeZMod_pow_eq_one (a : Multiplicative (ZMod (n : ℕ))) :
    a ^ (n : ℕ) = 1 := by
  apply Multiplicative.toAdd.injective
  change (n : ℕ) • a.toAdd = 0
  rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]

/-- The actual product of finite integral units, with archimedean part one. -/
def integralFiniteIdeleContinuousHom :
    (∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F).units) →ₜ* IdeleGroup F where
  toFun a := IdeleGroup.ofComponents 1 (FiniteIdeleGroup.integralStructureMap a)
  map_one' := by
    change IdeleGroup.ofComponents 1 1 = 1
    exact IdeleGroup.ofComponents_one
  map_mul' a b := by
    apply IdeleGroup.ext_parts
    · simp only [map_mul, IdeleGroup.infinitePart_ofComponents, mul_one]
    · simp only [map_mul, IdeleGroup.finiteCoordinates_ofComponents]
      rfl
  continuous_toFun := IdeleGroup.continuous_ofComponents.comp
    (continuous_const.prodMk RestrictedProduct.isEmbedding_structureMap.continuous)

/-- An integral idèle splits as its infinite part and its actual finite integral units. -/
theorem integralFiniteIdeleContinuousHom_split
    (a : IdeleGroup F) (ha : a ∈ IdeleGroup.integralAtFinitePlaces (K := F)) :
    a = IdeleGroup.ofComponents (IdeleGroup.infinitePart a) 1 *
      integralFiniteIdeleContinuousHom F (fun v => ⟨IdeleGroup.finiteCoordinates a v, ha v⟩) := by
  have hFinite : FiniteIdeleGroup.integralStructureMap
      (fun v => ⟨IdeleGroup.finiteCoordinates a v, ha v⟩) = IdeleGroup.finiteCoordinates a := by
    apply RestrictedProduct.ext
    intro v
    rfl
  change a = IdeleGroup.ofComponents (IdeleGroup.infinitePart a) 1 *
    IdeleGroup.ofComponents 1 (FiniteIdeleGroup.integralStructureMap _)
  rw [hFinite]
  exact IdeleGroup.eq_ofComponents_mul a

/-- Pointwise triviality on integral units implies triviality on their product. -/
theorem ideleCharacter_integralFinite_eq_one
    (chi : IdeleGroup F →ₜ* Multiplicative (ZMod (n : ℕ)))
    (hchi : ∀ (v : HeightOneSpectrum (𝓞 F)) (a : (v.adicCompletion F)ˣ),
      a ∈ (v.adicCompletionIntegers F).units → chi (IdeleGroup.finitePlaceIdele v a) = 1)
    (a : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F).units) :
    chi (integralFiniteIdeleContinuousHom F a) = 1 := by
  classical
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
      apply IdeleGroup.ext_parts
      · apply ContinuousMulEquiv.piUnits.injective
        funext w
        change IdeleGroup.infiniteComponent w
            (IdeleGroup.ofComponents 1
              (FiniteIdeleGroup.integralStructureMap (Pi.mulSingle v (a v)))) =
          IdeleGroup.infiniteComponent w (IdeleGroup.finitePlaceIdele v (a v).1)
        rw [IdeleGroup.finitePlaceIdele_infiniteComponent, IdeleGroup.infiniteComponent_apply,
          IdeleGroup.infinitePart_ofComponents, map_one, Pi.one_apply]
      apply RestrictedProduct.ext
      intro w
      change ((Pi.mulSingle v (a v) :
        ∀ w : HeightOneSpectrum (𝓞 F), (w.adicCompletionIntegers F).units) w).1 =
        IdeleGroup.finiteCoordinates (IdeleGroup.finitePlaceIdele v (a v).1) w
      rw [← IdeleGroup.finiteComponent_apply]
      by_cases h : w = v
      · subst w
        rw [Pi.mulSingle_eq_same, IdeleGroup.finitePlaceIdele_finiteComponent_same]
      · rw [Pi.mulSingle_eq_of_ne h, IdeleGroup.finitePlaceIdele_finiteComponent_of_ne v w _ h]
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
  classical
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
  obtain ⟨b, hb⟩ := infiniteIdele_pow_surjective_of_odd F n hpOdd (IdeleGroup.infinitePart a)
  have hinf : chi (IdeleGroup.ofComponents (IdeleGroup.infinitePart a) 1) = 1 := by
    rw [← hb]
    have hp : IdeleGroup.ofComponents (b ^ (n : ℕ)) 1 =
        (IdeleGroup.ofComponents b 1) ^ (n : ℕ) := by
      apply IdeleGroup.ext_parts <;> simp only [map_pow, IdeleGroup.infinitePart_ofComponents,
        IdeleGroup.finiteCoordinates_ofComponents, one_pow]
    rw [hp, map_pow, multiplicativeZMod_pow_eq_one]
  let u : ∀ v : HeightOneSpectrum (𝓞 F), (v.adicCompletionIntegers F).units :=
    fun v => ⟨IdeleGroup.finiteCoordinates a v, ha v⟩
  have hfin := ideleCharacter_integralFinite_eq_one F n chi hchi u
  have hsplit := integralFiniteIdeleContinuousHom_split F a ha
  change a = IdeleGroup.ofComponents (IdeleGroup.infinitePart a) 1 *
    integralFiniteIdeleContinuousHom F u at hsplit
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
  rw [map_div, map_pow, multiplicativeZMod_pow_eq_one] at h
  exact (div_one _).symm.trans h

end ClassFieldTower.Martinet.Shafarevich
