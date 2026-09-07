import SawinTotallyRealTowers.NegativeThreeCharacter
import SawinTotallyRealTowers.InfiniteArtinCompatibility
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.GlobalReciprocityCharacter
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.AbsoluteCharacterRadicalReciprocity
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.FiniteSupportGlobalReciprocity
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdeleIntegralCharacterRadical
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
import ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
import ClassFieldTheory.AlgebraicNumberTheory.Idele.NormOneCompact
import ClassFieldTheory.AlgebraicNumberTheory.Idele.SinglePlace
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.Normed.Ring.WithAbs
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.Topology.Algebra.GroupCompletion
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.ZMod

set_option autoImplicit false

/-!
# The local value at three of the negative-three character

Global reciprocity applied to the principal idele of negative one identifies
its local value at three with its nontrivial real sign. All other finite
components disappear by the proved unramifiedness of the actual quadratic
character. No Hilbert-symbol or norm-pairing comparison is assumed.
-/

open NumberField IsDedekindDomain
open scoped NumberField Classical

noncomputable section

namespace ClassFieldTower.Sawin
open ClassFieldTower.Martinet.Shafarevich

/-- The character of the actual field ℚ(√−3), evaluated through global
reciprocity on the three-adic unit −1, is nontrivial. -/
theorem negativeThreeCharacter_three_neg_one_ne_one :
    globalReciprocityIdeleCharacter ℚ 2 negativeThreeCharacter
      (IdeleGroup.finitePlaceIdele
        ((Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
          (⟨3, Nat.prime_three⟩ : Nat.Primes)) (-1)) ≠ 1 := by
  let v₃ : HeightOneSpectrum (𝓞 ℚ) :=
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm
      (⟨3, Nat.prime_three⟩ : Nat.Primes)
  let ψ := globalReciprocityIdeleCharacter ℚ 2 negativeThreeCharacter
  let S : Finset (HeightOneSpectrum (𝓞 ℚ)) := {v₃}
  let r : IdeleGroup ℚ →ₜ* Multiplicative (ZMod 2) :=
    finiteSupportIdeleRestrictionCharacter ℚ (2 : ℕ+) S ψ
  let δ : IdeleGroup ℚ →ₜ* Multiplicative (ZMod 2) := ψ / r
  have hfinite : ∀ (v : HeightOneSpectrum (𝓞 ℚ)) (a : (v.adicCompletion ℚ)ˣ),
      a ∈ (v.adicCompletionIntegers ℚ).units →
        δ (IdeleGroup.finitePlaceIdele v a) = 1 := by
    intro v a ha
    change ψ (IdeleGroup.finitePlaceIdele v a) /
      r (IdeleGroup.finitePlaceIdele v a) = 1
    rw [show r (IdeleGroup.finitePlaceIdele v a) =
      if v ∈ S then ψ (IdeleGroup.finitePlaceIdele v a) else 1 from
        finiteSupportIdeleRestrictionCharacter_finitePlace ℚ (2 : ℕ+) S ψ v a]
    by_cases hv : v ∈ S
    · rw [if_pos hv, div_self']
    · rw [if_neg hv, div_one]
      apply globalReciprocityIdeleCharacter_integral_eq_one_of_inertia
        ℚ (2 : ℕ+) negativeThreeCharacter v _ a ha
      intro σ
      exact negativeThreeCharacter_inertia v
        (fun h => hv (Finset.mem_singleton.mpr h)) σ
  let P : IdeleGroup ℚ := IdeleGroup.principalIdele ℚ (-1)
  have hIntegral : P ∈ IdeleGroup.integralAtFinitePlaces (K := ℚ) := by
    have h := IdeleGroup.principalRingUnit_mem_integralAtFinitePlaces
      (K := ℚ) (-1 : (𝓞 ℚ)ˣ)
    have he : InfiniteIdeleGroup.ringUnitToFieldUnit (K := ℚ)
        (-1 : (𝓞 ℚ)ˣ) = (-1 : ℚˣ) := by
      apply Units.ext
      change algebraMap (𝓞 ℚ) ℚ (-1) = -1
      rw [map_neg, map_one]
    rw [he] at h
    exact h
  let u : ∀ v : HeightOneSpectrum (𝓞 ℚ), (v.adicCompletionIntegers ℚ).units :=
    fun v => ⟨P.2 v, hIntegral v⟩
  have hFiniteP : δ (integralFiniteIdeleContinuousHom ℚ u) = 1 :=
    ideleCharacter_integralFinite_eq_one ℚ (2 : ℕ+) δ hfinite u
  have hSplit : P = IdeleGroup.infinitePlaceIdele Rat.infinitePlace (-1) *
      integralFiniteIdeleContinuousHom ℚ u := by
    apply Prod.ext
    · apply ContinuousMulEquiv.piUnits.injective
      funext v
      rw [Subsingleton.elim v Rat.infinitePlace]
      change IdeleGroup.infiniteComponent Rat.infinitePlace P =
        IdeleGroup.infiniteComponent Rat.infinitePlace
          (IdeleGroup.infinitePlaceIdele Rat.infinitePlace (-1)) * 1
      rw [IdeleGroup.infinitePlaceIdele_infiniteComponent_same, mul_one]
      apply Units.ext
      change ((IdeleGroup.infiniteComponent Rat.infinitePlace
        (IdeleGroup.principalIdele ℚ (-1 : ℚˣ))) : Rat.infinitePlace.Completion) = -1
      rw [IdeleGroup.infiniteComponent_principalIdele]
      apply InfinitePlace.Completion.ext
      change ((WithAbs.toAbs Rat.infinitePlace.1
        (-1 : ℚ)) : Rat.infinitePlace.1.Completion) = -1
      rw [WithAbs.toAbs_neg, WithAbs.toAbs_one,
        UniformSpace.Completion.coe_neg, UniformSpace.Completion.coe_one]
    · exact (one_mul P.2).symm
  have hrInfinite : r (IdeleGroup.infinitePlaceIdele Rat.infinitePlace (-1)) = 1 := by
    change (∏ v : ↥S, ψ (IdeleGroup.finitePlaceIdele v.1
      (IdeleGroup.finiteComponent v.1
        (IdeleGroup.infinitePlaceIdele Rat.infinitePlace (-1))))) = 1
    apply Finset.prod_eq_one
    intro v hv
    rw [IdeleGroup.infinitePlaceIdele_finiteComponent, map_one, map_one]
  have hrP : r P = ψ (IdeleGroup.finitePlaceIdele v₃ (-1)) := by
    change (∏ v : ↥({v₃} : Finset (HeightOneSpectrum (𝓞 ℚ))),
      ψ (IdeleGroup.finitePlaceIdele v.1 (IdeleGroup.finiteComponent v.1 P))) = _
    rw [Fintype.prod_subsingleton _ (⟨v₃, Finset.mem_singleton_self v₃⟩ :
      ↥({v₃} : Finset (HeightOneSpectrum (𝓞 ℚ))))]
    have he : IdeleGroup.finiteComponent v₃ P = (-1 : (v₃.adicCompletion ℚ)ˣ) := by
      apply Units.ext
      rw [IdeleGroup.finiteComponent_principalIdele]
      let f : ℚ →+* v₃.adicCompletion ℚ :=
        (HeightOneSpectrum.adicCompletion.equiv ℚ v₃).symm.toRingHom.comp
          (UniformSpace.Completion.coeRingHom.comp
            (WithVal.equiv (v₃.valuation ℚ)).symm.toRingHom)
      change f (-1) = -1
      rw [map_neg, map_one]
    rw [he]
  intro hLocal
  have hP : δ P = 1 := by
    change ψ P / r P = 1
    rw [hrP, hLocal]
    exact div_one _ |>.trans
      (globalReciprocityIdeleCharacter_principal ℚ 2 negativeThreeCharacter (-1))
  rw [hSplit, map_mul, hFiniteP, mul_one] at hP
  change ψ (IdeleGroup.infinitePlaceIdele Rat.infinitePlace (-1)) /
    r (IdeleGroup.infinitePlaceIdele Rat.infinitePlace (-1)) = 1 at hP
  rw [hrInfinite, div_one] at hP
  exact negativeThreeCharacter_infinite Rat.infinitePlace
    ((globalReciprocityIdeleCharacter_infinite_neg_one
      ℚ 2 negativeThreeCharacter Rat.infinitePlace).symm.trans hP)

end ClassFieldTower.Sawin
