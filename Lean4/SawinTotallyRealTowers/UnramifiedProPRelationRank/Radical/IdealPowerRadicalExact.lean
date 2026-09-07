import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.IdealPowerRadical
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Radical.OrdinaryUnitModP
import ClassFieldTheory.AlgebraicNumberTheory.RayClass.Narrow
import Mathlib.RingTheory.DedekindDomain.SelmerGroup

set_option autoImplicit false
/-!
# The exact unit--radical--class sequence

This file supplies the missing maps in the empty-support Selmer sequence:
ordinary units modulo powers inject into the ideal-power radical, whose
ideal-root class map surjects onto class-group power torsion.
-/

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type*) [Field K] [NumberField K]

/-- Ordinary integral units regarded as elements of the ideal-power radical. -/
noncomputable def integralUnitToIdealNthPowerRadical
    (n : ℕ+) :
    (𝓞 K)ˣ →* (idealNthPowerRadicalKummerSubgroup K n).1 where
  toFun u := ⟨RayClass.integralUnitToFieldUnit u, by
    change toPrincipalIdeal (𝓞 K) K
        (RayClass.integralUnitToFieldUnit u) ∈
      (powMonoidHom (n : ℕ) : FractionalIdealGroup K →*
        FractionalIdealGroup K).range
    refine ⟨1, ?_⟩
    rw [powMonoidHom_apply, one_pow]
    exact ((RayClass.toPrincipalIdeal_eq_one_iff_mem_integralUnits _).2
      ⟨u, rfl⟩).symm⟩
  map_one' := by
    apply Subtype.ext
    exact map_one (RayClass.integralUnitToFieldUnit (K := K))
  map_mul' u v := by
    apply Subtype.ext
    exact map_mul (RayClass.integralUnitToFieldUnit (K := K)) u v

/-- The raw map from integral units to the radical quotient. -/
noncomputable def integralUnitToIdealNthPowerRadicalQuotient
    (n : ℕ+) :
    (𝓞 K)ˣ →* IdealNthPowerRadicalQuotient K n :=
  (restrictedRadicalQuotientMk n
    (idealNthPowerRadicalKummerSubgroup K n)).comp
      (integralUnitToIdealNthPowerRadical K n)

private theorem integralUnitToIdealNthPowerRadicalQuotient_ker
    (n : ℕ+) :
    MonoidHom.ker (integralUnitToIdealNthPowerRadicalQuotient K n) =
      (powMonoidHom (n : ℕ) : (𝓞 K)ˣ →* (𝓞 K)ˣ).range := by
  let _ : Fact (0 < (n : ℕ)) := ⟨n.pos⟩
  ext u
  constructor
  · intro hu
    rw [MonoidHom.mem_ker] at hu
    have hrestricted :=
      (restrictedRadicalQuotientMk_eq_one_iff n
        (idealNthPowerRadicalKummerSubgroup K n)
        (integralUnitToIdealNthPowerRadical K n u)).mp hu
    obtain ⟨b, hb⟩ :=
      (mem_restrictedNthPowersSubgroup_iff n
        (idealNthPowerRadicalKummerSubgroup K n)).mp hrestricted
    have hselmer :
        IsDedekindDomain.selmerGroup.fromUnit
            (R := 𝓞 K) (K := K) (n := (n : ℕ)) u = 1 := by
      apply Subtype.ext
      apply (QuotientGroup.eq_one_iff _).2
      exact ⟨b, hb⟩
    have hker : u ∈ MonoidHom.ker
        (IsDedekindDomain.selmerGroup.fromUnit
          (R := 𝓞 K) (K := K) (n := (n : ℕ))) := hselmer
    rw [IsDedekindDomain.selmerGroup.fromUnit_ker] at hker
    exact hker
  · intro hu
    rw [MonoidHom.mem_ker]
    apply (restrictedRadicalQuotientMk_eq_one_iff n
      (idealNthPowerRadicalKummerSubgroup K n)
      (integralUnitToIdealNthPowerRadical K n u)).2
    apply (mem_restrictedNthPowersSubgroup_iff n
      (idealNthPowerRadicalKummerSubgroup K n)).2
    obtain ⟨v, hv⟩ := hu
    refine ⟨RayClass.integralUnitToFieldUnit v, ?_⟩
    change (RayClass.integralUnitToFieldUnit v) ^ (n : ℕ) =
      RayClass.integralUnitToFieldUnit u
    rw [← map_pow]
    exact congrArg (RayClass.integralUnitToFieldUnit (K := K))
      (by simpa only [powMonoidHom_apply] using hv)

/-- The injection of ordinary units modulo `n`-th powers into the
Shafarevich radical. -/
noncomputable def ordinaryUnitNthPowerQuotientToIdealRadical
    (n : ℕ+) :
    OrdinaryUnitNthPowerQuotient K (n : ℕ) →*
      IdealNthPowerRadicalQuotient K n :=
  (QuotientGroup.kerLift
      (integralUnitToIdealNthPowerRadicalQuotient K n)).comp
    (QuotientGroup.quotientMulEquivOfEq
      (integralUnitToIdealNthPowerRadicalQuotient_ker K n)).symm.toMonoidHom

theorem ordinaryUnitNthPowerQuotientToIdealRadical_injective
    (n : ℕ+) :
    Function.Injective
      (ordinaryUnitNthPowerQuotientToIdealRadical K n) := by
  dsimp only [ordinaryUnitNthPowerQuotientToIdealRadical,
    MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact Function.Injective.comp
    (QuotientGroup.kerLift_injective _)
    (MulEquiv.injective _)

@[simp]
theorem ordinaryUnitNthPowerQuotientToIdealRadical_mk
    (n : ℕ+) (u : (𝓞 K)ˣ) :
    ordinaryUnitNthPowerQuotientToIdealRadical K n
        (QuotientGroup.mk'
          (powMonoidHom (n : ℕ) : (𝓞 K)ˣ →* (𝓞 K)ˣ).range u) =
      restrictedRadicalQuotientMk n
        (idealNthPowerRadicalKummerSubgroup K n)
        (integralUnitToIdealNthPowerRadical K n u) := by
  rfl

/-- The ordinary-unit injection and ideal-root class map are exact. -/
theorem range_ordinaryUnitToIdealRadical_eq_ker_toClassTorsion
    (n : ℕ+) :
    MonoidHom.range (ordinaryUnitNthPowerQuotientToIdealRadical K n) =
      MonoidHom.ker (idealNthPowerRadicalToClassTorsion K n) := by
  ext q
  constructor
  · rintro ⟨u, rfl⟩
    rw [MonoidHom.mem_ker]
    induction u using QuotientGroup.induction_on' with
    | _ u =>
        change idealNthPowerRadicalToClassTorsion K n
          (ordinaryUnitNthPowerQuotientToIdealRadical K n
            (QuotientGroup.mk'
              (powMonoidHom (n : ℕ) : (𝓞 K)ˣ →* (𝓞 K)ˣ).range u)) = 1
        rw [ordinaryUnitNthPowerQuotientToIdealRadical_mk,
          idealNthPowerRadicalToClassTorsion_mk]
        apply Subtype.ext
        change ClassGroup.mk K
          (idealNthRoot K n
            (integralUnitToIdealNthPowerRadical K n u)) = 1
        rw [idealNthRoot_eq_of_pow_eq K n
          (integralUnitToIdealNthPowerRadical K n u) 1]
        · simp
        · rw [one_pow]
          exact ((RayClass.toPrincipalIdeal_eq_one_iff_mem_integralUnits _).2
            ⟨u, rfl⟩).symm
  · intro hq
    revert hq
    refine restrictedRadicalQuotient_inductionOn n
      (idealNthPowerRadicalKummerSubgroup K n)
      (motive := fun r ↦
        r ∈ MonoidHom.ker (idealNthPowerRadicalToClassTorsion K n) →
          r ∈ MonoidHom.range
            (ordinaryUnitNthPowerQuotientToIdealRadical K n)) q ?_
    intro a hq
    rw [MonoidHom.mem_ker,
      idealNthPowerRadicalToClassTorsion_mk] at hq
    have hclass : ClassGroup.mk K (idealNthRoot K n a) = 1 :=
      congrArg Subtype.val hq
    obtain ⟨b, hb⟩ :=
      (IdeleGroup.classGroup_mk_eq_one_iff
        (idealNthRoot K n a)).mp hclass
    have hx :
        toPrincipalIdeal (𝓞 K) K (a.1 / b ^ (n : ℕ)) = 1 := by
      rw [map_div, map_pow, hb, ← idealNthRoot_pow K n a]
      simp
    obtain ⟨u, hu⟩ :=
      (RayClass.toPrincipalIdeal_eq_one_iff_mem_integralUnits
        (a.1 / b ^ (n : ℕ))).mp hx
    refine ⟨QuotientGroup.mk'
        (powMonoidHom (n : ℕ) : (𝓞 K)ˣ →* (𝓞 K)ˣ).range u, ?_⟩
    rw [ordinaryUnitNthPowerQuotientToIdealRadical_mk]
    apply (restrictedRadicalQuotientMk_eq_iff n
      (idealNthPowerRadicalKummerSubgroup K n)
      (integralUnitToIdealNthPowerRadical K n u) a).2
    apply (mem_restrictedNthPowersSubgroup_iff n
      (idealNthPowerRadicalKummerSubgroup K n)).2
    refine ⟨b⁻¹, ?_⟩
    change (b⁻¹) ^ (n : ℕ) =
      RayClass.integralUnitToFieldUnit u / a.1
    rw [hu]
    simp [div_eq_mul_inv, mul_comm]

/-- The empty-support ideal-power radical quotient is finite. -/
noncomputable instance finite_idealNthPowerRadicalQuotient
    (n : ℕ+) :
    Finite (IdealNthPowerRadicalQuotient K n) := by
  let f := ordinaryUnitNthPowerQuotientToIdealRadical K n
  let g := idealNthPowerRadicalToClassTorsion K n
  let _ : Finite (OrdinaryUnitNthPowerQuotient K (n : ℕ)) :=
    finite_ordinaryUnitNthPowerQuotient K n
  let _ : Finite f.range :=
    Finite.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have hexact : f.range = g.ker :=
    range_ordinaryUnitToIdealRadical_eq_ker_toClassTorsion K n
  let _ : Finite g.ker := by
    rw [← hexact]
    infer_instance
  let _ : Finite
      (IdealNthPowerRadicalQuotient K n ⧸ g.ker) :=
    Finite.of_equiv (ClassGroupNthPowerTorsion K (n : ℕ))
      (QuotientGroup.quotientKerEquivOfSurjective g
        (idealNthPowerRadicalToClassTorsion_surjective K n)).symm.toEquiv
  exact Finite.of_subgroup_quotient g.ker

/-- The exact sequence computes the radical cardinality as the product of
the ordinary-unit quotient and the `n`-class quotient cardinalities. -/
theorem card_idealNthPowerRadicalQuotient
    (n : ℕ+) :
    Nat.card (IdealNthPowerRadicalQuotient K n) =
      Nat.card (OrdinaryUnitNthPowerQuotient K (n : ℕ)) *
        Nat.card (ClassFieldTower.Martinet.PClassGroup K (n : ℕ)) := by
  let f := ordinaryUnitNthPowerQuotientToIdealRadical K n
  let g := idealNthPowerRadicalToClassTorsion K n
  let _ : Finite (OrdinaryUnitNthPowerQuotient K (n : ℕ)) :=
    finite_ordinaryUnitNthPowerQuotient K n
  let eUnit : OrdinaryUnitNthPowerQuotient K (n : ℕ) ≃* f.range :=
    MulEquiv.ofBijective f.rangeRestrict
      ⟨fun x y h ↦ ordinaryUnitNthPowerQuotientToIdealRadical_injective
          K n (congrArg Subtype.val h),
        f.rangeRestrict_surjective⟩
  have hexact : f.range = g.ker :=
    range_ordinaryUnitToIdealRadical_eq_ker_toClassTorsion K n
  have hsurjective : Function.Surjective g :=
    idealNthPowerRadicalToClassTorsion_surjective K n
  calc
    Nat.card (IdealNthPowerRadicalQuotient K n) =
        Nat.card g.ker * Nat.card g.range := by
      rw [← g.ker.card_mul_index, Subgroup.index_ker]
    _ = Nat.card f.range * Nat.card g.range := by rw [hexact]
    _ = Nat.card (OrdinaryUnitNthPowerQuotient K (n : ℕ)) *
        Nat.card (ClassGroupNthPowerTorsion K (n : ℕ)) := by
      rw [← Nat.card_congr eUnit.toEquiv,
        g.range_eq_top_of_surjective hsurjective, Subgroup.card_top]
    _ = Nat.card (OrdinaryUnitNthPowerQuotient K (n : ℕ)) *
        Nat.card (ClassFieldTower.Martinet.PClassGroup K (n : ℕ)) := by
      rw [card_classGroupNthPowerTorsion_eq_card_pClassGroup K]

/-- For a prime `p`, the radical cardinality has the Dirichlet-unit rank,
the root-of-unity correction, and the elementary `p`-class factor. -/
theorem card_idealPthPowerRadicalQuotient
    (p : ℕ) (hp : p.Prime) :
    Nat.card
        (IdealNthPowerRadicalQuotient K (p.toPNat hp.pos)) =
      p ^ (NumberField.InfinitePlace.nrRealPlaces K +
          NumberField.InfinitePlace.nrComplexPlaces K - 1 +
            (if (primitiveRoots p K).Nonempty then 1 else 0)) *
        Nat.card (ClassFieldTower.Martinet.PClassGroup K p) := by
  rw [card_idealNthPowerRadicalQuotient K (p.toPNat hp.pos)]
  change Nat.card (OrdinaryUnitNthPowerQuotient K p) *
      Nat.card (ClassFieldTower.Martinet.PClassGroup K p) = _
  rw [card_ordinaryUnitNthPowerQuotient K p hp]

end ClassFieldTower.Martinet.Shafarevich
