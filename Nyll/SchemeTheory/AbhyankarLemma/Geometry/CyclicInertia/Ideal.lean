/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.Core
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Tame inertia cyclicity over a DVR

For a discrete valuation ring, the value-class source of the production
inertia character is cyclic and every decomposition automorphism acts
trivially on that source.  The lightweight character core then turns
coprimality with the exponential residue characteristic into cyclicity of
the inertia group.
-/


noncomputable section


universe u v

namespace TameAbhyankar.SGA1

open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

private theorem quotient_unitGroup_isCyclic_of_isDiscreteValuationRing
    {L : Type*} [Field L] (V : _root_.ValuationSubring L)
    [IsDiscreteValuationRing V] :
    IsCyclic (Lˣ ⧸ V.unitGroup) := by
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation L
  let f : Lˣ →* (WithZero (Multiplicative ℤ))ˣ :=
    Units.map v.toMonoidWithZeroHom.toMonoidHom
  have hV : v.valuationSubring = V := by
    apply _root_.ValuationSubring.toSubring_injective
    rw [← IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
      (A := V) (K := L)]
    ext x
    constructor
    · rintro ⟨a, _ha, rfl⟩
      exact a.property
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hker : f.ker = V.unitGroup := by
    rw [← hV]
    ext x
    rw [MonoidHom.mem_ker, v.mem_unitGroup_iff]
    constructor
    · intro hx
      exact congrArg Units.val hx
    · intro hx
      apply Units.ext
      exact hx
  let e : Lˣ ⧸ V.unitGroup ≃* f.range :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivRange f)
  have : IsCyclic f.range := Subgroup.isCyclic_of_le le_top
  exact isCyclic_of_injective e.toMonoidHom e.injective

private theorem relativeValueClass_isCyclic_of_isDiscreteValuationRing
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V] :
    IsCyclic
      ((Lˣ ⧸ V.unitGroup) ⧸ baseUnitValueClassSubgroup K V) := by
  let : IsCyclic (Lˣ ⧸ V.unitGroup) :=
    quotient_unitGroup_isCyclic_of_isDiscreteValuationRing V
  exact isCyclic_of_surjective
    (QuotientGroup.mk' (baseUnitValueClassSubgroup K V))
    (QuotientGroup.mk'_surjective _)

private theorem automorphismUnitQuotient_mk_mem_unitGroup_of_dvr
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    (sigma : decompositionGroup K V) (a : V) (ha : a ≠ 0) :
    automorphismUnitQuotient K V sigma
        (Units.mk0 (a : L) (by
          change algebraMap V L a ≠ 0
          exact (map_ne_zero_iff (algebraMap V L)
            (IsFractionRing.injective V L)).2 ha)) ∈
      V.unitGroup := by
  let eV : V ≃+* V :=
    MulSemiringAction.toRingEquiv (decompositionGroup K V) V sigma
  have haL : (a : L) ≠ 0 := by
    change algebraMap V L a ≠ 0
    exact (map_ne_zero_iff (algebraMap V L)
      (IsFractionRing.injective V L)).2 ha
  obtain ⟨pi, hpi⟩ := IsDiscreteValuationRing.exists_irreducible V
  obtain ⟨n, han⟩ :=
    IsDiscreteValuationRing.associated_pow_irreducible ha hpi
  obtain ⟨ua, hua⟩ := han
  have hepi : Irreducible (eV pi) := hpi.map eV.toMulEquiv
  have hepiAssoc : Associated (eV pi) pi :=
    IsDiscreteValuationRing.associated_of_irreducible V hepi hpi
  have heaPow : Associated (eV a) ((eV pi) ^ n) := by
    refine ⟨Units.map eV.toMonoidHom ua, ?_⟩
    simpa using congrArg eV hua
  have hea : Associated (eV a) a :=
    (heaPow.trans hepiAssoc.pow_pow).trans
      (Associated.symm ⟨ua, hua⟩)
  obtain ⟨u, hu⟩ := hea
  let aL : Lˣ := Units.mk0 (a : L) haL
  let uL : Lˣ := Units.map V.subtype.toMonoidHom u
  have huL : ((sigma : L ≃ₐ[K] L) (a : L)) * (u : V) = (a : L) := by
    have hu' := congrArg (fun z : V => (z : L)) hu
    change ((sigma : L ≃ₐ[K] L) • (a : L)) * (u : V) = (a : L) at hu'
    simpa only [AlgEquiv.smul_def] using hu'
  have hquotVal : ((sigma : L ≃ₐ[K] L) (a : L)) / (a : L) =
      ((u : V) : L)⁻¹ := by
    apply (mul_right_cancel₀ haL)
    rw [div_mul_cancel₀ _ haL]
    symm
    calc
      ((u : V) : L)⁻¹ * (a : L) =
          ((u : V) : L)⁻¹ *
            (((sigma : L ≃ₐ[K] L) (a : L)) * (u : V)) := by rw [huL]
      _ = (sigma : L ≃ₐ[K] L) (a : L) := by
        field_simp
  have hquot : automorphismUnitQuotient K V sigma aL = uL⁻¹ := by
    apply Units.ext
    simpa [automorphismUnitQuotient, aL, uL] using hquotVal
  rw [hquot]
  exact V.unitGroup.inv_mem
    (show uL ∈ V.unitGroup from
      (V.unitGroupMulEquiv.symm u).property)

/-- Every automorphism stabilizing a discrete valuation ring acts trivially on
the value group: its multiplicative displacement is a valuation-ring unit. -/
theorem automorphismUnitQuotient_mem_unitGroup_of_dvr
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    (sigma : decompositionGroup K V) (x : Lˣ) :
    automorphismUnitQuotient K V sigma x ∈ V.unitGroup := by
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := V) (x : L)
  have ha : a ≠ 0 := by
    intro ha0
    have hx0 : (x : L) = 0 := by simpa [ha0] using hab.symm
    exact Units.ne_zero x hx0
  let aL : Lˣ := Units.mk0 (a : L) (by
    exact (map_ne_zero_iff (algebraMap V L)
      (IsFractionRing.injective V L)).2 ha)
  let bL : Lˣ := Units.mk0 (b : L) (by
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb)
  have hx : x = aL / bL := by
    apply Units.ext
    rw [Units.val_div_eq_div_val]
    change (x : L) = (a : L) / (b : L)
    exact hab.symm
  rw [hx]
  rw [div_eq_mul_inv, automorphismUnitQuotient_mul_arg]
  have haUnit := automorphismUnitQuotient_mk_mem_unitGroup_of_dvr
    K V (sigma : decompositionGroup K V) a ha
  have hbne : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbUnit := automorphismUnitQuotient_mk_mem_unitGroup_of_dvr
    K V (sigma : decompositionGroup K V) b hbne
  have hinv :
      automorphismUnitQuotient K V (sigma : decompositionGroup K V) bL⁻¹ =
        (automorphismUnitQuotient K V
          (sigma : decompositionGroup K V) bL)⁻¹ := by
    apply Units.ext
    simp [automorphismUnitQuotient, div_eq_mul_inv, mul_comm]
  rw [hinv]
  exact V.unitGroup.mul_mem haUnit (V.unitGroup.inv_mem hbUnit)

private theorem valueTrivialInertiaGroup_eq_top_of_isDiscreteValuationRing
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V] :
    valueTrivialInertiaGroup K V = ⊤ := by
  rw [eq_top_iff]
  intro sigma _hsigma x
  rw [valueDisplacementClass_eq_one_iff]
  exact automorphismUnitQuotient_mem_unitGroup_of_dvr K V
    (sigma : decompositionGroup K V) x

/-- Every inertia automorphism over a discrete valuation ring acts trivially
on the relative value group.  This is the public elementwise form of the DVR
input used by the tame-inertia character. -/
theorem inertia_mem_valueTrivialInertiaGroup_of_dvr
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    (sigma : inertiaGroup K V) :
    sigma ∈ valueTrivialInertiaGroup K V := by
  rw [valueTrivialInertiaGroup_eq_top_of_isDiscreteValuationRing K V]
  exact Subgroup.mem_top sigma

/-- Tame inertia over a DVR is cyclic when its order is prime to the
exponential residue characteristic. -/
theorem inertiaGroup_isCyclic_of_card_coprime_ringExpChar_of_dvr
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [Finite (inertiaGroup K V)]
    (hcop : Nat.Coprime (Nat.card (inertiaGroup K V))
      (ringExpChar (IsLocalRing.ResidueField V))) :
    IsCyclic (inertiaGroup K V) := by
  let : IsCyclic
      ((Lˣ ⧸ V.unitGroup) ⧸ baseUnitValueClassSubgroup K V) :=
    relativeValueClass_isCyclic_of_isDiscreteValuationRing K V
  exact TameInertiaCyclicCore.inertiaGroup_isCyclic_of_card_coprime_ringExpChar
    K V (valueTrivialInertiaGroup_eq_top_of_isDiscreteValuationRing K V) hcop

end TameAbhyankar.SGA1

end
