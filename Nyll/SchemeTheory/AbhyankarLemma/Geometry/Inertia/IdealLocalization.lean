/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.Ideal
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Invariant.Galois

/-!
# Ideal inertia and localization at a height-one prime

This file compares the ideal-theoretic inertia subgroup attached to a
nonzero maximal ideal of a Dedekind normalization with the inertia group of
the corresponding valuation subring of the fraction field.  The valuation
subring is deliberately realized inside the fraction field as the ordinary
localization subalgebra, so the comparison does not depend on a choice of a
completion or of a henselization.
-/


noncomputable section


universe uA uB uK uL

namespace TameAbhyankar.SGA1

open scoped Pointwise
open RamificationTheory.HilbertRamification.ValuationSubring

attribute [local instance] Ideal.Quotient.field

section LocalizedValuationSubring

variable (B : Type uB) (L : Type uL)
variable [CommRing B] [IsDedekindDomain B]
variable [Field L] [Algebra B L] [IsFractionRing B L]

/-- The localization of `B` at `P`, embedded in its fraction field `L`. -/
abbrev idealLocalizationSubalgebra (P : Ideal B) [P.IsPrime] :
    Subalgebra B L :=
  Localization.subalgebra.ofField L P.primeCompl
    P.primeCompl_le_nonZeroDivisors

private theorem idealLocalizationSubalgebra_dvr
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDiscreteValuationRing (idealLocalizationSubalgebra B L P) :=
  IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
    B hP (idealLocalizationSubalgebra B L P)

/-- The `P`-local valuation subring of `L`.  Its carrier is definitionally
the carrier of the localization subalgebra `B_P ⊆ L`. -/
def idealLocalizationValuationSubring
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    _root_.ValuationSubring L := by
  let S := idealLocalizationSubalgebra B L P
  letI : IsDiscreteValuationRing S :=
    idealLocalizationSubalgebra_dvr B L P hP
  let W := ((IsDiscreteValuationRing.maximalIdeal S).valuation L).valuationSubring
  have hmap : Subring.map (algebraMap S L) ⊤ = S.toSubring := by
    ext x
    constructor
    · rintro ⟨y, _hy, rfl⟩
      exact y.property
    · intro hx
      exact ⟨⟨x, hx⟩, trivial, rfl⟩
  have hcarrier : S.toSubring = W.toSubring := by
    rw [← hmap]
    exact IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
  exact
    { toSubring := S.toSubring
      mem_or_inv_mem' := fun x ↦ by
        change x ∈ S.toSubring ∨ x⁻¹ ∈ S.toSubring
        rw [hcarrier]
        exact W.mem_or_inv_mem x }

@[simp] theorem mem_idealLocalizationValuationSubring_iff
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) (x : L) :
    x ∈ idealLocalizationValuationSubring B L P hP ↔
      x ∈ idealLocalizationSubalgebra B L P :=
  Iff.rfl

/-- The identity-on-the-fraction-field equivalence between the localization
subalgebra and the valuation-subring presentation used below. -/
def idealLocalizationEquiv
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    idealLocalizationSubalgebra B L P ≃+*
      idealLocalizationValuationSubring B L P hP where
  toFun x := ⟨x, x.property⟩
  invFun x := ⟨x, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem idealLocalizationEquiv_apply_coe
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥)
    (x : idealLocalizationSubalgebra B L P) :
    ((idealLocalizationEquiv B L P hP x :
      idealLocalizationValuationSubring B L P hP) : L) = x :=
  rfl

instance idealLocalizationValuationSubring_dvr
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥) :
    IsDiscreteValuationRing
      (idealLocalizationValuationSubring B L P hP) := by
  change IsDiscreteValuationRing (idealLocalizationSubalgebra B L P)
  exact idealLocalizationSubalgebra_dvr B L P hP

theorem idealLocalizationEquiv_mem_maximalIdeal_iff
    (P : Ideal B) [P.IsPrime] (hP : P ≠ ⊥)
    (x : idealLocalizationSubalgebra B L P) :
    letI := idealLocalizationSubalgebra_dvr B L P hP
    idealLocalizationEquiv B L P hP x ∈
        IsLocalRing.maximalIdeal
          (idealLocalizationValuationSubring B L P hP) ↔
      x ∈ IsLocalRing.maximalIdeal
        (idealLocalizationSubalgebra B L P) := by
  let : IsDiscreteValuationRing (idealLocalizationSubalgebra B L P) :=
    idealLocalizationSubalgebra_dvr B L P hP
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal]
  exact not_congr
    (MulEquiv.isUnit_map
      (idealLocalizationEquiv B L P hP).toMulEquiv)

/-- Localization does not change the residue field at `P`. -/
def idealLocalizationResidueEquiv
    (P : Ideal B) [P.IsMaximal] (hP : P ≠ ⊥) :
    B ⧸ P ≃+*
      IsLocalRing.ResidueField
        (idealLocalizationValuationSubring B L P hP) := by
  let S := idealLocalizationSubalgebra B L P
  let V := idealLocalizationValuationSubring B L P hP
  letI : IsDiscreteValuationRing S :=
    idealLocalizationSubalgebra_dvr B L P hP
  let e : S ≃+* V := idealLocalizationEquiv B L P hP
  haveI : ((IsLocalRing.maximalIdeal S).map e).IsMaximal :=
    Ideal.map_isMaximal_of_equiv e
  have hmax : IsLocalRing.maximalIdeal V =
      (IsLocalRing.maximalIdeal S).map e :=
    (IsLocalRing.eq_maximalIdeal
      (R := V) (I := (IsLocalRing.maximalIdeal S).map e)
      inferInstance).symm
  exact (IsLocalization.AtPrime.equivQuotMaximalIdeal P S).toRingEquiv.trans
    (Ideal.quotientEquiv
      (IsLocalRing.maximalIdeal S)
      (IsLocalRing.maximalIdeal V) e hmax)

/-- The exponential residue characteristic can be read either before or
after localization at `P`. -/
theorem ringExpChar_idealLocalizationResidueField_eq
    (P : Ideal B) [P.IsMaximal] (hP : P ≠ ⊥) :
    ringExpChar
        (IsLocalRing.ResidueField
          (idealLocalizationValuationSubring B L P hP)) =
      ringExpChar (B ⧸ P) := by
  let e := idealLocalizationResidueEquiv B L P hP
  let : Algebra (B ⧸ P)
      (IsLocalRing.ResidueField
        (idealLocalizationValuationSubring B L P hP)) :=
    e.toRingHom.toAlgebra
  unfold ringExpChar
  exact congrArg (fun n : ℕ ↦ max n 1)
    (Algebra.ringChar_eq (B ⧸ P)
      (IsLocalRing.ResidueField
        (idealLocalizationValuationSubring B L P hP))).symm

end LocalizedValuationSubring

section NormalizationInertia

variable {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL}
variable [CommRing A] [CommRing B] [Field K] [Field L]
variable [Algebra A K] [IsFractionRing A K]
variable [Algebra B L] [IsFractionRing B L]
variable [Algebra A B] [Algebra K L] [Algebra A L]
variable [IsScalarTower A K L] [IsScalarTower A B L]
variable [IsIntegralClosure B A L]
variable [Algebra.IsAlgebraic K L]
variable [IsDedekindDomain B]

omit [IsFractionRing B L] [IsDedekindDomain B] in
@[simp] theorem algebraMap_normalization_smul
    (sigma : Gal(L/K)) (b : B) :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    algebraMap B L (sigma • b) = sigma (algebraMap B L b) := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  change algebraMap B L (galRestrict A K L B sigma b) =
    sigma (algebraMap B L b)
  exact algebraMap_galRestrict_apply A sigma b

variable (P : Ideal B) [P.IsMaximal]
variable (hP : P ≠ ⊥)

private theorem globalInertia_maps_localization :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    ∀ (sigma : P.toAddSubgroup.inertia Gal(L/K)) {x : L},
      x ∈ idealLocalizationValuationSubring B L P hP →
      ((sigma : Gal(L/K)) : L ≃ₐ[K] L) x ∈
        idealLocalizationValuationSubring B L P hP := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  intro sigma x hx
  change x ∈ idealLocalizationSubalgebra B L P at hx
  change ((sigma : Gal(L/K)) : L ≃ₐ[K] L) x ∈
    idealLocalizationSubalgebra B L P
  rcases hx with ⟨a, s, hs, rfl⟩
  have hdelta : (sigma : Gal(L/K)) • s - s ∈ P := sigma.property s
  have hsigma : (sigma : Gal(L/K)) • s ∈ P.primeCompl := by
    intro hsigmaP
    have hsP : s ∈ P := by
      simpa only [sub_sub_cancel] using P.sub_mem hsigmaP hdelta
    exact hs hsP
  refine ⟨(sigma : Gal(L/K)) • a, (sigma : Gal(L/K)) • s,
    hsigma, ?_⟩
  simp only [map_mul, map_inv₀,
    algebraMap_normalization_smul (A := A)]

private theorem globalInertia_maps_localization_iff :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    ∀ (sigma : P.toAddSubgroup.inertia Gal(L/K)) (x : L),
      ((sigma : Gal(L/K)) : L ≃ₐ[K] L) x ∈
          idealLocalizationValuationSubring B L P hP ↔
        x ∈ idealLocalizationValuationSubring B L P hP := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  intro sigma x
  constructor
  · intro hx
    have hinv := globalInertia_maps_localization
      (A := A) (P := P) (hP := hP) sigma⁻¹ hx
    simpa using hinv
  · exact globalInertia_maps_localization
      (A := A) (P := P) (hP := hP) sigma

/-- A global ideal-inertia element preserves the local valuation subring, so
it gives an element of the local decomposition group. -/
def globalIdealInertiaToDecomposition :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    P.toAddSubgroup.inertia Gal(L/K) →
      decompositionGroup K (idealLocalizationValuationSubring B L P hP) := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  intro sigma
  refine ⟨(sigma : Gal(L/K)), ?_⟩
  apply _root_.ValuationSubring.toSubring_injective
  ext x
  change x ∈ (sigma : Gal(L/K)) •
      idealLocalizationValuationSubring B L P hP ↔
    x ∈ idealLocalizationValuationSubring B L P hP
  rw [_root_.ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  exact globalInertia_maps_localization_iff
    (A := A) (P := P) (hP := hP) sigma⁻¹ x

private theorem globalIdealInertiaToDecomposition_mem_localIdealInertia :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    ∀ sigma : P.toAddSubgroup.inertia Gal(L/K),
      globalIdealInertiaToDecomposition
          (A := A) (P := P) (hP := hP) sigma ∈
        (IsLocalRing.maximalIdeal
          (idealLocalizationValuationSubring B L P hP)).toAddSubgroup.inertia
            (decompositionGroup K
              (idealLocalizationValuationSubring B L P hP)) := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  intro sigma x
  let S := idealLocalizationSubalgebra B L P
  let V := idealLocalizationValuationSubring B L P hP
  let : IsDiscreteValuationRing S :=
    idealLocalizationSubalgebra_dvr B L P hP
  let e : S ≃+* V := idealLocalizationEquiv B L P hP
  let delta : decompositionGroup K V :=
    globalIdealInertiaToDecomposition
      (A := A) (P := P) (hP := hP) sigma
  rcases x.property with ⟨a, s, hs, hx⟩
  have hs0 : s ≠ 0 := by
    intro hszero
    apply hs
    simp [hszero]
  have hdeltaA : (sigma : Gal(L/K)) • a - a ∈ P := sigma.property a
  have hdeltaS : (sigma : Gal(L/K)) • s - s ∈ P := sigma.property s
  have hsigma : (sigma : Gal(L/K)) • s ∈ P.primeCompl := by
    intro hsigmaP
    have hsP : s ∈ P := by
      simpa only [sub_sub_cancel] using P.sub_mem hsigmaP hdeltaS
    exact hs hsP
  have hsL0 : algebraMap B L s ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective B L).ne hs0
  have hsigmaMapL0 :
      ((sigma : Gal(L/K)) : L ≃ₐ[K] L) (algebraMap B L s) ≠ 0 :=
    by simpa only [map_zero] using
      ((sigma : Gal(L/K)) : L ≃ₐ[K] L).injective.ne hsL0
  let ys : S := ⟨x, x.property⟩
  let sigmays : S := e.symm (delta • x)
  have hys : ys = IsLocalization.mk' S a ⟨s, hs⟩ := by
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    apply Subtype.ext
    change (x : L) * algebraMap B L s = algebraMap B L a
    rw [hx]
    simp [hs0]
  have hsigmays : sigmays =
      IsLocalization.mk' S ((sigma : Gal(L/K)) • a)
        ⟨(sigma : Gal(L/K)) • s, hsigma⟩ := by
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    apply Subtype.ext
    change ((sigma : Gal(L/K)) : L ≃ₐ[K] L) (x : L) *
        algebraMap B L ((sigma : Gal(L/K)) • s) =
      algebraMap B L ((sigma : Gal(L/K)) • a)
    rw [algebraMap_normalization_smul (A := A),
      algebraMap_normalization_smul (A := A), hx, map_mul, map_inv₀]
    rw [mul_assoc, inv_mul_cancel₀ hsigmaMapL0, mul_one]
  have hnum :
      (sigma : Gal(L/K)) • a * s -
          a * ((sigma : Gal(L/K)) • s) ∈ P := by
    have h := P.sub_mem
      (P.mul_mem_right s hdeltaA)
      (P.mul_mem_left a hdeltaS)
    convert h using 1
    all_goals ring
  let den : P.primeCompl :=
    ⟨((sigma : Gal(L/K)) • s) * s,
      P.primeCompl.mul_mem hsigma hs⟩
  have hfrac : IsLocalization.mk' S
        ((sigma : Gal(L/K)) • a * s -
          a * ((sigma : Gal(L/K)) • s)) den ∈
      IsLocalRing.maximalIdeal S :=
    (IsLocalization.AtPrime.mk'_mem_maximal_iff S P _ den).mpr hnum
  have hsub : sigmays - ys ∈ IsLocalRing.maximalIdeal S := by
    rw [hsigmays, hys]
    rw [← IsLocalization.mk'_sub]
    exact hfrac
  have hlocal : e (sigmays - ys) ∈ IsLocalRing.maximalIdeal V :=
    (idealLocalizationEquiv_mem_maximalIdeal_iff B L P hP
      (sigmays - ys)).mpr hsub
  rw [map_sub] at hlocal
  have hesigma : e sigmays = delta • x := by
    exact e.apply_symm_apply (delta • x)
  have heys : e ys = x := by
    apply Subtype.ext
    rfl
  rwa [hesigma, heys] at hlocal

/-- Localization sends global ideal inertia to the inertia group of the
`P`-local valuation subring. -/
def globalIdealInertiaToLocalInertia :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    P.toAddSubgroup.inertia Gal(L/K) →*
      inertiaGroup K (idealLocalizationValuationSubring B L P hP) := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  refine
    { toFun := fun sigma ↦
        ⟨globalIdealInertiaToDecomposition
            (A := A) (P := P) (hP := hP) sigma, ?_⟩
      map_one' := ?_
      map_mul' := ?_ }
  · rw [← TameInertiaCyclicCore.valuationSubring_maximalIdeal_inertia_eq]
    exact globalIdealInertiaToDecomposition_mem_localIdealInertia
      (A := A) (P := P) (hP := hP) sigma
  · rfl
  · intro sigma tau
    rfl

/-- Restricting a local inertia automorphism to the normalization recovers a
global ideal-inertia element. -/
def localInertiaToGlobalIdealInertia :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    inertiaGroup K (idealLocalizationValuationSubring B L P hP) →*
      P.toAddSubgroup.inertia Gal(L/K) := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  let S := idealLocalizationSubalgebra B L P
  let V := idealLocalizationValuationSubring B L P hP
  letI : IsDiscreteValuationRing S :=
    idealLocalizationSubalgebra_dvr B L P hP
  let e : S ≃+* V := idealLocalizationEquiv B L P hP
  refine
    { toFun := fun tau ↦ ⟨((tau : decompositionGroup K V) : Gal(L/K)), ?_⟩
      map_one' := ?_
      map_mul' := ?_ }
  · intro b
    let vb : V :=
      ⟨algebraMap B L b, by
        change algebraMap B L b ∈ idealLocalizationSubalgebra B L P
        exact ⟨b, 1, P.primeCompl.one_mem, by simp⟩⟩
    have htauIdeal : (tau : decompositionGroup K V) ∈
        (IsLocalRing.maximalIdeal V).toAddSubgroup.inertia
          (decompositionGroup K V) := by
      rw [TameInertiaCyclicCore.valuationSubring_maximalIdeal_inertia_eq]
      exact tau.property
    have hlocal : (tau : decompositionGroup K V) • vb - vb ∈
        IsLocalRing.maximalIdeal V :=
      htauIdeal vb
    let zS : S := e.symm ((tau : decompositionGroup K V) • vb - vb)
    have hzS : zS ∈ IsLocalRing.maximalIdeal S := by
      apply (idealLocalizationEquiv_mem_maximalIdeal_iff B L P hP zS).mp
      simpa [e, zS] using hlocal
    have hzEq : zS = algebraMap B S
        (((tau : decompositionGroup K V) : Gal(L/K)) • b - b) := by
      apply Subtype.ext
      change
        (((tau : decompositionGroup K V) : Gal(L/K)) : L ≃ₐ[K] L)
              (algebraMap B L b) - algebraMap B L b =
          algebraMap B L
            (((tau : decompositionGroup K V) : Gal(L/K)) • b - b)
      rw [map_sub, algebraMap_normalization_smul (A := A)]
    apply (IsLocalization.AtPrime.to_map_mem_maximal_iff S P _).mp
    rw [← hzEq]
    exact hzS
  · rfl
  · intro sigma tau
    rfl

/-- Global ideal inertia at `P` is canonically the inertia group of the
valuation subring obtained by localizing at `P`. -/
def idealInertiaLocalizationMulEquiv :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    P.toAddSubgroup.inertia Gal(L/K) ≃*
      inertiaGroup K (idealLocalizationValuationSubring B L P hP) := by
  letI := IsIntegralClosure.MulSemiringAction A K L B
  refine
    { toFun := globalIdealInertiaToLocalInertia
        (A := A) (P := P) (hP := hP)
      invFun := localInertiaToGlobalIdealInertia
        (A := A) (P := P) (hP := hP)
      left_inv := ?_
      right_inv := ?_
      map_mul' := ?_ }
  · intro sigma
    apply Subtype.ext
    rfl
  · intro tau
    apply Subtype.ext
    apply Subtype.ext
    rfl
  · intro sigma tau
    rfl

/-- The global and localized inertia groups have the same cardinality. -/
theorem natCard_idealInertia_eq_localInertia :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    Nat.card (P.toAddSubgroup.inertia Gal(L/K)) =
      Nat.card
        (inertiaGroup K
          (idealLocalizationValuationSubring B L P hP)) := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  exact Nat.card_congr
    (idealInertiaLocalizationMulEquiv
      (A := A) (P := P) (hP := hP)).toEquiv

/-- Tame ideal inertia at every nonzero maximal ideal of a Dedekind
normalization is cyclic.  The proof is purely local at `P`; no completeness
or henselian hypothesis is used. -/
theorem idealInertia_isCyclic_of_card_coprime_ringExpChar
    [FiniteDimensional K L] [IsGalois K L]
    (hP0 : P ≠ ⊥)
    (hcop :
      letI := IsIntegralClosure.MulSemiringAction A K L B
      Nat.Coprime
        (Nat.card (P.toAddSubgroup.inertia Gal(L/K)))
        (ringExpChar (B ⧸ P))) :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    IsCyclic (P.toAddSubgroup.inertia Gal(L/K)) := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  let V := idealLocalizationValuationSubring B L P hP0
  let : Finite (L ≃ₐ[K] L) := inferInstance
  let : Finite (inertiaGroup K V) := inferInstance
  have hcard :
      Nat.card (P.toAddSubgroup.inertia Gal(L/K)) =
        Nat.card (inertiaGroup K V) :=
    natCard_idealInertia_eq_localInertia
      (A := A) (P := P) (hP := hP0)
  have hchar :
      ringExpChar (IsLocalRing.ResidueField V) =
        ringExpChar (B ⧸ P) :=
    ringExpChar_idealLocalizationResidueField_eq B L P hP0
  have hcopLocal : Nat.Coprime
      (Nat.card (inertiaGroup K V))
      (ringExpChar (IsLocalRing.ResidueField V)) := by
    rw [← hcard, hchar]
    exact hcop
  have hlocal : IsCyclic (inertiaGroup K V) :=
    inertiaGroup_isCyclic_of_card_coprime_ringExpChar_of_dvr
      K V hcopLocal
  exact (idealInertiaLocalizationMulEquiv
    (A := A) (P := P) (hP := hP0)).isCyclic.mpr hlocal

end NormalizationInertia

end TameAbhyankar.SGA1

end
