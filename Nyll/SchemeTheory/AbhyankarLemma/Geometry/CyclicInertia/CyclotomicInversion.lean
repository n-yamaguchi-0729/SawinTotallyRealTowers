/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.SeparableClosure.GeometricallyIntegralRestriction
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.ResidueLift
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.Conjugation
import Nyll.GaloisCohomology.Kummer.Concrete.Cyclotomic.RationalCyclotomicCharacterEquiv
import Nyll.SchemeTheory.FunctionFields.IntegerBase

/-!
# Cyclotomic inversion and tame inertia

This file constructs the rational cyclotomic automorphism with character
`-1`, transports it to a separable closure of a regular characteristic-zero
field, and connects its residue lift to conjugation on finite tame inertia.
-/

noncomputable section


universe u v w

namespace EtaleFundamentalGroups

open ClassFormation KummerTheory

/-- The rational cyclotomic extension has an automorphism which inverts every
finite-order unit. -/
theorem exists_rationalCyclotomicAutomorphism_inverting_torsionUnits :
    ∃ sigma : rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField,
      ∀ z : rationalCyclotomicFieldˣ, IsOfFinOrder z →
        Units.mapEquiv sigma.toMulEquiv z = z⁻¹ := by
  obtain ⟨sigma, hsigma⟩ :=
    rationalCyclotomicCharacter_surjective (-1 : ZHatˣ)
  refine ⟨sigma, ?_⟩
  intro z hz
  obtain ⟨n, hnpos, hzn⟩ := hz.exists_pow_eq_one
  let npos : ℕ+ := ⟨n, hnpos⟩
  have hnne : n ≠ 0 := Nat.ne_of_gt hnpos
  have hzn' : (z : rationalCyclotomicField) ^ n = 1 :=
    congrArg Units.val hzn
  have hzmem :
      (z : rationalCyclotomicField) ∈ rationalCyclotomicLevel npos := by
    apply IntermediateField.subset_adjoin
    exact ⟨(npos : ℕ), by simp, npos.ne_zero, by simpa [npos] using hzn'⟩
  let y : rationalCyclotomicLevel npos := ⟨(z : rationalCyclotomicField), hzmem⟩
  let a : (ZMod (npos : ℕ))ˣ :=
    IsCyclotomicExtension.Rat.galEquivZMod (npos : ℕ)
      (rationalCyclotomicLevel npos)
      (sigma.restrictNormal (rationalCyclotomicLevel npos))
  have ha : a = -1 := by
    apply Units.ext
    let e := ZMod.equivPi (n := n) hnne
    apply e.injective
    funext q
    have hqPrime : q.1.Prime := Nat.prime_of_mem_primeFactors q.2
    let p : Nat.Primes := ⟨q.1, hqPrime⟩
    let : Fact p.1.Prime := ⟨p.2⟩
    let k := n.factorization q.1
    have hpow : p.1 ^ k ∣ n :=
      (hqPrime.pow_dvd_iff_le_factorization hnne).2 le_rfl
    have hminusCoord :
        zHatUnitsContinuousMulEquivPrimeProduct (-1 : ZHatˣ) p = -1 := by
      apply Units.ext
      simp [zHatUnitsContinuousMulEquivPrimeProduct_coe_apply]
    have hpCoordinate :=
      congrArg
        (fun u : ZHatˣ => zHatUnitsContinuousMulEquivPrimeProduct u p)
        hsigma
    rw [hminusCoord] at hpCoordinate
    have hcharCoordinate :=
      zHatUnitsContinuousMulEquivPrimeProduct_rationalCyclotomicCharacter
        sigma p
    change
      zHatUnitsContinuousMulEquivPrimeProduct
          (rationalCyclotomicCharacter sigma) p =
        rationalCyclotomicCharacterPrimeProduct sigma p at hcharCoordinate
    rw [hcharCoordinate] at hpCoordinate
    have hpReduction :=
      congrArg (Units.map (PadicInt.toZModPow k).toMonoidHom) hpCoordinate
    rw [rationalCyclotomicCharacterPrimeProduct_toZModPow_of_dvd
      sigma p k npos hpow] at hpReduction
    have hred :
        ZMod.unitsMap hpow a = ZMod.unitsMap hpow (-1) := by
      dsimp [a]
      have hpadicNeg :
          Units.map (PadicInt.toZModPow k).toMonoidHom
              (-1 : ℤ_[p.1]ˣ) = -1 := by
        apply Units.ext
        simp
      have hunitsMapNeg :
          ZMod.unitsMap hpow (-1) = (-1 : (ZMod (p.1 ^ k))ˣ) := by
        apply Units.ext
        change ZMod.castHom hpow (ZMod (p.1 ^ k)) (-1) = -1
        rw [map_neg, map_one]
      calc
        _ = -1 := hpReduction.trans hpadicNeg
        _ = ZMod.unitsMap hpow (-1) := hunitsMapNeg.symm
    have heval (c : ZMod n) :
        e c q = ZMod.castHom hpow (ZMod (p.1 ^ k)) c := by
      change
        ((Pi.evalRingHom
            (fun r : n.primeFactors =>
              ZMod (r.1 ^ n.factorization r.1)) q).comp
          e.toRingHom) c =
            ZMod.castHom hpow (ZMod (p.1 ^ k)) c
      exact RingHom.congr_fun (Subsingleton.elim _ _) c
    exact (heval a.val).trans
      ((congrArg Units.val hred).trans
        (heval (-1 : (ZMod (npos : ℕ))ˣ).val).symm)
  have hyPow : y ^ n = 1 := by
    apply Subtype.ext
    exact hzn'
  have hyAction :
      (sigma.restrictNormal (rationalCyclotomicLevel npos)) y =
        y ^ a.val.val := by
    exact IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (npos : ℕ) (rationalCyclotomicLevel npos)
      (sigma.restrictNormal (rationalCyclotomicLevel npos)) hyPow
  have hval :
      ((-1 : (ZMod (npos : ℕ))ˣ) : ZMod (npos : ℕ)).val = n - 1 := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hnne
    change (-1 : ZMod m.succ).val = m
    exact ZMod.val_neg_one m
  have hpredMul :
      (z : rationalCyclotomicField) ^ (n - 1) * z = 1 := by
    calc
      (z : rationalCyclotomicField) ^ (n - 1) * z =
          (z : rationalCyclotomicField) ^ ((n - 1) + 1) := by
            rw [pow_succ]
      _ = (z : rationalCyclotomicField) ^ n := by
        rw [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hnne)]
      _ = 1 := hzn'
  apply Units.ext
  rw [Units.coe_mapEquiv, Units.val_inv_eq_inv_val]
  change sigma (z : rationalCyclotomicField) =
    (z : rationalCyclotomicField)⁻¹
  calc
    sigma (z : rationalCyclotomicField) =
        algebraMap (rationalCyclotomicLevel npos) rationalCyclotomicField
          ((sigma.restrictNormal (rationalCyclotomicLevel npos)) y) :=
      (AlgEquiv.restrictNormal_commutes sigma
        (rationalCyclotomicLevel npos) y).symm
    _ = algebraMap (rationalCyclotomicLevel npos) rationalCyclotomicField
          (y ^ a.val.val) := by rw [hyAction]
    _ = (z : rationalCyclotomicField) ^ a.val.val := by
      rw [map_pow]
      rfl
    _ = (z : rationalCyclotomicField) ^ (n - 1) := by rw [ha, hval]
    _ = (z : rationalCyclotomicField)⁻¹ := by
      calc
        (z : rationalCyclotomicField) ^ (n - 1) =
            ((z : rationalCyclotomicField) ^ (n - 1) * z) *
              (z : rationalCyclotomicField)⁻¹ := by simp
        _ = (z : rationalCyclotomicField)⁻¹ := by rw [hpredMul, one_mul]

private theorem exists_rationalCyclotomicAutomorphism_inverting_torsion :
    ∃ sigma : rationalCyclotomicField ≃ₐ[ℚ] rationalCyclotomicField,
      ∀ z : rationalCyclotomicField, IsOfFinOrder z → sigma z = z⁻¹ := by
  obtain ⟨sigma, hsigma⟩ :=
    exists_rationalCyclotomicAutomorphism_inverting_torsionUnits
  refine ⟨sigma, ?_⟩
  intro z hz
  obtain ⟨n, hnpos, hzn⟩ := hz.exists_pow_eq_one
  have hz0 : z ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (Nat.ne_of_gt hnpos)] at hzn
    exact zero_ne_one hzn
  let u : rationalCyclotomicFieldˣ := Units.mk0 z hz0
  have hu : IsOfFinOrder u := by
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨n, hnpos, ?_⟩
    apply Units.ext
    exact hzn
  have hinv := congrArg Units.val (hsigma u hu)
  rw [Units.coe_mapEquiv, Units.val_inv_eq_inv_val] at hinv
  change sigma z = z⁻¹ at hinv
  exact hinv

/-- The separable closure of `ℚ` has an automorphism which inverts every
finite-order element. -/
theorem exists_separableClosureRatAutomorphism_inverting_torsion :
    ∃ sigma : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ,
      ∀ z : SeparableClosure ℚ, IsOfFinOrder z → sigma z = z⁻¹ := by
  let : Normal ℚ (SeparableClosure ℚ) := by
    let : IsSepClosure ℚ (SeparableClosure ℚ) :=
      separableClosure.isSepClosure ℚ (AlgebraicClosure ℚ)
    let hg : IsGalois ℚ (SeparableClosure ℚ) := IsSepClosure.isGalois
    exact hg.to_normal
  obtain ⟨sigmaCyc, hsigmaCyc⟩ :=
    exists_rationalCyclotomicAutomorphism_inverting_torsion
  obtain ⟨sigma, hsigma⟩ :=
    (AlgEquiv.restrictNormalHom_surjective
      (F := ℚ) (K₁ := rationalCyclotomicField)
      (E := SeparableClosure ℚ)) sigmaCyc
  change sigma.restrictNormal rationalCyclotomicField = sigmaCyc at hsigma
  refine ⟨sigma, ?_⟩
  intro z hz
  obtain ⟨n, hnpos, hzn⟩ := hz.exists_pow_eq_one
  have hnne : n ≠ 0 := Nat.ne_of_gt hnpos
  have hzmem : (z : SeparableClosure ℚ) ∈ rationalCyclotomicField := by
    apply IntermediateField.subset_adjoin
    exact ⟨n, Set.mem_univ n, hnne, hzn⟩
  let y : rationalCyclotomicField := ⟨z, hzmem⟩
  have hy : IsOfFinOrder y := by
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨n, hnpos, ?_⟩
    apply Subtype.ext
    exact hzn
  have hcyc := hsigmaCyc y hy
  have hcomm :=
    AlgEquiv.restrictNormal_commutes sigma rationalCyclotomicField y
  rw [hsigma] at hcomm
  calc
    sigma z = algebraMap rationalCyclotomicField (SeparableClosure ℚ)
        (sigmaCyc y) := hcomm.symm
    _ = algebraMap rationalCyclotomicField (SeparableClosure ℚ) y⁻¹ := by
      rw [hcyc]
    _ = z⁻¹ := rfl

/-- If a field is isomorphic to `ℚ`, a separable closure of `ℚ`, regarded
through that isomorphism as an extension of the field, has an automorphism
which inverts every finite-order element.  This formulation includes
universe lifts of `ℚ`. -/
theorem exists_separableClosureAutomorphism_inverting_torsion_of_ratEquiv
    (k : Type u) [Field k] [PerfectField k] (e : k ≃+* ℚ) :
    letI : Algebra k (SeparableClosure ℚ) :=
      ((algebraMap ℚ (SeparableClosure ℚ)).comp e.toRingHom).toAlgebra
    ∃ sigma : SeparableClosure ℚ ≃ₐ[k] SeparableClosure ℚ,
      ∀ z : SeparableClosure ℚ, IsOfFinOrder z → sigma z = z⁻¹ := by
  let : Algebra k (SeparableClosure ℚ) :=
    ((algebraMap ℚ (SeparableClosure ℚ)).comp e.toRingHom).toAlgebra
  obtain ⟨sigmaQ, hsigmaQ⟩ :=
    exists_separableClosureRatAutomorphism_inverting_torsion
  refine ⟨AlgEquiv.ofRingEquiv (f := sigmaQ.toRingEquiv) ?_, hsigmaQ⟩
  intro x
  exact sigmaQ.commutes (e x)

/-- Let `F / ℚ` be a field and let `Omega` be a separable closure of `F`.
If `F` is linearly disjoint from the separable closure of `ℚ` inside
`Omega`, then an `F`-automorphism of `Omega` inverts every finite-order
unit.  The linear-disjointness hypothesis is the field-theoretic form of
regularity used for geometrically integral characteristic-zero generic
fibres. -/
theorem exists_algEquiv_inverting_torsionUnits_of_separableClosure_linearDisjoint
    {F : Type u} {Omega : Type v}
    [Field F] [Field Omega]
    [Algebra ℚ F] [Algebra F Omega] [Algebra ℚ Omega]
    [IsScalarTower ℚ F Omega] [IsSepClosure F Omega]
    (hdisjoint : (separableClosure ℚ Omega).LinearDisjoint F) :
    ∃ tau : Omega ≃ₐ[F] Omega,
      ∀ z : Omegaˣ, IsOfFinOrder z →
        Units.mapEquiv tau.toMulEquiv z = z⁻¹ := by
  let : Algebra ℚ (separableClosure ℚ Omega) :=
    (separableClosure ℚ Omega).algebra'
  obtain ⟨sigmaSep, hsigmaSep⟩ :
      ∃ sigmaSep : separableClosure ℚ Omega ≃ₐ[ℚ] separableClosure ℚ Omega,
        ∀ x : separableClosure ℚ Omega, IsOfFinOrder x → sigmaSep x = x⁻¹ := by
    let : IsSepClosed Omega := IsSepClosure.sep_closed F
    obtain ⟨sigmaRat, hsigmaRat⟩ :=
      exists_separableClosureRatAutomorphism_inverting_torsion
    let e : SeparableClosure ℚ ≃ₐ[ℚ] separableClosure ℚ Omega := by
      let : IsSepClosure ℚ (separableClosure ℚ Omega) :=
        separableClosure.isSepClosure ℚ Omega
      let : IsSepClosure ℚ (SeparableClosure ℚ) :=
        separableClosure.isSepClosure ℚ (AlgebraicClosure ℚ)
      exact IsSepClosure.equiv ℚ (SeparableClosure ℚ) (separableClosure ℚ Omega)
    let sigmaSep :
        separableClosure ℚ Omega ≃ₐ[ℚ] separableClosure ℚ Omega :=
      AlgEquiv.autCongr e sigmaRat
    have hsigmaSep (x : separableClosure ℚ Omega) (hx : IsOfFinOrder x) :
        sigmaSep x = x⁻¹ := by
      let y : SeparableClosure ℚ := e.symm x
      have hy : IsOfFinOrder y :=
        e.symm.toRingEquiv.toMonoidHom.isOfFinOrder hx
      change e (sigmaRat (e.symm x)) = x⁻¹
      rw [hsigmaRat y hy]
      simp [y]
    exact ⟨sigmaSep, hsigmaSep⟩
  obtain ⟨tau, htau⟩ :=
    (separableClosureRestriction_surjective_of_linearDisjoint
      (k := ℚ) (K := F) (Ω := Omega) hdisjoint) sigmaSep
  refine ⟨tau, ?_⟩
  intro z hz
  obtain ⟨n, hnpos, hzn⟩ := hz.exists_pow_eq_one
  have hnne : n ≠ 0 := Nat.ne_of_gt hnpos
  have hzn' : (z : Omega) ^ n = 1 := congrArg Units.val hzn
  have hzIntegral : IsIntegral ℚ (z : Omega) := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1,
      Polynomial.monic_X_pow_sub_C 1 hnne, ?_⟩
    simp [hzn']
  have hzSeparable : IsSeparable ℚ (z : Omega) :=
    PerfectField.separable_of_irreducible (minpoly.irreducible hzIntegral)
  let x : separableClosure ℚ Omega :=
    ⟨(z : Omega), mem_separableClosure_iff.mpr hzSeparable⟩
  have hx : IsOfFinOrder x := by
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨n, hnpos, ?_⟩
    apply Subtype.ext
    exact hzn'
  have hres := congrArg (fun f => f x) htau
  have hresCoe := congrArg Subtype.val hres
  have hsepInv := hsigmaSep x hx
  apply Units.ext
  rw [Units.coe_mapEquiv, Units.val_inv_eq_inv_val]
  change tau (z : Omega) = (z : Omega)⁻¹
  calc
    tau (z : Omega) = (sigmaSep x : separableClosure ℚ Omega) := by
      exact hresCoe
    _ = (x⁻¹ : separableClosure ℚ Omega) := by rw [hsepInv]
    _ = (z : Omega)⁻¹ := rfl

/-- Cyclotomic inversion over a rational base field presented by a ring
equivalence with `ℚ`.  This version applies directly to `ULift ℚ`, so it is
compatible with arithmetic schemes in an arbitrary universe. -/
theorem exists_algEquiv_inverting_torsionUnits_of_separableClosure_linearDisjoint_of_ratEquiv
    {k : Type u} {F : Type v} {Omega : Type w}
    [Field k] [PerfectField k] [Field F] [Field Omega]
    [Algebra k F] [Algebra F Omega] [Algebra k Omega]
    [IsScalarTower k F Omega] [IsSepClosure F Omega]
    (e : k ≃+* ℚ)
    (hdisjoint : (separableClosure k Omega).LinearDisjoint F) :
    ∃ tau : Omega ≃ₐ[F] Omega,
      ∀ z : Omegaˣ, IsOfFinOrder z →
        Units.mapEquiv tau.toMulEquiv z = z⁻¹ := by
  obtain ⟨sigmaSep, hsigmaSep⟩ :
      ∃ sigmaSep : separableClosure k Omega ≃ₐ[k] separableClosure k Omega,
        ∀ x : separableClosure k Omega, IsOfFinOrder x → sigmaSep x = x⁻¹ := by
    let : IsSepClosed Omega := IsSepClosure.sep_closed F
    let : Algebra k (SeparableClosure ℚ) :=
      ((algebraMap ℚ (SeparableClosure ℚ)).comp e.toRingHom).toAlgebra
    let : IsSepClosure k (SeparableClosure ℚ) := by
      have hsep : Algebra.IsSeparable k (SeparableClosure ℚ) := by
        let : IsSepClosure ℚ (SeparableClosure ℚ) :=
          separableClosure.isSepClosure ℚ (AlgebraicClosure ℚ)
        apply Algebra.IsSeparable.of_equiv_equiv e.symm
          (RingEquiv.refl (SeparableClosure ℚ))
        ext q
        rw [RingHom.algebraMap_toAlgebra]
        simp
      exact IsSepClosure.mk inferInstance hsep
    obtain ⟨sigmaRat, hsigmaRat⟩ :=
      exists_separableClosureAutomorphism_inverting_torsion_of_ratEquiv k e
    let ek : SeparableClosure ℚ ≃ₐ[k] separableClosure k Omega :=
      IsSepClosure.equiv k (SeparableClosure ℚ) (separableClosure k Omega)
    let sigmaSep :
        separableClosure k Omega ≃ₐ[k] separableClosure k Omega :=
      AlgEquiv.autCongr ek sigmaRat
    have hsigmaSep (x : separableClosure k Omega) (hx : IsOfFinOrder x) :
        sigmaSep x = x⁻¹ := by
      let y : SeparableClosure ℚ := ek.symm x
      have hy : IsOfFinOrder y :=
        ek.symm.toRingEquiv.toMonoidHom.isOfFinOrder hx
      change ek (sigmaRat (ek.symm x)) = x⁻¹
      rw [hsigmaRat y hy]
      simp [y]
    exact ⟨sigmaSep, hsigmaSep⟩
  obtain ⟨tau, htau⟩ :=
    (separableClosureRestriction_surjective_of_linearDisjoint
      (k := k) (K := F) (Ω := Omega) hdisjoint) sigmaSep
  refine ⟨tau, ?_⟩
  intro z hz
  obtain ⟨n, hnpos, hzn⟩ := hz.exists_pow_eq_one
  have hnne : n ≠ 0 := Nat.ne_of_gt hnpos
  have hzn' : (z : Omega) ^ n = 1 := congrArg Units.val hzn
  have hzIntegral : IsIntegral k (z : Omega) := by
    refine ⟨Polynomial.X ^ n - Polynomial.C 1,
      Polynomial.monic_X_pow_sub_C 1 hnne, ?_⟩
    simp [hzn']
  have hzSeparable : IsSeparable k (z : Omega) :=
    PerfectField.separable_of_irreducible (minpoly.irreducible hzIntegral)
  let x : separableClosure k Omega :=
    ⟨(z : Omega), mem_separableClosure_iff.mpr hzSeparable⟩
  have hx : IsOfFinOrder x := by
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨n, hnpos, ?_⟩
    apply Subtype.ext
    exact hzn'
  have hres := congrArg (fun f => f x) htau
  have hresCoe := congrArg Subtype.val hres
  have hsepInv := hsigmaSep x hx
  apply Units.ext
  rw [Units.coe_mapEquiv, Units.val_inv_eq_inv_val]
  change tau (z : Omega) = (z : Omega)⁻¹
  calc
    tau (z : Omega) = (sigmaSep x : separableClosure k Omega) := by
      exact hresCoe
    _ = (x⁻¹ : separableClosure k Omega) := by rw [hsepInv]
    _ = (z : Omega)⁻¹ := rfl

end EtaleFundamentalGroups

namespace TameAbhyankar.SGA1

open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

/-- If the characteristic-zero decomposition residue field is regular over
`ℚ` in the linear-disjointness form, one decomposition element conjugates
every element of finite tame inertia to its inverse. -/
theorem exists_inertiaConjugate_eq_inv_of_residue_linearDisjoint
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [CharZero (decompositionResidueField K V)]
    [Finite (inertiaGroup K V)]
    [IsSepClosure (decompositionResidueField K V) (selectedResidueField V)] :
    letI : CharZero (selectedResidueField V) :=
      charZero_of_injective_algebraMap
        (algebraMap (decompositionResidueField K V)
          (selectedResidueField V)).injective
    letI : Algebra ℚ (decompositionResidueField K V) :=
      DivisionRing.toRatAlgebra
    letI : Algebra ℚ (selectedResidueField V) :=
      DivisionRing.toRatAlgebra
    letI : IsScalarTower ℚ (decompositionResidueField K V)
        (selectedResidueField V) :=
      IsScalarTower.of_algebraMap_eq fun q => by simp
    (
      (separableClosure ℚ (selectedResidueField V)).LinearDisjoint
        (decompositionResidueField K V)) →
    ∃ g : decompositionGroup K V,
      ∀ sigma : inertiaGroup K V,
        inertiaConjugate K V g sigma = sigma⁻¹ := by
  intro hdisjoint
  let : CharZero (selectedResidueField V) :=
    charZero_of_injective_algebraMap
      (algebraMap (decompositionResidueField K V)
        (selectedResidueField V)).injective
  obtain ⟨tau, htau⟩ :=
    EtaleFundamentalGroups.exists_algEquiv_inverting_torsionUnits_of_separableClosure_linearDisjoint
        (F := decompositionResidueField K V)
        (Omega := selectedResidueField V) hdisjoint
  obtain ⟨g, hg, hresidue⟩ :=
    exists_galoisAutomorphism_stabilizing_of_residueAutomorphism K V tau
  let g' : decompositionGroup K V := ⟨g, hg⟩
  refine ⟨g', ?_⟩
  intro sigma
  apply inertiaConjugate_eq_inv_of_torsion_residue_inversion K V g'
  intro z hz
  have haction :
      residueAction K V g' (z : selectedResidueField V) =
        tau (z : selectedResidueField V) := by
    exact DFunLike.congr_fun hresidue (z : selectedResidueField V)
  apply Units.ext
  rw [Units.coe_mapEquiv, Units.val_inv_eq_inv_val]
  change residueAction K V g' (z : selectedResidueField V) =
    (z : selectedResidueField V)⁻¹
  rw [haction]
  have hinv := congrArg Units.val (htau z hz)
  rw [Units.coe_mapEquiv, Units.val_inv_eq_inv_val] at hinv
  exact hinv

/-- Under the same regularity input, every finite inertia element is
conjugate to its inverse inside the decomposition group. -/
theorem inertia_isConj_inv_of_residue_linearDisjoint
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [CharZero (decompositionResidueField K V)]
    [Finite (inertiaGroup K V)]
    [IsSepClosure (decompositionResidueField K V) (selectedResidueField V)] :
    letI : CharZero (selectedResidueField V) :=
      charZero_of_injective_algebraMap
        (algebraMap (decompositionResidueField K V)
          (selectedResidueField V)).injective
    letI : Algebra ℚ (decompositionResidueField K V) :=
      DivisionRing.toRatAlgebra
    letI : Algebra ℚ (selectedResidueField V) :=
      DivisionRing.toRatAlgebra
    letI : IsScalarTower ℚ (decompositionResidueField K V)
        (selectedResidueField V) :=
      IsScalarTower.of_algebraMap_eq fun q => by simp
    (
      (separableClosure ℚ (selectedResidueField V)).LinearDisjoint
        (decompositionResidueField K V)) →
    ∀ sigma : inertiaGroup K V,
      IsConj (sigma : decompositionGroup K V)
        ((sigma⁻¹ : inertiaGroup K V) : decompositionGroup K V) := by
  intro hdisjoint
  obtain ⟨g, hg⟩ :=
    exists_inertiaConjugate_eq_inv_of_residue_linearDisjoint K V hdisjoint
  intro sigma
  refine isConj_iff.mpr ⟨g, ?_⟩
  exact congrArg Subtype.val (hg sigma)

/-- Cyclotomic inversion in finite inertia over any rational base field
presented by an equivalence with `ℚ`. -/
theorem exists_inertiaConjugate_eq_inv_of_residue_linearDisjoint_of_ratEquiv
    (k : Type v) [Field k] [PerfectField k] (e : k ≃+* ℚ)
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [CharZero (decompositionResidueField K V)]
    [Finite (inertiaGroup K V)]
    [IsSepClosure (decompositionResidueField K V) (selectedResidueField V)]
    [Algebra k (decompositionResidueField K V)]
    [Algebra k (selectedResidueField V)]
    [IsScalarTower k (decompositionResidueField K V)
      (selectedResidueField V)]
    (hdisjoint :
      (separableClosure k (selectedResidueField V)).LinearDisjoint
        (decompositionResidueField K V)) :
    ∃ g : decompositionGroup K V,
      ∀ sigma : inertiaGroup K V,
        inertiaConjugate K V g sigma = sigma⁻¹ := by
  let : CharZero (selectedResidueField V) :=
    charZero_of_injective_algebraMap
      (algebraMap (decompositionResidueField K V)
        (selectedResidueField V)).injective
  obtain ⟨tau, htau⟩ :=
    (open _root_.EtaleFundamentalGroups in
      exists_algEquiv_inverting_torsionUnits_of_separableClosure_linearDisjoint_of_ratEquiv
        (F := decompositionResidueField K V)
        (Omega := selectedResidueField V) e hdisjoint)
  obtain ⟨g, hg, hresidue⟩ :=
    exists_galoisAutomorphism_stabilizing_of_residueAutomorphism K V tau
  let g' : decompositionGroup K V := ⟨g, hg⟩
  refine ⟨g', ?_⟩
  intro sigma
  apply inertiaConjugate_eq_inv_of_torsion_residue_inversion K V g'
  intro z hz
  have haction :
      residueAction K V g' (z : selectedResidueField V) =
        tau (z : selectedResidueField V) := by
    exact DFunLike.congr_fun hresidue (z : selectedResidueField V)
  apply Units.ext
  rw [Units.coe_mapEquiv, Units.val_inv_eq_inv_val]
  change residueAction K V g' (z : selectedResidueField V) =
    (z : selectedResidueField V)⁻¹
  rw [haction]
  have hinv := congrArg Units.val (htau z hz)
  rw [Units.coe_mapEquiv, Units.val_inv_eq_inv_val] at hinv
  exact hinv

/-- Under the rational-base regularity input, every finite inertia element
is conjugate to its inverse inside the decomposition group. -/
theorem inertia_isConj_inv_of_residue_linearDisjoint_of_ratEquiv
    (k : Type v) [Field k] [PerfectField k] (e : k ≃+* ℚ)
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [CharZero (decompositionResidueField K V)]
    [Finite (inertiaGroup K V)]
    [IsSepClosure (decompositionResidueField K V) (selectedResidueField V)]
    [Algebra k (decompositionResidueField K V)]
    [Algebra k (selectedResidueField V)]
    [IsScalarTower k (decompositionResidueField K V)
      (selectedResidueField V)]
    (hdisjoint :
      (separableClosure k (selectedResidueField V)).LinearDisjoint
        (decompositionResidueField K V)) :
    ∀ sigma : inertiaGroup K V,
      IsConj (sigma : decompositionGroup K V)
        ((sigma⁻¹ : inertiaGroup K V) : decompositionGroup K V) := by
  obtain ⟨g, hg⟩ :=
    exists_inertiaConjugate_eq_inv_of_residue_linearDisjoint_of_ratEquiv
      k e K V hdisjoint
  intro sigma
  refine isConj_iff.mpr ⟨g, ?_⟩
  exact congrArg Subtype.val (hg sigma)

/-- Geometric integrality over a rational base field, including a universe
lift of `ℚ`, directly supplies conjugacy of every finite inertia element
with its inverse. -/
theorem inertia_isConj_inv_of_geometricallyIntegral_residue_of_ratEquiv
    (k : Type v) [Field k] [PerfectField k] (e : k ≃+* ℚ)
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [CharZero (decompositionResidueField K V)]
    [Finite (inertiaGroup K V)]
    [IsSepClosure (decompositionResidueField K V) (selectedResidueField V)]
    [Algebra k (decompositionResidueField K V)]
    [Algebra k (selectedResidueField V)]
    [IsScalarTower k (decompositionResidueField K V)
      (selectedResidueField V)]
    (hgeo : AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap k (decompositionResidueField K V))))) :
    ∀ sigma : inertiaGroup K V,
      IsConj (sigma : decompositionGroup K V)
        ((sigma⁻¹ : inertiaGroup K V) : decompositionGroup K V) := by
  apply inertia_isConj_inv_of_residue_linearDisjoint_of_ratEquiv k e K V
  exact
    EtaleFundamentalGroups.separableClosure_linearDisjoint_of_geometricallyIntegral

section IntegerBase

local instance : IsDomain (ULift.{v} ℤ) :=
  (ULift.ringEquiv : ULift.{v} ℤ ≃+* ℤ).toMulEquiv.isDomain ℤ

private abbrev integerGenericResidueField : Type v :=
  AlgebraicGeometry.Scheme.residueField
    (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{v} ℤ)))
    (_root_.genericPoint
      (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{v} ℤ))))

/-- Geometric integrality over the generic residue field of the integer base
supplies conjugacy of every finite inertia element with its inverse.

The rational base field and its perfectness are consequences of the generic
point of `Spec (ULift ℤ)`; they are not additional hypotheses. -/
theorem inertia_isConj_inv_of_geometricallyIntegral_residue_over_integers
    (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [CharZero (decompositionResidueField K V)]
    [Finite (inertiaGroup K V)]
    [IsSepClosure (decompositionResidueField K V) (selectedResidueField V)]
    [Algebra integerGenericResidueField (decompositionResidueField K V)]
    [Algebra integerGenericResidueField (selectedResidueField V)]
    [IsScalarTower integerGenericResidueField
      (decompositionResidueField K V) (selectedResidueField V)]
    (hgeo : AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap integerGenericResidueField
          (decompositionResidueField K V))))) :
    ∀ sigma : inertiaGroup K V,
      IsConj (sigma : decompositionGroup K V)
        ((sigma⁻¹ : inertiaGroup K V) : decompositionGroup K V) := by
  let e : integerGenericResidueField ≃+* ℚ :=
    AlgebraicGeometry.specULiftZGenericResidueFieldEquivQ
  let : PerfectField integerGenericResidueField :=
    PerfectField.of_ringEquiv e.symm
  exact
    inertia_isConj_inv_of_geometricallyIntegral_residue_of_ratEquiv
      integerGenericResidueField e K V hgeo

end IntegerBase

/-- Geometric integrality of the characteristic-zero decomposition residue
field supplies the linear disjointness needed for cyclotomic inversion.
Consequently every finite inertia element is conjugate to its inverse. -/
theorem inertia_isConj_inv_of_geometricallyIntegral_residue
    (K : Type) {L : Type} [Field K] [Field L] [Algebra K L]
    [IsGalois K L]
    (V : _root_.ValuationSubring L) [IsDiscreteValuationRing V]
    [CharZero (decompositionResidueField K V)]
    [Finite (inertiaGroup K V)]
    [IsSepClosure (decompositionResidueField K V) (selectedResidueField V)] :
    letI : CharZero (selectedResidueField V) :=
      charZero_of_injective_algebraMap
        (algebraMap (decompositionResidueField K V)
          (selectedResidueField V)).injective
    letI : Algebra ℚ (decompositionResidueField K V) :=
      DivisionRing.toRatAlgebra
    letI : Algebra ℚ (selectedResidueField V) :=
      DivisionRing.toRatAlgebra
    letI : IsScalarTower ℚ (decompositionResidueField K V)
        (selectedResidueField V) :=
      IsScalarTower.of_algebraMap_eq fun q => by simp
    AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap ℚ (decompositionResidueField K V)))) →
    ∀ sigma : inertiaGroup K V,
      IsConj (sigma : decompositionGroup K V)
        ((sigma⁻¹ : inertiaGroup K V) : decompositionGroup K V) := by
  intro hgeo
  let : CharZero (selectedResidueField V) :=
    charZero_of_injective_algebraMap
      (algebraMap (decompositionResidueField K V)
        (selectedResidueField V)).injective
  apply inertia_isConj_inv_of_residue_linearDisjoint K V
  exact
    EtaleFundamentalGroups.separableClosure_linearDisjoint_of_geometricallyIntegral

end TameAbhyankar.SGA1
