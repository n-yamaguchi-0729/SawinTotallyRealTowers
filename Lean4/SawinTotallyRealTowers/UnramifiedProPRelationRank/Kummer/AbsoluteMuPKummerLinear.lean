/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep

set_option autoImplicit false
/-!
# Linear Kummer classes with natural `mu_p` coefficients

This file descends the continuous absolute Kummer class with its natural
Galois action from field units to `p`-power classes.
-/

open scoped Pointwise Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open CategoryTheory KummerTheory TopRep ContRepresentation

variable (K : Type*) [Field K] [CharZero K]
variable (p : ℕ) [Fact p.Prime]

/-- The orbit map of a `p`-th root of unity under the absolute Galois group is
locally constant. -/
theorem absoluteMuP_orbit_isLocallyConstant (x : AbsoluteMuP K p) :
    IsLocallyConstant
      (fun sigma : Field.absoluteGaloisGroup K ↦
        absoluteMuPActionContinuousLinearMap K p sigma x) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro sigma
  let alpha : AlgebraicClosure K := x.toMul.1
  let E := FiniteGaloisIntermediateField.adjoin K {alpha}
  let e := absoluteGaloisGroupContinuousMulEquiv K
  let H : Set Gal(AlgebraicClosure K/K) := E.fixingSubgroup
  refine ⟨e ⁻¹' (e sigma • H), ?_, ?_, ?_⟩
  · exact ((IntermediateField.fixingSubgroup_isOpen E.toIntermediateField).leftCoset
      (e sigma)).preimage e.continuous
  · change e sigma ∈ e sigma • H
    exact ⟨1, E.fixingSubgroup.one_mem, mul_one (e sigma)⟩
  · intro tau htau
    change e tau ∈ e sigma • H at htau
    rcases htau with ⟨h, hh, htau⟩
    have hfix : h alpha = alpha :=
      ((IntermediateField.mem_fixingSubgroup_iff E.toIntermediateField h).mp hh)
        alpha
        (FiniteGaloisIntermediateField.subset_adjoin K {alpha}
          (Set.mem_singleton alpha))
    have hfixUnit : h • x.toMul.1 = x.toMul.1 := by
      apply Units.ext
      exact hfix
    apply Additive.toMul.injective
    apply Subtype.ext
    change e tau • x.toMul.1 = e sigma • x.toMul.1
    change e sigma * h = e tau at htau
    rw [← htau, mul_smul, hfixUnit]

/-- The orbit map of a root of unity, packaged as a homogeneous zero-cochain. -/
def absoluteMuPHomogeneousZeroCochain (x : AbsoluteMuP K p) :
    (TopRep.homogeneousCochains (absoluteMuPTopRep K p)).X 0 := by
  let c : C(Field.absoluteGaloisGroup K, AbsoluteMuP K p) :=
    ⟨fun sigma ↦ absoluteMuPActionContinuousLinearMap K p sigma x,
      (absoluteMuP_orbit_isLocallyConstant K p x).continuous⟩
  exact ⟨c, by
    intro tau
    apply ContinuousMap.ext
    intro sigma
    change absoluteMuPActionContinuousLinearMap K p tau
        (absoluteMuPActionContinuousLinearMap K p (tau⁻¹ * sigma) x) =
      absoluteMuPActionContinuousLinearMap K p sigma x
    apply Additive.toMul.injective
    apply Subtype.ext
    change (absoluteGaloisGroupContinuousMulEquiv K tau) •
        ((absoluteGaloisGroupContinuousMulEquiv K (tau⁻¹ * sigma)) • x.toMul.1) =
      (absoluteGaloisGroupContinuousMulEquiv K sigma) • x.toMul.1
    rw [← mul_smul]
    congr 1
    simp⟩

@[simp]
theorem absoluteMuPHomogeneousZeroCochain_boundary_apply
    (x : AbsoluteMuP K p)
    (g h : Field.absoluteGaloisGroup K) :
    (((TopRep.homogeneousCochains (absoluteMuPTopRep K p)).d 0 1).hom
        (absoluteMuPHomogeneousZeroCochain K p x)).1 g h =
      absoluteMuPActionContinuousLinearMap K p h x -
        absoluteMuPActionContinuousLinearMap K p g x := by
  have hd := TopRep.homogeneousCochains.d_apply
    (absoluteMuPTopRep K p) 0
      (absoluteMuPHomogeneousZeroCochain K p x)
  have hdh := congrArg (fun tau ↦ tau g h) hd
  rw [hdh]
  simp [TopRep.d_succ, TopRep.d_zero, TopRep.hom_sub,
    absoluteMuPHomogeneousZeroCochain]
  rfl

/-- The root-of-unity correction comparing the chosen root of a product with
the product of the chosen roots. -/
def absoluteKummerMuPMulCorrection (a b : Kˣ) : AbsoluteMuP K p :=
  Additive.ofMul
    ⟨absoluteKummerChosenRoot K p (a * b) /
        (absoluteKummerChosenRoot K p a * absoluteKummerChosenRoot K p b), by
      change absoluteKummerChosenRoot K p (a * b) /
          (absoluteKummerChosenRoot K p a * absoluteKummerChosenRoot K p b) ∈
        nthRootsSubgroup (AlgebraicClosure K) p
      apply div_mem_nthRootsSubgroup_of_pow_eq_pow
      rw [mul_pow, absoluteKummerChosenRoot_pow,
        absoluteKummerChosenRoot_pow, absoluteKummerChosenRoot_pow, map_mul]⟩

omit [CharZero K] in
/-- Evaluation of the multiplicativity correction in the ambient unit group. -/
@[simp]
theorem absoluteKummerMuPMulCorrection_apply_coe (a b : Kˣ) :
    (absoluteKummerMuPMulCorrection K p a b).toMul.1 =
      absoluteKummerChosenRoot K p (a * b) /
        (absoluteKummerChosenRoot K p a * absoluteKummerChosenRoot K p b) :=
  rfl

omit [CharZero K] in
/-- The failure of the chosen root cocycle to preserve products is the
principal cocycle attached to the root-of-unity correction. -/
theorem absoluteKummerMuPRootCocycle_mul_sub
    (a b : Kˣ) (sigma : Field.absoluteGaloisGroup K) :
    absoluteKummerMuPRootCocycle K p (a * b) sigma -
          absoluteKummerMuPRootCocycle K p a sigma -
        absoluteKummerMuPRootCocycle K p b sigma =
      absoluteMuPActionContinuousLinearMap K p sigma
          (absoluteKummerMuPMulCorrection K p a b) -
        absoluteKummerMuPMulCorrection K p a b := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change
    rootQuotient (K := K) (L := AlgebraicClosure K)
          (absoluteKummerChosenRoot K p (a * b))
          (absoluteGaloisGroupContinuousMulEquiv K sigma) /
        rootQuotient (K := K) (L := AlgebraicClosure K)
          (absoluteKummerChosenRoot K p a)
          (absoluteGaloisGroupContinuousMulEquiv K sigma) /
      rootQuotient (K := K) (L := AlgebraicClosure K)
          (absoluteKummerChosenRoot K p b)
          (absoluteGaloisGroupContinuousMulEquiv K sigma) =
    rootQuotient (K := K) (L := AlgebraicClosure K)
      (absoluteKummerChosenRoot K p (a * b) /
        (absoluteKummerChosenRoot K p a *
          absoluteKummerChosenRoot K p b))
      (absoluteGaloisGroupContinuousMulEquiv K sigma)
  rw [rootQuotient_div, rootQuotient_mul_root]
  simp [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- At the homogeneous-cochain level, the product discrepancy is the
boundary of the root-of-unity correction. -/
theorem absoluteKummerMuPHomogeneousOneCochain_mul_sub_boundary
    (a b : Kˣ) :
    absoluteKummerMuPHomogeneousOneCochain K p (a * b) -
          (absoluteKummerMuPHomogeneousOneCochain K p a +
            absoluteKummerMuPHomogeneousOneCochain K p b) =
      ((TopRep.homogeneousCochains (absoluteMuPTopRep K p)).d 0 1).hom
        (absoluteMuPHomogeneousZeroCochain K p
          (absoluteKummerMuPMulCorrection K p a b)) := by
  apply Subtype.ext
  ext g h
  rw [absoluteMuPHomogeneousZeroCochain_boundary_apply]
  calc
    (absoluteKummerMuPRootCocycle K p (a * b) h -
          absoluteKummerMuPRootCocycle K p (a * b) g) -
        ((absoluteKummerMuPRootCocycle K p a h -
            absoluteKummerMuPRootCocycle K p a g) +
          (absoluteKummerMuPRootCocycle K p b h -
            absoluteKummerMuPRootCocycle K p b g)) =
      (absoluteKummerMuPRootCocycle K p (a * b) h -
            absoluteKummerMuPRootCocycle K p a h -
          absoluteKummerMuPRootCocycle K p b h) -
        (absoluteKummerMuPRootCocycle K p (a * b) g -
            absoluteKummerMuPRootCocycle K p a g -
          absoluteKummerMuPRootCocycle K p b g) := by abel
    _ = (absoluteMuPActionContinuousLinearMap K p h
              (absoluteKummerMuPMulCorrection K p a b) -
            absoluteKummerMuPMulCorrection K p a b) -
          (absoluteMuPActionContinuousLinearMap K p g
              (absoluteKummerMuPMulCorrection K p a b) -
            absoluteKummerMuPMulCorrection K p a b) := by
      rw [absoluteKummerMuPRootCocycle_mul_sub,
        absoluteKummerMuPRootCocycle_mul_sub]
    _ = absoluteMuPActionContinuousLinearMap K p h
            (absoluteKummerMuPMulCorrection K p a b) -
          absoluteMuPActionContinuousLinearMap K p g
            (absoluteKummerMuPMulCorrection K p a b) := by abel

/-- The difference of the product cocycle and the sum of its factors is the
corresponding homogeneous boundary. -/
theorem absoluteKummerMuPHomogeneousOneCocycle_mul_sub_boundary
    (a b : Kˣ) :
    absoluteKummerMuPHomogeneousOneCocycle K p (a * b) -
          (absoluteKummerMuPHomogeneousOneCocycle K p a +
            absoluteKummerMuPHomogeneousOneCocycle K p b) =
      ((TopRep.homogeneousCochains (absoluteMuPTopRep K p)).toCycles 0 1).hom
        (absoluteMuPHomogeneousZeroCochain K p
          (absoluteKummerMuPMulCorrection K p a b)) := by
  let C := TopRep.homogeneousCochains (absoluteMuPTopRep K p)
  let F := forget₂ (TopModuleCat (ZMod p)) (ModuleCat (ZMod p))
  apply (ModuleCat.mono_iff_injective (F.map (C.iCycles 1))).1 inferInstance
  change (C.iCycles 1).hom _ = (C.iCycles 1).hom _
  calc
    (C.iCycles 1).hom
        (absoluteKummerMuPHomogeneousOneCocycle K p (a * b) -
          (absoluteKummerMuPHomogeneousOneCocycle K p a +
            absoluteKummerMuPHomogeneousOneCocycle K p b)) =
      absoluteKummerMuPHomogeneousOneCochain K p (a * b) -
        (absoluteKummerMuPHomogeneousOneCochain K p a +
          absoluteKummerMuPHomogeneousOneCochain K p b) := by
      rw [map_sub, map_add,
        iCycles_absoluteKummerMuPHomogeneousOneCocycle,
        iCycles_absoluteKummerMuPHomogeneousOneCocycle,
        iCycles_absoluteKummerMuPHomogeneousOneCocycle]
    _ = (C.d 0 1).hom
        (absoluteMuPHomogeneousZeroCochain K p
          (absoluteKummerMuPMulCorrection K p a b)) :=
      absoluteKummerMuPHomogeneousOneCochain_mul_sub_boundary K p a b
    _ = (C.iCycles 1).hom
        ((C.toCycles 0 1).hom
          (absoluteMuPHomogeneousZeroCochain K p
            (absoluteKummerMuPMulCorrection K p a b))) := by
      symm
      exact ConcreteCategory.congr_hom (C.toCycles_i 0 1)
        (absoluteMuPHomogeneousZeroCochain K p
          (absoluteKummerMuPMulCorrection K p a b))

/-- Absolute Kummer classes with natural `mu_p` coefficients preserve
multiplication of radicands. -/
theorem absoluteKummerMuPH1Class_mul (a b : Kˣ) :
    absoluteKummerMuPH1Class K p (a * b) =
      absoluteKummerMuPH1Class K p a +
        absoluteKummerMuPH1Class K p b := by
  let A := absoluteMuPTopRep K p
  let C := TopRep.homogeneousCochains A
  change ContinuousCohomology.π A 1
      (absoluteKummerMuPHomogeneousOneCocycle K p (a * b)) =
    ContinuousCohomology.π A 1
        (absoluteKummerMuPHomogeneousOneCocycle K p a) +
      ContinuousCohomology.π A 1
        (absoluteKummerMuPHomogeneousOneCocycle K p b)
  rw [← map_add, ← sub_eq_zero, ← map_sub]
  rw [absoluteKummerMuPHomogeneousOneCocycle_mul_sub_boundary]
  exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 0 1)
    (absoluteMuPHomogeneousZeroCochain K p
      (absoluteKummerMuPMulCorrection K p a b))

/-- Natural-coefficient absolute Kummer theory as a linear map from
`p`-power classes to continuous `H¹`. -/
noncomputable def absoluteKummerMuPH1LinearMap :
    absolutePowerClassModP K p →ₗ[ZMod p]
      continuousCohomology 1 (absoluteMuPTopRep K p) := by
  letI : Module (ZMod p)
      (Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range)) :=
    additiveZModModuleOfPowEqOne p
      (absolutePowerClassQuotient_pow_eq_one K p)
  let chi : Kˣ →*
      Multiplicative
        (continuousCohomology 1 (absoluteMuPTopRep K p)) :=
    { toFun := fun a ↦ Multiplicative.ofAdd
        (absoluteKummerMuPH1Class K p a)
      map_one' := by
        apply Multiplicative.toAdd.injective
        change absoluteKummerMuPH1Class K p 1 = 0
        have h := absoluteKummerMuPH1Class_mul K p (1 : Kˣ) 1
        simp only [one_mul] at h
        calc
          absoluteKummerMuPH1Class K p 1 =
              (absoluteKummerMuPH1Class K p 1 +
                absoluteKummerMuPH1Class K p 1) -
                  absoluteKummerMuPH1Class K p 1 := by abel
          _ = absoluteKummerMuPH1Class K p 1 -
                absoluteKummerMuPH1Class K p 1 := by rw [← h]
          _ = 0 := sub_self _
      map_mul' := by
        intro a b
        apply Multiplicative.toAdd.injective
        exact absoluteKummerMuPH1Class_mul K p a b }
  let chiQuotient :
      (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →*
        Multiplicative
          (continuousCohomology 1 (absoluteMuPTopRep K p)) :=
    QuotientGroup.lift _ chi <| by
      rintro _ ⟨a, rfl⟩
      rw [MonoidHom.mem_ker]
      change chi (a ^ p) = 1
      rw [map_pow]
      apply Multiplicative.toAdd.injective
      change p • absoluteKummerMuPH1Class K p a = 0
      rw [← Nat.cast_smul_eq_nsmul (ZMod p)]
      simp
  let f :
      Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →+
        continuousCohomology 1 (absoluteMuPTopRep K p) :=
    { toFun := fun x ↦ (chiQuotient (Additive.toMul x)).toAdd
      map_zero' := by
        change (chiQuotient 1).toAdd = 0
        rw [map_one]
        rfl
      map_add' := by
        intro x y
        change (chiQuotient
          (Additive.toMul x * Additive.toMul y)).toAdd = _
        rw [map_mul]
        rfl }
  exact f.toZModLinearMap p

/-- Evaluation of the natural-coefficient Kummer linear map on a represented
power class recovers the previously constructed continuous `H¹` class. -/
@[simp]
theorem absoluteKummerMuPH1LinearMap_mk (a : Kˣ) :
    absoluteKummerMuPH1LinearMap K p
        (Additive.ofMul
          (QuotientGroup.mk'
            (powMonoidHom p : Kˣ →* Kˣ).range a)) =
      absoluteKummerMuPH1Class K p a := by
  simp [absoluteKummerMuPH1LinearMap]
  rfl

end ClassFieldTower.Martinet.Shafarevich
