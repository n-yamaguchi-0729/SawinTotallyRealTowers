/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.AbsoluteMuNTopRep
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Absolute Kummer classes on power quotients

The natural Kummer cocycles give a homomorphism from the actual group of
power classes to continuous cohomology with the natural roots-of-unity action.
-/

@[expose] public section

open scoped Pointwise Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open CategoryTheory KummerTheory TopRep ContRepresentation

variable (K : Type*) [Field K]

section ZeroCochain

variable (n : ℕ)

/-- The orbit map of a root of unity, packaged as a homogeneous zero-cochain. -/
noncomputable def absoluteMuNHomogeneousZeroCochain (x : AbsoluteMuN K n) :
    (TopRep.homogeneousCochains (absoluteMuNTopRep K n)).X 0 := by
  let c : C(Field.absoluteGaloisGroup K, AbsoluteMuN K n) :=
    ⟨fun sigma ↦ absoluteMuNActionContinuousLinearMap K n sigma x,
      (absoluteMuNAction_isLocallyConstant K n x).continuous⟩
  exact ⟨c, by
    intro tau
    apply ContinuousMap.ext
    intro sigma
    change absoluteMuNActionContinuousLinearMap K n tau
        (absoluteMuNActionContinuousLinearMap K n (tau⁻¹ * sigma) x) =
      absoluteMuNActionContinuousLinearMap K n sigma x
    apply Additive.toMul.injective
    apply Subtype.ext
    change (absoluteGaloisGroupContinuousMulEquiv K tau) •
        ((absoluteGaloisGroupContinuousMulEquiv K (tau⁻¹ * sigma)) • x.toMul.1) =
      (absoluteGaloisGroupContinuousMulEquiv K sigma) • x.toMul.1
    rw [← mul_smul]
    congr 1
    rw [← map_mul, mul_inv_cancel_left]⟩

@[simp]
theorem absoluteMuNHomogeneousZeroCochain_boundary_apply
    (x : AbsoluteMuN K n)
    (g h : Field.absoluteGaloisGroup K) :
    (((TopRep.homogeneousCochains (absoluteMuNTopRep K n)).d 0 1).hom
        (absoluteMuNHomogeneousZeroCochain K n x)).1 g h =
      absoluteMuNActionContinuousLinearMap K n h x -
        absoluteMuNActionContinuousLinearMap K n g x := by
  have hd := TopRep.homogeneousCochains.d_apply
    (absoluteMuNTopRep K n) 0
      (absoluteMuNHomogeneousZeroCochain K n x)
  have hdh := congrArg (fun tau ↦ tau g h) hd
  rw [hdh]
  rfl

end ZeroCochain

variable (n : ℕ+)

/-- The root-of-unity correction comparing the chosen root of a product with
the product of the chosen roots. -/
noncomputable def absoluteKummerMuNMulCorrection (a b : Kˣ) : AbsoluteMuN K (n : ℕ) :=
  Additive.ofMul
    ⟨absoluteKummerMuNChosenRoot K n (a * b) /
        (absoluteKummerMuNChosenRoot K n a * absoluteKummerMuNChosenRoot K n b), by
      change absoluteKummerMuNChosenRoot K n (a * b) /
          (absoluteKummerMuNChosenRoot K n a * absoluteKummerMuNChosenRoot K n b) ∈
        nthRootsSubgroup (AlgebraicClosure K) (n : ℕ)
      apply div_mem_nthRootsSubgroup_of_pow_eq_pow
      rw [mul_pow, absoluteKummerMuNChosenRoot_pow,
        absoluteKummerMuNChosenRoot_pow, absoluteKummerMuNChosenRoot_pow, map_mul]⟩

/-- Evaluation of the multiplicativity correction in the ambient unit group. -/
@[simp]
theorem absoluteKummerMuNMulCorrection_apply_coe (a b : Kˣ) :
    (absoluteKummerMuNMulCorrection K n a b).toMul.1 =
      absoluteKummerMuNChosenRoot K n (a * b) /
        (absoluteKummerMuNChosenRoot K n a * absoluteKummerMuNChosenRoot K n b) :=
  rfl

/-- The failure of the chosen root cocycle to preserve products is the
principal cocycle attached to the root-of-unity correction. -/
theorem absoluteKummerMuNRootCocycle_mul_sub
    (a b : Kˣ) (sigma : Field.absoluteGaloisGroup K) :
    absoluteKummerMuNRootCocycle K n (a * b) sigma -
          absoluteKummerMuNRootCocycle K n a sigma -
        absoluteKummerMuNRootCocycle K n b sigma =
      absoluteMuNActionContinuousLinearMap K (n : ℕ) sigma
          (absoluteKummerMuNMulCorrection K n a b) -
        absoluteKummerMuNMulCorrection K n a b := by
  apply Additive.toMul.injective
  apply Subtype.ext
  change
    rootQuotient (K := K) (L := AlgebraicClosure K)
          (absoluteKummerMuNChosenRoot K n (a * b))
          (absoluteGaloisGroupContinuousMulEquiv K sigma) /
        rootQuotient (K := K) (L := AlgebraicClosure K)
          (absoluteKummerMuNChosenRoot K n a)
          (absoluteGaloisGroupContinuousMulEquiv K sigma) /
      rootQuotient (K := K) (L := AlgebraicClosure K)
          (absoluteKummerMuNChosenRoot K n b)
          (absoluteGaloisGroupContinuousMulEquiv K sigma) =
    rootQuotient (K := K) (L := AlgebraicClosure K)
      (absoluteKummerMuNChosenRoot K n (a * b) /
        (absoluteKummerMuNChosenRoot K n a *
          absoluteKummerMuNChosenRoot K n b))
      (absoluteGaloisGroupContinuousMulEquiv K sigma)
  rw [rootQuotient_div, rootQuotient_mul_root]
  rw [div_div]

/-- At the homogeneous-cochain level, the product discrepancy is the
boundary of the root-of-unity correction. -/
theorem absoluteKummerMuNHomogeneousOneCochain_mul_sub_boundary
    (a b : Kˣ) :
    absoluteKummerMuNHomogeneousOneCochain K n (a * b) -
          (absoluteKummerMuNHomogeneousOneCochain K n a +
            absoluteKummerMuNHomogeneousOneCochain K n b) =
      ((TopRep.homogeneousCochains (absoluteMuNTopRep K (n : ℕ))).d 0 1).hom
        (absoluteMuNHomogeneousZeroCochain K n
          (absoluteKummerMuNMulCorrection K n a b)) := by
  apply Subtype.ext
  ext g h
  rw [absoluteMuNHomogeneousZeroCochain_boundary_apply]
  calc
    (absoluteKummerMuNRootCocycle K n (a * b) h -
          absoluteKummerMuNRootCocycle K n (a * b) g) -
        ((absoluteKummerMuNRootCocycle K n a h -
            absoluteKummerMuNRootCocycle K n a g) +
          (absoluteKummerMuNRootCocycle K n b h -
            absoluteKummerMuNRootCocycle K n b g)) =
      (absoluteKummerMuNRootCocycle K n (a * b) h -
            absoluteKummerMuNRootCocycle K n a h -
          absoluteKummerMuNRootCocycle K n b h) -
        (absoluteKummerMuNRootCocycle K n (a * b) g -
            absoluteKummerMuNRootCocycle K n a g -
          absoluteKummerMuNRootCocycle K n b g) := by abel
    _ = (absoluteMuNActionContinuousLinearMap K (n : ℕ) h
              (absoluteKummerMuNMulCorrection K n a b) -
            absoluteKummerMuNMulCorrection K n a b) -
          (absoluteMuNActionContinuousLinearMap K (n : ℕ) g
              (absoluteKummerMuNMulCorrection K n a b) -
            absoluteKummerMuNMulCorrection K n a b) := by
      rw [absoluteKummerMuNRootCocycle_mul_sub,
        absoluteKummerMuNRootCocycle_mul_sub]
    _ = absoluteMuNActionContinuousLinearMap K (n : ℕ) h
            (absoluteKummerMuNMulCorrection K n a b) -
          absoluteMuNActionContinuousLinearMap K (n : ℕ) g
            (absoluteKummerMuNMulCorrection K n a b) := by abel

/-- The difference of the product cocycle and the sum of its factors is the
corresponding homogeneous boundary. -/
theorem absoluteKummerMuNHomogeneousOneCocycle_mul_sub_boundary
    (a b : Kˣ) :
    absoluteKummerMuNHomogeneousOneCocycle K n (a * b) -
          (absoluteKummerMuNHomogeneousOneCocycle K n a +
            absoluteKummerMuNHomogeneousOneCocycle K n b) =
      ((TopRep.homogeneousCochains (absoluteMuNTopRep K (n : ℕ))).toCycles 0 1).hom
        (absoluteMuNHomogeneousZeroCochain K n
          (absoluteKummerMuNMulCorrection K n a b)) := by
  let C := TopRep.homogeneousCochains (absoluteMuNTopRep K (n : ℕ))
  let F := forget₂ (TopModuleCat (ZMod (n : ℕ))) (ModuleCat (ZMod (n : ℕ)))
  apply (ModuleCat.mono_iff_injective (F.map (C.iCycles 1))).1 inferInstance
  change (C.iCycles 1).hom _ = (C.iCycles 1).hom _
  calc
    (C.iCycles 1).hom
        (absoluteKummerMuNHomogeneousOneCocycle K n (a * b) -
          (absoluteKummerMuNHomogeneousOneCocycle K n a +
            absoluteKummerMuNHomogeneousOneCocycle K n b)) =
      absoluteKummerMuNHomogeneousOneCochain K n (a * b) -
        (absoluteKummerMuNHomogeneousOneCochain K n a +
          absoluteKummerMuNHomogeneousOneCochain K n b) := by
      rw [map_sub, map_add,
        iCycles_absoluteKummerMuNHomogeneousOneCocycle,
        iCycles_absoluteKummerMuNHomogeneousOneCocycle,
        iCycles_absoluteKummerMuNHomogeneousOneCocycle]
    _ = (C.d 0 1).hom
        (absoluteMuNHomogeneousZeroCochain K n
          (absoluteKummerMuNMulCorrection K n a b)) :=
      absoluteKummerMuNHomogeneousOneCochain_mul_sub_boundary K n a b
    _ = (C.iCycles 1).hom
        ((C.toCycles 0 1).hom
          (absoluteMuNHomogeneousZeroCochain K n
            (absoluteKummerMuNMulCorrection K n a b))) := by
      symm
      exact ConcreteCategory.congr_hom (C.toCycles_i 0 1)
        (absoluteMuNHomogeneousZeroCochain K n
          (absoluteKummerMuNMulCorrection K n a b))

/-- Absolute Kummer classes with natural `mu_n` coefficients preserve
multiplication of radicands. -/
theorem absoluteKummerMuNH1Class_mul (a b : Kˣ) :
    absoluteKummerMuNH1Class K n (a * b) =
      absoluteKummerMuNH1Class K n a +
        absoluteKummerMuNH1Class K n b := by
  let A := absoluteMuNTopRep K (n : ℕ)
  let C := TopRep.homogeneousCochains A
  change ContinuousCohomology.π A 1
      (absoluteKummerMuNHomogeneousOneCocycle K n (a * b)) =
    ContinuousCohomology.π A 1
        (absoluteKummerMuNHomogeneousOneCocycle K n a) +
      ContinuousCohomology.π A 1
        (absoluteKummerMuNHomogeneousOneCocycle K n b)
  rw [← map_add, ← sub_eq_zero, ← map_sub]
  rw [absoluteKummerMuNHomogeneousOneCocycle_mul_sub_boundary]
  exact ConcreteCategory.congr_hom (C.toCycles_comp_homologyπ 0 1)
    (absoluteMuNHomogeneousZeroCochain K n
      (absoluteKummerMuNMulCorrection K n a b))

/-- The Kummer class of a unit, as a multiplicative homomorphism. -/
noncomputable def absoluteKummerMuNH1Hom :
    Kˣ →* Multiplicative (continuousCohomology 1 (absoluteMuNTopRep K (n : ℕ))) where
  toFun a := Multiplicative.ofAdd (absoluteKummerMuNH1Class K n a)
  map_one' := by
    apply Multiplicative.toAdd.injective
    change absoluteKummerMuNH1Class K n 1 = 0
    have h := absoluteKummerMuNH1Class_mul K n (1 : Kˣ) 1
    rw [one_mul] at h
    exact add_right_cancel (h.symm.trans (zero_add _).symm)
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    exact absoluteKummerMuNH1Class_mul K n a b

/-- The natural Kummer homomorphism on the actual quotient by `n`-th powers. -/
noncomputable def absoluteKummerMuNPowerClassHom :
    (Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range) →*
      Multiplicative (continuousCohomology 1 (absoluteMuNTopRep K (n : ℕ))) :=
  QuotientGroup.lift _ (absoluteKummerMuNH1Hom K n) <| by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    change absoluteKummerMuNH1Hom K n (a ^ (n : ℕ)) = 1
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    change (n : ℕ) • absoluteKummerMuNH1Class K n a = 0
    rw [← Nat.cast_smul_eq_nsmul (ZMod (n : ℕ)), ZMod.natCast_self, zero_smul]

@[simp]
theorem absoluteKummerMuNPowerClassHom_mk (a : Kˣ) :
    (absoluteKummerMuNPowerClassHom K n
      (QuotientGroup.mk' (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range a)).toAdd =
        absoluteKummerMuNH1Class K n a :=
  rfl

end ClassFieldTower.Martinet.Shafarevich
