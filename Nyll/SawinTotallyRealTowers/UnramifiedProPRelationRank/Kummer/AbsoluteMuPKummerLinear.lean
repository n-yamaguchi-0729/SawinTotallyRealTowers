/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.AbsoluteMuNKummerLinear
public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTopRep
public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteKummerH1Linear

/-!
# Linear Kummer classes with natural `mu_p` coefficients

This file descends the continuous absolute Kummer class with its natural
Galois action from field units to `p`-power classes.
-/

@[expose] public section

open scoped Pointwise Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open CategoryTheory KummerTheory TopRep ContRepresentation

variable (K : Type*) [Field K] [CharZero K]
variable (p : ℕ) [Fact p.Prime]

omit [CharZero K] [Fact p.Prime] in
/-- The orbit map of a `p`-th root of unity under the absolute Galois group is
locally constant. -/
theorem absoluteMuP_orbit_isLocallyConstant (x : AbsoluteMuP K p) :
    IsLocallyConstant
      (fun sigma : Field.absoluteGaloisGroup K ↦
        absoluteMuPActionContinuousLinearMap K p sigma x) :=
  absoluteMuNAction_isLocallyConstant K p x

/-- The orbit map of a root of unity, packaged as a homogeneous zero-cochain. -/
noncomputable def absoluteMuPHomogeneousZeroCochain (x : AbsoluteMuP K p) :
    (TopRep.homogeneousCochains (absoluteMuPTopRep K p)).X 0 :=
  absoluteMuNHomogeneousZeroCochain K p x

omit [Fact p.Prime] in
omit [CharZero K] in
@[simp]
theorem absoluteMuPHomogeneousZeroCochain_boundary_apply
    (x : AbsoluteMuP K p)
    (g h : Field.absoluteGaloisGroup K) :
    (((TopRep.homogeneousCochains (absoluteMuPTopRep K p)).d 0 1).hom
        (absoluteMuPHomogeneousZeroCochain K p x)).1 g h =
      absoluteMuPActionContinuousLinearMap K p h x -
        absoluteMuPActionContinuousLinearMap K p g x :=
  absoluteMuNHomogeneousZeroCochain_boundary_apply K p x g h

/-- The root-of-unity correction comparing the chosen root of a product with
the product of the chosen roots. -/
noncomputable def absoluteKummerMuPMulCorrection (a b : Kˣ) : AbsoluteMuP K p :=
  absoluteKummerMuNMulCorrection K (primePNat p) a b

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
        absoluteKummerMuPMulCorrection K p a b :=
  absoluteKummerMuNRootCocycle_mul_sub K (primePNat p) a b sigma

omit [CharZero K] in
/-- At the homogeneous-cochain level, the product discrepancy is the
boundary of the root-of-unity correction. -/
theorem absoluteKummerMuPHomogeneousOneCochain_mul_sub_boundary
    (a b : Kˣ) :
    absoluteKummerMuPHomogeneousOneCochain K p (a * b) -
          (absoluteKummerMuPHomogeneousOneCochain K p a +
            absoluteKummerMuPHomogeneousOneCochain K p b) =
      ((TopRep.homogeneousCochains (absoluteMuPTopRep K p)).d 0 1).hom
        (absoluteMuPHomogeneousZeroCochain K p
          (absoluteKummerMuPMulCorrection K p a b)) :=
  absoluteKummerMuNHomogeneousOneCochain_mul_sub_boundary K (primePNat p) a b

omit [CharZero K] in
/-- The difference of the product cocycle and the sum of its factors is the
corresponding homogeneous boundary. -/
theorem absoluteKummerMuPHomogeneousOneCocycle_mul_sub_boundary
    (a b : Kˣ) :
    absoluteKummerMuPHomogeneousOneCocycle K p (a * b) -
          (absoluteKummerMuPHomogeneousOneCocycle K p a +
            absoluteKummerMuPHomogeneousOneCocycle K p b) =
      ((TopRep.homogeneousCochains (absoluteMuPTopRep K p)).toCycles 0 1).hom
        (absoluteMuPHomogeneousZeroCochain K p
          (absoluteKummerMuPMulCorrection K p a b)) :=
  absoluteKummerMuNHomogeneousOneCocycle_mul_sub_boundary K (primePNat p) a b

omit [CharZero K] in
/-- Absolute Kummer classes with natural `mu_p` coefficients preserve
multiplication of radicands. -/
theorem absoluteKummerMuPH1Class_mul (a b : Kˣ) :
    absoluteKummerMuPH1Class K p (a * b) =
      absoluteKummerMuPH1Class K p a +
        absoluteKummerMuPH1Class K p b :=
  absoluteKummerMuNH1Class_mul K (primePNat p) a b

/-- Natural-coefficient absolute Kummer theory as a linear map from
`p`-power classes to continuous `H¹`. -/
noncomputable def absoluteKummerMuPH1LinearMap :
    absolutePowerClassModP K p →ₗ[ZMod p]
      continuousCohomology 1 (absoluteMuPTopRep K p) := by
  letI : Module (ZMod p)
      (Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range)) :=
    additiveZModModuleOfPowEqOne p
      (absolutePowerClassQuotient_pow_eq_one K p)
  let chiQuotient := absoluteKummerMuNPowerClassHom K (primePNat p)
  let f :
      Additive (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) →+
        continuousCohomology 1 (absoluteMuPTopRep K p) :=
    { toFun := fun x ↦ (chiQuotient (Additive.toMul x)).toAdd
      map_zero' := by
        exact congrArg Multiplicative.toAdd chiQuotient.map_one
      map_add' := by
        intro x y
        exact congrArg Multiplicative.toAdd
          (chiQuotient.map_mul (Additive.toMul x) (Additive.toMul y)) }
  exact f.toZModLinearMap p

omit [CharZero K] in
/-- Evaluation of the natural-coefficient Kummer linear map on a represented
power class recovers the previously constructed continuous `H¹` class. -/
@[simp]
theorem absoluteKummerMuPH1LinearMap_mk (a : Kˣ) :
    absoluteKummerMuPH1LinearMap K p
        (Additive.ofMul
          (QuotientGroup.mk'
            (powMonoidHom p : Kˣ →* Kˣ).range a)) =
      absoluteKummerMuPH1Class K p a := by
  rfl

end ClassFieldTower.Martinet.Shafarevich
