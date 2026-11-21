/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Topology.AbsoluteGaloisMap
public import Nyll.GaloisCohomology.Kummer.AbsoluteMuNTopRep

/-!
# Prime specializations of the natural roots-of-unity representation

The coefficient objects and Kummer cocycles are the `mu_n` constructions at a prime exponent.
-/

@[expose] public section

open scoped Pointwise Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open CategoryTheory KummerTheory TopRep ContRepresentation groupCohomology

variable (K : Type*) [Field K]
variable (p : ℕ)

/-- The prime specialization of `AbsoluteMuN`. -/
abbrev AbsoluteMuP :=
  AbsoluteMuN K p

/-- The prime specialization of `absoluteMuN_nsmul_eq_zero`. -/
theorem absoluteMuP_nsmul_eq_zero (x : AbsoluteMuP K p) : p • x = 0 :=
  absoluteMuN_nsmul_eq_zero K p x

/-- The prime specialization of `absoluteMuNModule`. -/
noncomputable abbrev absoluteMuPModule : Module (ZMod p) (AbsoluteMuP K p) :=
  absoluteMuNModule K p

/-- The prime specialization of `absoluteMuNContinuousSMul`. -/
abbrev absoluteMuPContinuousSMul : ContinuousSMul (ZMod p) (AbsoluteMuP K p) :=
  absoluteMuNContinuousSMul K p

/-- The prime specialization of `absoluteMuNActionAddHom`. -/
def absoluteMuPActionAddHom (sigma : Field.absoluteGaloisGroup K) :
    AbsoluteMuP K p →+ AbsoluteMuP K p :=
  absoluteMuNActionAddHom K p sigma

/-- The prime specialization of `absoluteMuNActionAddHom_apply_coe`. -/
@[simp]
theorem absoluteMuPActionAddHom_apply_coe
    (sigma : Field.absoluteGaloisGroup K) (x : AbsoluteMuP K p) :
    (absoluteMuPActionAddHom K p sigma x).toMul.1 =
    (absoluteGaloisGroupContinuousMulEquiv K sigma) • x.toMul.1 :=
  absoluteMuNActionAddHom_apply_coe K p sigma x

/-- The prime specialization of `absoluteMuNActionContinuousLinearMap`. -/
def absoluteMuPActionContinuousLinearMap (sigma : Field.absoluteGaloisGroup K) :
    AbsoluteMuP K p →L[ZMod p] AbsoluteMuP K p :=
  absoluteMuNActionContinuousLinearMap K p sigma

/-- The prime specialization of `absoluteMuNActionContinuousLinearMap_apply`. -/
@[simp]
theorem absoluteMuPActionContinuousLinearMap_apply
    (sigma : Field.absoluteGaloisGroup K) (x : AbsoluteMuP K p) :
    absoluteMuPActionContinuousLinearMap K p sigma x =
      absoluteMuPActionAddHom K p sigma x :=
  absoluteMuNActionContinuousLinearMap_apply K p sigma x

/-- The prime specialization of `absoluteMuNContRepresentation`. -/
def absoluteMuPContRepresentation :
    ContRepresentation (ZMod p) (Field.absoluteGaloisGroup K) (AbsoluteMuP K p) :=
  absoluteMuNContRepresentation K p

/-- The prime specialization of `absoluteMuNTopRep`. -/
def absoluteMuPTopRep :
    TopRep (ZMod p) (Field.absoluteGaloisGroup K) :=
  absoluteMuNTopRep K p

variable [Fact p.Prime]

/-- A prime exponent as a positive natural number. -/
abbrev primePNat : ℕ+ :=
  p.toPNat (Fact.out : p.Prime).pos

/-- The prime specialization of `absoluteKummerMuNChosenRoot`. -/
def absoluteKummerChosenRoot (a : Kˣ) : (AlgebraicClosure K)ˣ :=
  absoluteKummerMuNChosenRoot K (primePNat p) a

/-- The prime specialization of `absoluteKummerMuNChosenRoot_pow`. -/
@[simp]
theorem absoluteKummerChosenRoot_pow (a : Kˣ) :
    absoluteKummerChosenRoot K p a ^ p =
      Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a :=
  absoluteKummerMuNChosenRoot_pow K (primePNat p) a

/-- The prime specialization of `absoluteKummerMuNRootCocycle`. -/
def absoluteKummerMuPRootCocycle (a : Kˣ)
    (sigma : Field.absoluteGaloisGroup K) : AbsoluteMuP K p :=
  absoluteKummerMuNRootCocycle K (primePNat p) a sigma

/-- The prime specialization of `absoluteKummerMuNRootCocycle_apply_coe`. -/
@[simp]
theorem absoluteKummerMuPRootCocycle_apply_coe
    (a : Kˣ) (sigma : Field.absoluteGaloisGroup K) :
    (absoluteKummerMuPRootCocycle K p a sigma).toMul.1 =
      absoluteGaloisGroupContinuousMulEquiv K sigma •
          absoluteKummerChosenRoot K p a /
        absoluteKummerChosenRoot K p a :=
  absoluteKummerMuNRootCocycle_apply_coe K (primePNat p) a sigma

/-- The prime specialization of `absoluteKummerMuNRootCocycle_mul`. -/
theorem absoluteKummerMuPRootCocycle_mul
    (a : Kˣ) (sigma tau : Field.absoluteGaloisGroup K) :
    absoluteKummerMuPRootCocycle K p a (sigma * tau) =
      absoluteMuPActionContinuousLinearMap K p sigma
          (absoluteKummerMuPRootCocycle K p a tau) +
        absoluteKummerMuPRootCocycle K p a sigma :=
  absoluteKummerMuNRootCocycle_mul K (primePNat p) a sigma tau

/-- The prime specialization of `absoluteKummerMuNRootCocycle_isLocallyConstant`. -/
theorem absoluteKummerMuPRootCocycle_isLocallyConstant (a : Kˣ) :
    IsLocallyConstant (absoluteKummerMuPRootCocycle K p a) :=
  absoluteKummerMuNRootCocycle_isLocallyConstant K (primePNat p) a

/-- The prime specialization of `absoluteKummerMuNRootCocycle_continuous`. -/
theorem absoluteKummerMuPRootCocycle_continuous (a : Kˣ) :
    Continuous (absoluteKummerMuPRootCocycle K p a) :=
  absoluteKummerMuNRootCocycle_continuous K (primePNat p) a

/-- The prime specialization of `absoluteKummerMuNRootCocycleContinuousMap`. -/
def absoluteKummerMuPRootCocycleContinuousMap (a : Kˣ) :
    C(Field.absoluteGaloisGroup K, AbsoluteMuP K p) :=
  absoluteKummerMuNRootCocycleContinuousMap K (primePNat p) a

/-- The prime specialization of `absoluteKummerMuNHomogeneousOneCochain`. -/
def absoluteKummerMuPHomogeneousOneCochain (a : Kˣ) :
    (TopRep.homogeneousCochains (absoluteMuPTopRep K p)).X 1 :=
  absoluteKummerMuNHomogeneousOneCochain K (primePNat p) a

/-- The prime specialization of `absoluteKummerMuNHomogeneousOneCochain_apply`. -/
@[simp]
theorem absoluteKummerMuPHomogeneousOneCochain_apply
    (a : Kˣ) (g h : Field.absoluteGaloisGroup K) :
    (absoluteKummerMuPHomogeneousOneCochain K p a).1 g h =
      absoluteKummerMuPRootCocycle K p a h -
        absoluteKummerMuPRootCocycle K p a g :=
  absoluteKummerMuNHomogeneousOneCochain_apply K (primePNat p) a g h

/-- The prime specialization of `absoluteKummerMuNHomogeneousOneCochain_eq_action`. -/
theorem absoluteKummerMuPHomogeneousOneCochain_eq_action
    (a : Kˣ) (g h : Field.absoluteGaloisGroup K) :
    (absoluteKummerMuPHomogeneousOneCochain K p a).1 g h =
      absoluteMuPActionContinuousLinearMap K p g
        (absoluteKummerMuPRootCocycle K p a (g⁻¹ * h)) :=
  absoluteKummerMuNHomogeneousOneCochain_eq_action K (primePNat p) a g h

/-- The prime specialization of `absoluteKummerMuNHomogeneousOneCochain_mem_cycles`. -/
theorem absoluteKummerMuPHomogeneousOneCochain_mem_cycles (a : Kˣ) :
    ((TopRep.homogeneousCochains (absoluteMuPTopRep K p)).d 1 2).hom
      (absoluteKummerMuPHomogeneousOneCochain K p a) = 0 :=
  absoluteKummerMuNHomogeneousOneCochain_mem_cycles K (primePNat p) a

/-- The prime specialization of `absoluteKummerMuNHomogeneousOneCocycle`. -/
noncomputable def absoluteKummerMuPHomogeneousOneCocycle (a : Kˣ) :
    ContinuousCohomology.cocycles (absoluteMuPTopRep K p) 1 :=
  absoluteKummerMuNHomogeneousOneCocycle K (primePNat p) a

/-- The prime specialization of `iCycles_absoluteKummerMuNHomogeneousOneCocycle`. -/
@[simp]
theorem iCycles_absoluteKummerMuPHomogeneousOneCocycle (a : Kˣ) :
    (TopRep.homogeneousCochains (absoluteMuPTopRep K p)).iCycles 1
        (absoluteKummerMuPHomogeneousOneCocycle K p a) =
      absoluteKummerMuPHomogeneousOneCochain K p a :=
  iCycles_absoluteKummerMuNHomogeneousOneCocycle K (primePNat p) a

/-- The prime specialization of `absoluteKummerMuNH1Class`. -/
noncomputable def absoluteKummerMuPH1Class (a : Kˣ) :
    continuousCohomology 1 (absoluteMuPTopRep K p) :=
  absoluteKummerMuNH1Class K (primePNat p) a

end ClassFieldTower.Martinet.Shafarevich
