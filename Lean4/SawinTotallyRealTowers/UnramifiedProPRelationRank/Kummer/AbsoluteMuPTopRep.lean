/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteKummerH1Linear
import GaloisCohomology.ProP.FiniteTransgression
import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Instances.ZMod

set_option autoImplicit false
/-!
# The natural absolute-Galois representation on `mu_p`

For an arbitrary characteristic-zero field, the `p`-th roots of unity in its algebraic closure
form a discrete `ZMod p`-module with the natural (generally nontrivial) absolute-Galois action.
This file constructs that coefficient `TopRep` without assuming that the base field contains
the roots of unity.  It also constructs the usual root quotient attached to a base-field unit
as a continuous twisted one-cocycle for this action.
-/

open scoped Pointwise Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open CategoryTheory KummerTheory TopRep ContRepresentation groupCohomology

variable (K : Type*) [Field K]
variable (p : ℕ) [Fact p.Prime]

/-- Unfold the public absolute-Galois-group wrapper to the Galois group on which the canonical
field action is defined. -/
def absoluteGaloisGroupContinuousMulEquiv :
    Field.absoluteGaloisGroup K ≃ₜ* Gal(AlgebraicClosure K/K) := by
  change Gal(AlgebraicClosure K/K) ≃ₜ* Gal(AlgebraicClosure K/K)
  exact ContinuousMulEquiv.refl _

/-- The additive presentation of the discrete group of `p`-th roots of unity in an algebraic
closure.  No choice of a primitive root is made. -/
abbrev AbsoluteMuP :=
  Additive (DiscreteNthRootsSubgroup (AlgebraicClosure K) p)

omit [Fact p.Prime] in
/-- Every element of `AbsoluteMuP K p` is killed by `p`. -/
theorem absoluteMuP_nsmul_eq_zero (x : AbsoluteMuP K p) : p • x = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (mem_nthRootsSubgroup_iff (AlgebraicClosure K)).mp x.toMul.property

/-- The intrinsic `ZMod p`-module structure on `mu_p`. -/
noncomputable instance absoluteMuPModule : Module (ZMod p) (AbsoluteMuP K p) :=
  additiveZModModuleOfPowEqOne p fun x => by
    apply Subtype.ext
    exact (mem_nthRootsSubgroup_iff (AlgebraicClosure K)).mp x.property

/-- The intrinsic scalar action is continuous for the discrete topology on `mu_p`. -/
instance absoluteMuPContinuousSMul : ContinuousSMul (ZMod p) (AbsoluteMuP K p) :=
  ⟨continuous_of_discreteTopology⟩

/-- The natural action of an absolute Galois element on `mu_p`, as an additive homomorphism. -/
def absoluteMuPActionAddHom (sigma : Field.absoluteGaloisGroup K) :
    AbsoluteMuP K p →+ AbsoluteMuP K p where
  toFun x := Additive.ofMul
    ⟨absoluteGaloisGroupContinuousMulEquiv K sigma • x.toMul.1,
      smul_mem_nthRootsSubgroup (AlgebraicClosure K) p
        (absoluteGaloisGroupContinuousMulEquiv K sigma) x.toMul.property⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Additive.toMul.injective
    apply Subtype.ext
    simp

omit [Fact p.Prime] in
@[simp]
theorem absoluteMuPActionAddHom_apply_coe
    (sigma : Field.absoluteGaloisGroup K) (x : AbsoluteMuP K p) :
    (absoluteMuPActionAddHom K p sigma x).toMul.1 =
    (absoluteGaloisGroupContinuousMulEquiv K sigma) • x.toMul.1 :=
  rfl

/-- The natural Galois action on `mu_p`; the scalar action of `ZMod p` is intrinsic, so every
Galois action map is automatically linear. -/
def absoluteMuPActionContinuousLinearMap (sigma : Field.absoluteGaloisGroup K) :
    AbsoluteMuP K p →L[ZMod p] AbsoluteMuP K p where
  toLinearMap := (absoluteMuPActionAddHom K p sigma).toZModLinearMap p
  cont := continuous_of_discreteTopology

@[simp]
theorem absoluteMuPActionContinuousLinearMap_apply
    (sigma : Field.absoluteGaloisGroup K) (x : AbsoluteMuP K p) :
    absoluteMuPActionContinuousLinearMap K p sigma x =
      absoluteMuPActionAddHom K p sigma x :=
  rfl

/-- The natural continuous representation of the absolute Galois group on `mu_p`.  Here
"continuous representation" is Mathlib's `ContRepresentation`: the coefficient module is a
topological module and each action map is continuous. -/
def absoluteMuPContRepresentation :
    ContRepresentation (ZMod p) (Field.absoluteGaloisGroup K) (AbsoluteMuP K p) where
  toMonoidHom :=
  { toFun := absoluteMuPActionContinuousLinearMap K p
    map_one' := by
      apply ContinuousLinearMap.ext
      intro x
      apply Additive.toMul.injective
      apply Subtype.ext
      simp
    map_mul' := by
      intro sigma tau
      apply ContinuousLinearMap.ext
      intro x
      apply Additive.toMul.injective
      apply Subtype.ext
      simp [mul_smul] }

/-- The natural Tate-dual coefficient object `mu_p` in `TopRep`. -/
def absoluteMuPTopRep :
    TopRep (ZMod p) (Field.absoluteGaloisGroup K) :=
  TopRep.of (absoluteMuPContRepresentation K p)

variable [CharZero K]

private abbrev primePNat : ℕ+ :=
  (p.toPNat (Fact.out : p.Prime).pos)

private abbrev AbsoluteRadicalDatum :=
  chosenFiniteKummerRadicalDatum
    (K := K) (L := AlgebraicClosure K) (primePNat p)

/-- The chosen algebraic-closure root used to form the Kummer cocycle of a base-field unit. -/
def absoluteKummerChosenRoot (a : Kˣ) : (AlgebraicClosure K)ˣ :=
  (AbsoluteRadicalDatum K p).root
    (unitsEquivAbsoluteRadicalCarrier K (primePNat p) a)

omit [CharZero K] in
/-- The chosen absolute Kummer root has the prescribed `p`-th power. -/
@[simp]
theorem absoluteKummerChosenRoot_pow (a : Kˣ) :
    absoluteKummerChosenRoot K p a ^ p =
      Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a := by
  rw [absoluteKummerChosenRoot]
  change (AbsoluteRadicalDatum K p).root
      (unitsEquivAbsoluteRadicalCarrier K (primePNat p) a) ^
        (primePNat p : ℕ) = _
  rw [(AbsoluteRadicalDatum K p).root_pow_eq_map]
  congr 1

/-- The usual quotient `sigma(beta) / beta`, valued in the natural Galois module `mu_p`.
Unlike the character-valued API, this construction does not assume `mu_p` lies in `K`. -/
def absoluteKummerMuPRootCocycle (a : Kˣ)
    (sigma : Field.absoluteGaloisGroup K) : AbsoluteMuP K p :=
  let a' := unitsEquivAbsoluteRadicalCarrier K (primePNat p) a
  Additive.ofMul
    ⟨(AbsoluteRadicalDatum K p).rootCocycle a'
        (absoluteGaloisGroupContinuousMulEquiv K sigma),
      (AbsoluteRadicalDatum K p).rootCocycle_mem_nthRootsSubgroup a'
        (absoluteGaloisGroupContinuousMulEquiv K sigma)⟩

omit [CharZero K] in
/-- Evaluation of the root cocycle in the ambient unit group. -/
@[simp]
theorem absoluteKummerMuPRootCocycle_apply_coe
    (a : Kˣ) (sigma : Field.absoluteGaloisGroup K) :
    (absoluteKummerMuPRootCocycle K p a sigma).toMul.1 =
      absoluteGaloisGroupContinuousMulEquiv K sigma •
          absoluteKummerChosenRoot K p a /
        absoluteKummerChosenRoot K p a :=
  rfl

omit [CharZero K] in
/-- The root quotient satisfies the twisted additive cocycle identity for the natural action on
`mu_p`. -/
theorem absoluteKummerMuPRootCocycle_mul
    (a : Kˣ) (sigma tau : Field.absoluteGaloisGroup K) :
    absoluteKummerMuPRootCocycle K p a (sigma * tau) =
      absoluteMuPActionContinuousLinearMap K p sigma
          (absoluteKummerMuPRootCocycle K p a tau) +
        absoluteKummerMuPRootCocycle K p a sigma := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (AbsoluteRadicalDatum K p).rootCocycle_mul
    (unitsEquivAbsoluteRadicalCarrier K (primePNat p) a)
      (absoluteGaloisGroupContinuousMulEquiv K sigma)
      (absoluteGaloisGroupContinuousMulEquiv K tau)

/-- The root quotient is locally constant on the Krull-topological absolute Galois group. -/
theorem absoluteKummerMuPRootCocycle_isLocallyConstant (a : Kˣ) :
    IsLocallyConstant (absoluteKummerMuPRootCocycle K p a) := by
  rw [IsLocallyConstant.iff_exists_open]
  intro sigma
  let beta := absoluteKummerChosenRoot K p a
  let E := FiniteGaloisIntermediateField.adjoin K {(beta : AlgebraicClosure K)}
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
    have hfix : h (beta : AlgebraicClosure K) = beta :=
      ((IntermediateField.mem_fixingSubgroup_iff E.toIntermediateField h).mp hh)
        (beta : AlgebraicClosure K)
        (FiniteGaloisIntermediateField.subset_adjoin K {(beta : AlgebraicClosure K)}
          (Set.mem_singleton (beta : AlgebraicClosure K)))
    have hfixUnit : h • beta = beta := by
      apply Units.ext
      exact hfix
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [absoluteKummerMuPRootCocycle_apply_coe]
    change e sigma * h = e tau at htau
    rw [← htau, mul_smul, hfixUnit]

/-- The absolute Kummer root quotient is continuous with its natural, nontrivial coefficient
action. -/
theorem absoluteKummerMuPRootCocycle_continuous (a : Kˣ) :
    Continuous (absoluteKummerMuPRootCocycle K p a) :=
  (absoluteKummerMuPRootCocycle_isLocallyConstant K p a).continuous

/-- The root quotient packaged as a continuous map. -/
def absoluteKummerMuPRootCocycleContinuousMap (a : Kˣ) :
    C(Field.absoluteGaloisGroup K, AbsoluteMuP K p) :=
  ⟨absoluteKummerMuPRootCocycle K p a,
    absoluteKummerMuPRootCocycle_continuous K p a⟩

/-- The homogeneous one-cochain associated with the absolute Kummer root cocycle.  Writing it as
`c(h) - c(g)` makes continuity immediate and avoids imposing joint continuity on Mathlib's
`TopRep` action. -/
def absoluteKummerMuPHomogeneousOneCochain (a : Kˣ) :
    (TopRep.homogeneousCochains (absoluteMuPTopRep K p)).X 1 := by
  let c := absoluteKummerMuPRootCocycleContinuousMap K p a
  let sigma : C(Field.absoluteGaloisGroup K,
      C(Field.absoluteGaloisGroup K, AbsoluteMuP K p)) :=
    ContinuousMap.curry
      ⟨fun x ↦ c x.2 - c x.1,
        (c.continuous_toFun.comp continuous_snd).sub
          (c.continuous_toFun.comp continuous_fst)⟩
  exact ⟨sigma, by
    intro tau
    apply ContinuousMap.ext
    intro g
    apply ContinuousMap.ext
    intro h
    change absoluteMuPActionContinuousLinearMap K p tau
        (c (tau⁻¹ * h) - c (tau⁻¹ * g)) = c h - c g
    rw [map_sub]
    change absoluteMuPActionContinuousLinearMap K p tau
        (absoluteKummerMuPRootCocycle K p a (tau⁻¹ * h)) -
          absoluteMuPActionContinuousLinearMap K p tau
            (absoluteKummerMuPRootCocycle K p a (tau⁻¹ * g)) =
      absoluteKummerMuPRootCocycle K p a h -
        absoluteKummerMuPRootCocycle K p a g
    have hh := absoluteKummerMuPRootCocycle_mul K p a tau (tau⁻¹ * h)
    have hg := absoluteKummerMuPRootCocycle_mul K p a tau (tau⁻¹ * g)
    rw [show tau * (tau⁻¹ * h) = h by group] at hh
    rw [show tau * (tau⁻¹ * g) = g by group] at hg
    rw [hh, hg]
    abel⟩

@[simp]
theorem absoluteKummerMuPHomogeneousOneCochain_apply
    (a : Kˣ) (g h : Field.absoluteGaloisGroup K) :
    (absoluteKummerMuPHomogeneousOneCochain K p a).1 g h =
      absoluteKummerMuPRootCocycle K p a h -
        absoluteKummerMuPRootCocycle K p a g :=
  rfl

/-- The difference presentation agrees with the usual homogeneousization
`g • c(g⁻¹h)`. -/
theorem absoluteKummerMuPHomogeneousOneCochain_eq_action
    (a : Kˣ) (g h : Field.absoluteGaloisGroup K) :
    (absoluteKummerMuPHomogeneousOneCochain K p a).1 g h =
      absoluteMuPActionContinuousLinearMap K p g
        (absoluteKummerMuPRootCocycle K p a (g⁻¹ * h)) := by
  rw [absoluteKummerMuPHomogeneousOneCochain_apply]
  have hc := absoluteKummerMuPRootCocycle_mul K p a g (g⁻¹ * h)
  rw [show g * (g⁻¹ * h) = h by group] at hc
  rw [hc]
  abel

/-- The homogeneous Kummer one-cochain is killed by the next differential. -/
theorem absoluteKummerMuPHomogeneousOneCochain_mem_cycles (a : Kˣ) :
    ((TopRep.homogeneousCochains (absoluteMuPTopRep K p)).d 1 2).hom
      (absoluteKummerMuPHomogeneousOneCochain K p a) = 0 := by
  change _ =
    (0 : (TopRep.resolutionX (absoluteMuPTopRep K p) 3).ρ.invariants)
  apply Subtype.ext
  ext g h k
  have hd := TopRep.homogeneousCochains.d_apply
    (absoluteMuPTopRep K p) 1
      (absoluteKummerMuPHomogeneousOneCochain K p a)
  have hdh := congrArg (fun tau ↦ tau g h k) hd
  rw [hdh]
  simp [TopRep.d_succ, TopRep.d_zero, TopRep.hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun]
  change (absoluteKummerMuPRootCocycle K p a k -
      absoluteKummerMuPRootCocycle K p a h) -
    ((absoluteKummerMuPRootCocycle K p a k -
        absoluteKummerMuPRootCocycle K p a g) -
      (absoluteKummerMuPRootCocycle K p a h -
        absoluteKummerMuPRootCocycle K p a g)) = 0
  abel

/-- The absolute Kummer root quotient packaged as a homogeneous continuous one-cocycle. -/
noncomputable def absoluteKummerMuPHomogeneousOneCocycle (a : Kˣ) :
    ContinuousCohomology.cocycles (absoluteMuPTopRep K p) 1 :=
  ClassFieldTower.Cohomology.homogeneousCocycleOfElement
    (absoluteMuPTopRep K p) 1
      (absoluteKummerMuPHomogeneousOneCochain K p a)
      (absoluteKummerMuPHomogeneousOneCochain_mem_cycles K p a)

@[simp]
theorem iCycles_absoluteKummerMuPHomogeneousOneCocycle (a : Kˣ) :
    (TopRep.homogeneousCochains (absoluteMuPTopRep K p)).iCycles 1
        (absoluteKummerMuPHomogeneousOneCocycle K p a) =
      absoluteKummerMuPHomogeneousOneCochain K p a :=
  ClassFieldTower.Cohomology.iCycles_homogeneousCocycleOfElement
    (absoluteMuPTopRep K p) 1
      (absoluteKummerMuPHomogeneousOneCochain K p a)
      (absoluteKummerMuPHomogeneousOneCochain_mem_cycles K p a)

/-- The degree-one continuous cohomology class of the absolute Kummer root quotient with its
natural Tate-dual coefficient action. -/
noncomputable def absoluteKummerMuPH1Class (a : Kˣ) :
    continuousCohomology 1 (absoluteMuPTopRep K p) :=
  ContinuousCohomology.π (absoluteMuPTopRep K p) 1
    (absoluteKummerMuPHomogeneousOneCocycle K p a)

end ClassFieldTower.Martinet.Shafarevich
