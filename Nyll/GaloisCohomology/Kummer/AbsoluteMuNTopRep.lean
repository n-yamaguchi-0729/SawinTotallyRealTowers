/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteKummerH1
public import Nyll.GaloisCohomology.Topology.AlgebraicGaloisOrbits
public import Nyll.GaloisCohomology.Topology.AbsoluteGaloisMap
public import Nyll.GaloisCohomology.ProP.FiniteTransgression
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Instances.ZMod

/-!
# The natural absolute-Galois representation on `mu_n`

For an arbitrary field, the `n`-th roots of unity in its algebraic closure
form a discrete `ZMod n`-module with the natural (generally nontrivial) absolute-Galois action.
This file constructs that coefficient `TopRep` without assuming that the base field contains
the roots of unity.  It also constructs the usual root quotient attached to a base-field unit
as a continuous twisted one-cocycle for this action.
-/

@[expose] public section

open scoped Pointwise Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open CategoryTheory KummerTheory TopRep ContRepresentation groupCohomology

variable (K : Type*) [Field K]

section Coefficients

variable (n : ℕ)

/-- The additive presentation of the discrete group of `n`-th roots of unity in an algebraic
closure.  No choice of a primitive root is made. -/
abbrev AbsoluteMuN :=
  Additive (DiscreteNthRootsSubgroup (AlgebraicClosure K) n)

/-- Every element of `AbsoluteMuN K n` is killed by `n`. -/
theorem absoluteMuN_nsmul_eq_zero (x : AbsoluteMuN K n) : n • x = 0 := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (mem_nthRootsSubgroup_iff (AlgebraicClosure K)).mp x.toMul.property

/-- The intrinsic `ZMod n`-module structure on `mu_n`. -/
noncomputable instance absoluteMuNModule : Module (ZMod n) (AbsoluteMuN K n) :=
  AddCommGroup.zmodModule (absoluteMuN_nsmul_eq_zero K n)

/-- The intrinsic scalar action is continuous for the discrete topology on `mu_n`. -/
instance absoluteMuNContinuousSMul : ContinuousSMul (ZMod n) (AbsoluteMuN K n) :=
  ⟨continuous_of_discreteTopology⟩

/-- The roots-of-unity coefficient group is finite for every nonzero exponent. -/
instance absoluteMuNFinite [NeZero n] : Finite (AbsoluteMuN K n) :=
  inferInstanceAs (Finite (nthRootsSubgroup (AlgebraicClosure K) n))

/-- For a nonzero exponent, the natural coefficient module is finitely generated. -/
theorem absoluteMuN_moduleFinite [NeZero n] : Module.Finite (ZMod n) (AbsoluteMuN K n) :=
  Module.Finite.of_finite

/-- The natural action of an absolute Galois element on `mu_n`, as an additive homomorphism. -/
def absoluteMuNActionAddHom (sigma : Field.absoluteGaloisGroup K) :
    AbsoluteMuN K n →+ AbsoluteMuN K n where
  toFun x := Additive.ofMul
    ⟨absoluteGaloisGroupContinuousMulEquiv K sigma • x.toMul.1,
      smul_mem_nthRootsSubgroup (AlgebraicClosure K) n
        (absoluteGaloisGroupContinuousMulEquiv K sigma) x.toMul.property⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (absoluteGaloisGroupContinuousMulEquiv K sigma) •
      (1 : (AlgebraicClosure K)ˣ) = 1
    exact smul_one _
  map_add' x y := by
    apply Additive.toMul.injective
    apply Subtype.ext
    change (absoluteGaloisGroupContinuousMulEquiv K sigma) •
      (x.toMul.1 * y.toMul.1) =
        ((absoluteGaloisGroupContinuousMulEquiv K sigma) • x.toMul.1) *
          ((absoluteGaloisGroupContinuousMulEquiv K sigma) • y.toMul.1)
    exact smul_mul' _ _ _

@[simp]
theorem absoluteMuNActionAddHom_apply_coe
    (sigma : Field.absoluteGaloisGroup K) (x : AbsoluteMuN K n) :
    (absoluteMuNActionAddHom K n sigma x).toMul.1 =
    (absoluteGaloisGroupContinuousMulEquiv K sigma) • x.toMul.1 :=
  rfl

/-- The natural Galois action on `mu_n`; the scalar action of `ZMod n` is intrinsic, so every
Galois action map is automatically linear. -/
def absoluteMuNActionContinuousLinearMap (sigma : Field.absoluteGaloisGroup K) :
    AbsoluteMuN K n →L[ZMod n] AbsoluteMuN K n where
  toLinearMap := (absoluteMuNActionAddHom K n sigma).toZModLinearMap n
  cont := continuous_of_discreteTopology

@[simp]
theorem absoluteMuNActionContinuousLinearMap_apply
    (sigma : Field.absoluteGaloisGroup K) (x : AbsoluteMuN K n) :
    absoluteMuNActionContinuousLinearMap K n sigma x =
      absoluteMuNActionAddHom K n sigma x :=
  rfl

/-- The natural continuous representation of the absolute Galois group on `mu_n`.  Here
"continuous representation" is Mathlib's `ContRepresentation`: the coefficient module is a
topological module and each action map is continuous. -/
def absoluteMuNContRepresentation :
    ContRepresentation (ZMod n) (Field.absoluteGaloisGroup K) (AbsoluteMuN K n) where
  toMonoidHom :=
  { toFun := absoluteMuNActionContinuousLinearMap K n
    map_one' := by
      apply ContinuousLinearMap.ext
      intro x
      apply Additive.toMul.injective
      apply Subtype.ext
      change (absoluteGaloisGroupContinuousMulEquiv K 1) • x.toMul.1 = x.toMul.1
      rw [map_one, one_smul]
    map_mul' := by
      intro sigma tau
      apply ContinuousLinearMap.ext
      intro x
      apply Additive.toMul.injective
      apply Subtype.ext
      change (absoluteGaloisGroupContinuousMulEquiv K (sigma * tau)) • x.toMul.1 =
        (absoluteGaloisGroupContinuousMulEquiv K sigma) •
          ((absoluteGaloisGroupContinuousMulEquiv K tau) • x.toMul.1)
      rw [map_mul, mul_smul] }

/-- The natural Tate-dual coefficient object `mu_n` in `TopRep`. -/
def absoluteMuNTopRep :
    TopRep (ZMod n) (Field.absoluteGaloisGroup K) :=
  TopRep.of (absoluteMuNContRepresentation K n)

/-- Every orbit in the natural roots-of-unity module is locally constant. -/
theorem absoluteMuNAction_isLocallyConstant (x : AbsoluteMuN K n) :
    IsLocallyConstant (fun sigma => absoluteMuNActionAddHom K n sigma x) := by
  have horbit := (GaloisCohomology.isLocallyConstant_galois_units
    (K := K) x.toMul.1).comp_continuous
      (absoluteGaloisGroupContinuousMulEquiv K).continuous
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro sigma
  obtain ⟨U, hU, hsigma, hconst⟩ := horbit.exists_open sigma
  refine ⟨U, hU, hsigma, ?_⟩
  intro tau htau
  apply Additive.toMul.injective
  apply Subtype.ext
  exact hconst tau htau

/-- The natural action is jointly continuous for the Krull and discrete topologies. -/
theorem absoluteMuNTopRep_action_continuous :
    Continuous (fun gx : Field.absoluteGaloisGroup K × AbsoluteMuN K n =>
      (absoluteMuNTopRep K n).ρ gx.1 gx.2) := by
  apply continuous_prod_of_discrete_right.mpr
  intro x
  exact (absoluteMuNAction_isLocallyConstant K n x).continuous

end Coefficients

section PositiveExponent

variable (n : ℕ+)

/-- The chosen algebraic-closure root used to form the Kummer cocycle of a base-field unit. -/
def absoluteKummerMuNChosenRoot (a : Kˣ) : (AlgebraicClosure K)ˣ :=
  (AbsoluteRadicalDatum K n).root
    (unitsEquivAbsoluteRadicalCarrier K n a)

/-- The chosen absolute Kummer root has the prescribed `n`-th power. -/
@[simp]
theorem absoluteKummerMuNChosenRoot_pow (a : Kˣ) :
    absoluteKummerMuNChosenRoot K n a ^ (n : ℕ) =
      Units.map (algebraMap K (AlgebraicClosure K)).toMonoidHom a := by
  rw [absoluteKummerMuNChosenRoot]
  rw [(AbsoluteRadicalDatum K n).root_pow_eq_map]
  congr 1

/-- The usual quotient `sigma(beta) / beta`, valued in the natural Galois module `mu_n`.
Unlike the character-valued API, this construction does not assume `mu_n` lies in `K`. -/
def absoluteKummerMuNRootCocycle (a : Kˣ)
    (sigma : Field.absoluteGaloisGroup K) : AbsoluteMuN K n :=
  let a' := unitsEquivAbsoluteRadicalCarrier K n a
  Additive.ofMul
    ⟨(AbsoluteRadicalDatum K n).rootCocycle a'
        (absoluteGaloisGroupContinuousMulEquiv K sigma),
      (AbsoluteRadicalDatum K n).rootCocycle_mem_nthRootsSubgroup a'
        (absoluteGaloisGroupContinuousMulEquiv K sigma)⟩

/-- Evaluation of the root cocycle in the ambient unit group. -/
@[simp]
theorem absoluteKummerMuNRootCocycle_apply_coe
    (a : Kˣ) (sigma : Field.absoluteGaloisGroup K) :
    (absoluteKummerMuNRootCocycle K n a sigma).toMul.1 =
      absoluteGaloisGroupContinuousMulEquiv K sigma •
          absoluteKummerMuNChosenRoot K n a /
        absoluteKummerMuNChosenRoot K n a :=
  rfl

/-- The root quotient satisfies the twisted additive cocycle identity for the natural action on
`mu_n`. -/
theorem absoluteKummerMuNRootCocycle_mul
    (a : Kˣ) (sigma tau : Field.absoluteGaloisGroup K) :
    absoluteKummerMuNRootCocycle K n a (sigma * tau) =
      absoluteMuNActionContinuousLinearMap K n sigma
          (absoluteKummerMuNRootCocycle K n a tau) +
        absoluteKummerMuNRootCocycle K n a sigma := by
  apply Additive.toMul.injective
  apply Subtype.ext
  exact (AbsoluteRadicalDatum K n).rootCocycle_mul
    (unitsEquivAbsoluteRadicalCarrier K n a)
      (absoluteGaloisGroupContinuousMulEquiv K sigma)
      (absoluteGaloisGroupContinuousMulEquiv K tau)

/-- The root quotient is locally constant on the Krull-topological absolute Galois group. -/
theorem absoluteKummerMuNRootCocycle_isLocallyConstant (a : Kˣ) :
    IsLocallyConstant (absoluteKummerMuNRootCocycle K n a) := by
  have horbit := (GaloisCohomology.isLocallyConstant_galois_units
    (K := K) (absoluteKummerMuNChosenRoot K n a)).comp_continuous
      (absoluteGaloisGroupContinuousMulEquiv K).continuous
  apply (IsLocallyConstant.iff_exists_open _).mpr
  intro sigma
  obtain ⟨U, hU, hsigma, hconst⟩ := horbit.exists_open sigma
  refine ⟨U, hU, hsigma, ?_⟩
  intro tau htau
  apply Additive.toMul.injective
  apply Subtype.ext
  exact congrArg (fun z : (AlgebraicClosure K)ˣ => z / absoluteKummerMuNChosenRoot K n a)
    (hconst tau htau)

/-- The absolute Kummer root quotient is continuous with its natural, nontrivial coefficient
action. -/
theorem absoluteKummerMuNRootCocycle_continuous (a : Kˣ) :
    Continuous (absoluteKummerMuNRootCocycle K n a) :=
  (absoluteKummerMuNRootCocycle_isLocallyConstant K n a).continuous

/-- The root quotient packaged as a continuous map. -/
def absoluteKummerMuNRootCocycleContinuousMap (a : Kˣ) :
    C(Field.absoluteGaloisGroup K, AbsoluteMuN K n) :=
  ⟨absoluteKummerMuNRootCocycle K n a,
    absoluteKummerMuNRootCocycle_continuous K n a⟩

/-- The homogeneous one-cochain associated with the absolute Kummer root cocycle.  Writing it as
`c(h) - c(g)` expresses continuity directly through the continuous root quotient. -/
def absoluteKummerMuNHomogeneousOneCochain (a : Kˣ) :
    (TopRep.homogeneousCochains (absoluteMuNTopRep K n)).X 1 := by
  let c := absoluteKummerMuNRootCocycleContinuousMap K n a
  let sigma : C(Field.absoluteGaloisGroup K,
      C(Field.absoluteGaloisGroup K, AbsoluteMuN K n)) :=
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
    change absoluteMuNActionContinuousLinearMap K n tau
        (c (tau⁻¹ * h) - c (tau⁻¹ * g)) = c h - c g
    rw [map_sub]
    change absoluteMuNActionContinuousLinearMap K n tau
        (absoluteKummerMuNRootCocycle K n a (tau⁻¹ * h)) -
          absoluteMuNActionContinuousLinearMap K n tau
            (absoluteKummerMuNRootCocycle K n a (tau⁻¹ * g)) =
      absoluteKummerMuNRootCocycle K n a h -
        absoluteKummerMuNRootCocycle K n a g
    have hh := absoluteKummerMuNRootCocycle_mul K n a tau (tau⁻¹ * h)
    have hg := absoluteKummerMuNRootCocycle_mul K n a tau (tau⁻¹ * g)
    rw [show tau * (tau⁻¹ * h) = h by group] at hh
    rw [show tau * (tau⁻¹ * g) = g by group] at hg
    rw [hh, hg]
    abel⟩

@[simp]
theorem absoluteKummerMuNHomogeneousOneCochain_apply
    (a : Kˣ) (g h : Field.absoluteGaloisGroup K) :
    (absoluteKummerMuNHomogeneousOneCochain K n a).1 g h =
      absoluteKummerMuNRootCocycle K n a h -
        absoluteKummerMuNRootCocycle K n a g :=
  rfl

/-- The difference presentation agrees with the usual homogeneousization
`g • c(g⁻¹h)`. -/
theorem absoluteKummerMuNHomogeneousOneCochain_eq_action
    (a : Kˣ) (g h : Field.absoluteGaloisGroup K) :
    (absoluteKummerMuNHomogeneousOneCochain K n a).1 g h =
      absoluteMuNActionContinuousLinearMap K n g
        (absoluteKummerMuNRootCocycle K n a (g⁻¹ * h)) := by
  rw [absoluteKummerMuNHomogeneousOneCochain_apply]
  have hc := absoluteKummerMuNRootCocycle_mul K n a g (g⁻¹ * h)
  rw [show g * (g⁻¹ * h) = h by group] at hc
  rw [hc]
  abel

/-- The homogeneous Kummer one-cochain is killed by the next differential. -/
theorem absoluteKummerMuNHomogeneousOneCochain_mem_cycles (a : Kˣ) :
    ((TopRep.homogeneousCochains (absoluteMuNTopRep K n)).d 1 2).hom
      (absoluteKummerMuNHomogeneousOneCochain K n a) = 0 := by
  change _ =
    (0 : (TopRep.resolutionX (absoluteMuNTopRep K n) 3).ρ.invariants)
  apply Subtype.ext
  ext g h k
  have hd := TopRep.homogeneousCochains.d_apply
    (absoluteMuNTopRep K n) 1
      (absoluteKummerMuNHomogeneousOneCochain K n a)
  have hdh := congrArg (fun tau ↦ tau g h k) hd
  rw [hdh]
  simp only [Nat.reduceAdd, ZeroMemClass.coe_zero, ContinuousMap.zero_apply]
  change (absoluteKummerMuNRootCocycle K n a k -
      absoluteKummerMuNRootCocycle K n a h) -
    ((absoluteKummerMuNRootCocycle K n a k -
        absoluteKummerMuNRootCocycle K n a g) -
      (absoluteKummerMuNRootCocycle K n a h -
        absoluteKummerMuNRootCocycle K n a g)) = 0
  abel

/-- The absolute Kummer root quotient packaged as a homogeneous continuous one-cocycle. -/
noncomputable def absoluteKummerMuNHomogeneousOneCocycle (a : Kˣ) :
    ContinuousCohomology.cocycles (absoluteMuNTopRep K n) 1 :=
  ClassFieldTower.Cohomology.homogeneousCocycleOfElement
    (absoluteMuNTopRep K n) 1
      (absoluteKummerMuNHomogeneousOneCochain K n a)
      (absoluteKummerMuNHomogeneousOneCochain_mem_cycles K n a)

@[simp]
theorem iCycles_absoluteKummerMuNHomogeneousOneCocycle (a : Kˣ) :
    (TopRep.homogeneousCochains (absoluteMuNTopRep K n)).iCycles 1
        (absoluteKummerMuNHomogeneousOneCocycle K n a) =
      absoluteKummerMuNHomogeneousOneCochain K n a :=
  ClassFieldTower.Cohomology.iCycles_homogeneousCocycleOfElement
    (absoluteMuNTopRep K n) 1
      (absoluteKummerMuNHomogeneousOneCochain K n a)
      (absoluteKummerMuNHomogeneousOneCochain_mem_cycles K n a)

/-- The degree-one continuous cohomology class of the absolute Kummer root quotient with its
natural Tate-dual coefficient action. -/
noncomputable def absoluteKummerMuNH1Class (a : Kˣ) :
    continuousCohomology 1 (absoluteMuNTopRep K n) :=
  ContinuousCohomology.π (absoluteMuNTopRep K n) 1
    (absoluteKummerMuNHomogeneousOneCocycle K n a)

end PositiveExponent

end ClassFieldTower.Martinet.Shafarevich
