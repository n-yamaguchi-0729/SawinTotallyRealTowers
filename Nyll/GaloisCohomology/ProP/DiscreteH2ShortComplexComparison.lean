/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.ProP.DiscreteH2CochainComparison
public import Nyll.GaloisCohomology.Cyclic.IntegralCoefficientCohomology
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.RepresentationTheory.Continuous.Basic
public import Mathlib.RepresentationTheory.Continuous.TopRep
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.ContinuousMap.Defs

/-!
# The degree-two short complex for a discrete group

The explicit homogeneous/inhomogeneous cochain equivalences commute with
the two differentials surrounding degree two.  We package them as an
isomorphism of short complexes after forgetting topology and restricting
scalars to the underlying additive groups. The ordinary coefficient ring and
acting group share an arbitrary universe; the original integer comparison is
the specialization to universe zero.
-/

@[expose] public section

open CategoryTheory TopRep ContRepresentation

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

variable {p : ℕ}
variable {R : Type u} [CommRing R] [Module R (ULift.{u} (ZMod p))]
variable {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable [DiscreteTopology Q]

/-- The ordinary trivial representation matching the lifted continuous
coefficient carrier. -/
abbrev ordinaryTrivialZModPLifted : Rep.{u} R Q :=
  Rep.trivial R Q (ULift.{u} (ZMod p))

/-- With lifted integer scalars this is the actual integral coefficient
transport of the original integer representation, through identity maps. -/
def ordinaryTrivialZModPLiftedIntegralIso :
    ordinaryTrivialZModPLifted (R := ULift.{u} ℤ) (p := p) (Q := Q) ≅
      (IntegralGroupCohomology.coefficientFunctor Q).obj
        (Rep.trivial ℤ Q (ULift.{u} (ZMod p))) where
  hom := Rep.ofHom
    { toLinearMap :=
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl }
  inv := Rep.ofHom
    { toLinearMap :=
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }
      isIntertwining' := fun _ => rfl }
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

omit [TopologicalSpace Q] [IsTopologicalGroup Q] [DiscreteTopology Q] in
/-- The integral representation comparison keeps every coefficient value. -/
theorem ordinaryTrivialZModPLiftedIntegralIso_hom_apply (x : ULift.{u} (ZMod p)) :
    (ordinaryTrivialZModPLiftedIntegralIso (p := p) (Q := Q)).hom x = x := rfl

omit [DiscreteTopology Q] in
/-- Dehomogenization intertwines the degree-one differentials. -/
theorem dehomogenizeOne_d
    (c : (trivialZModPCochainsLifted p Q).X 1) :
    dehomogenizeTwo
        ((trivialZModPCochainsLifted p Q).d 1 2 c) =
      groupCohomology.d₁₂ (ordinaryTrivialZModPLifted (R := R) (p := p) (Q := Q))
        (dehomogenizeOne c) := by
  funext x
  rcases x with ⟨g, h⟩
  change
    ((((trivialZModPCochainsLifted p Q).d 1 2).hom c).1
        1 g (g * h)) =
      c.1 1 h - c.1 1 (g * h) + c.1 1 g
  have hd :
      (((trivialZModPCochainsLifted p Q).d 1 2).hom c).1 =
        (d (trivialZModPLifted p Q) 2).hom c.1 := by
    simpa only [Nat.reduceAdd] using
      homogeneousCochains.d_apply (trivialZModPLifted p Q) 1 c
  have hdeval := congrArg
    (fun t ↦ t 1 g (g * h)) hd
  rw [hdeval]
  simp only [Nat.reduceAdd, hom_d_succ, d_zero, hom_ofHom,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun,
    ContinuousMap.sub_apply, ContinuousMap.const_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  have hc := congrArg (fun t ↦ t g (g * h)) (c.2 g)
  change c.1 (g⁻¹ * g) (g⁻¹ * (g * h)) = c.1 g (g * h) at hc
  have hc' : c.1 1 h = c.1 g (g * h) := by simpa only [inv_mul_cancel, inv_mul_cancel_left] using hc
  rw [← hc']
  abel

omit [DiscreteTopology Q] in
/-- Dehomogenization intertwines the degree-two differentials. -/
theorem dehomogenizeTwo_d
    (c : (trivialZModPCochainsLifted p Q).X 2) :
    dehomogenizeThree
        ((trivialZModPCochainsLifted p Q).d 2 3 c) =
      groupCohomology.d₂₃ (ordinaryTrivialZModPLifted (R := R) (p := p) (Q := Q))
        (dehomogenizeTwo c) := by
  funext x
  rcases x with ⟨g, h, k⟩
  change
    ((((trivialZModPCochainsLifted p Q).d 2 3).hom c).1
        1 g (g * h) (g * h * k)) =
      c.1 1 h (h * k) - c.1 1 (g * h) ((g * h) * k) +
        c.1 1 g (g * (h * k)) - c.1 1 g (g * h)
  have hd :
      (((trivialZModPCochainsLifted p Q).d 2 3).hom c).1 =
        (d (trivialZModPLifted p Q) 3).hom c.1 := by
    simpa only [Nat.reduceAdd] using
      homogeneousCochains.d_apply (trivialZModPLifted p Q) 2 c
  have hdeval := congrArg
    (fun t ↦ t 1 g (g * h) (g * h * k)) hd
  rw [hdeval]
  simp only [Nat.reduceAdd, hom_d_succ, d_zero, hom_ofHom,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun,
    ContinuousMap.sub_apply, ContinuousMap.const_apply, ContinuousMap.comp_apply,
    ContinuousMap.coe_mk]
  have hc := congrArg (fun t ↦ t g (g * h) (g * h * k)) (c.2 g)
  change c.1 (g⁻¹ * g) (g⁻¹ * (g * h))
      (g⁻¹ * (g * h * k)) = c.1 g (g * h) (g * h * k) at hc
  have hc' : c.1 1 h (h * k) = c.1 g (g * h) (g * h * k) := by
    simpa only [mul_assoc, inv_mul_cancel, inv_mul_cancel_left] using hc
  rw [← hc']
  rw [show g * h * k = g * (h * k) by group]
  abel

/-- Forget topology and the `ZMod p`-linear structure, retaining the
underlying additive group. -/
abbrev continuousCochainsToAddCommGrp (p : ℕ) :
    TopModuleCat.{u} (ZMod p) ⥤ AddCommGrpCat.{u} :=
  forget₂ (TopModuleCat.{u} (ZMod p)) (ModuleCat.{u} (ZMod p)) ⋙
    forget₂ (ModuleCat.{u} (ZMod p)) AddCommGrpCat.{u}

/-- Forget the scalar action on ordinary group cochains. -/
abbrev ordinaryCochainsToAddCommGrp (R : Type u) [CommRing R] :
    ModuleCat.{u} R ⥤ AddCommGrpCat.{u} :=
  forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}

/-- The degree-one cochain equivalence as an additive-group isomorphism. -/
noncomputable def homogeneousOneCochainAddCommGrpIso :
    (continuousCochainsToAddCommGrp p).obj
        ((trivialZModPCochainsLifted p Q).X 1) ≅
      (ordinaryCochainsToAddCommGrp R).obj
        (ModuleCat.of R (Q → ULift.{u} (ZMod p))) :=
  homogeneousOneCochainAddEquiv.toAddCommGrpIso

/-- The degree-two cochain equivalence as an additive-group isomorphism. -/
noncomputable def homogeneousTwoCochainAddCommGrpIso :
    (continuousCochainsToAddCommGrp p).obj
        ((trivialZModPCochainsLifted p Q).X 2) ≅
      (ordinaryCochainsToAddCommGrp R).obj
        (ModuleCat.of R (Q × Q → ULift.{u} (ZMod p))) :=
  homogeneousTwoCochainAddEquiv.toAddCommGrpIso

/-- The degree-three cochain equivalence as an additive-group isomorphism. -/
noncomputable def homogeneousThreeCochainAddCommGrpIso :
    (continuousCochainsToAddCommGrp p).obj
        ((trivialZModPCochainsLifted p Q).X 3) ≅
      (ordinaryCochainsToAddCommGrp R).obj
        (ModuleCat.of R (Q × Q × Q → ULift.{u} (ZMod p))) :=
  homogeneousThreeCochainAddEquiv.toAddCommGrpIso

/-- For a discrete group, the homogeneous continuous degree-two short
complex is the ordinary inhomogeneous one after forgetting structure. -/
noncomputable def discreteH2ShortComplexIso :
    ((trivialZModPCochainsLifted p Q).sc' 1 2 3).map
        (continuousCochainsToAddCommGrp p) ≅
      (groupCohomology.shortComplexH2
          (ordinaryTrivialZModPLifted (R := R) (p := p) (Q := Q))).map
        (ordinaryCochainsToAddCommGrp R) := by
  refine ShortComplex.isoMk
    (homogeneousOneCochainAddCommGrpIso (R := R) (p := p) (Q := Q))
    (homogeneousTwoCochainAddCommGrpIso (R := R) (p := p) (Q := Q))
    (homogeneousThreeCochainAddCommGrpIso (R := R) (p := p) (Q := Q)) ?_ ?_
  · ext c
    exact (dehomogenizeOne_d (R := R) (p := p) (Q := Q) c).symm
  · ext c
    exact (dehomogenizeTwo_d (R := R) (p := p) (Q := Q) c).symm

end

end ClassFieldTower.Cohomology
