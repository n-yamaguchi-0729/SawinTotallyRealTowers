/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.DiscreteH2CochainComparison
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

set_option autoImplicit false
/-!
# The degree-two short complex for a discrete group

The explicit homogeneous/inhomogeneous cochain equivalences commute with
the two differentials surrounding degree two.  We package them as an
isomorphism of short complexes after forgetting topology and restricting
scalars from `ZMod p` to `Int`.
-/

open CategoryTheory TopRep ContRepresentation

namespace ClassFieldTower.Cohomology

noncomputable section

variable {p : ℕ}
variable {Q : Type} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable [DiscreteTopology Q]

/-- The ordinary trivial representation matching the lifted continuous
coefficient carrier. -/
abbrev ordinaryTrivialZModPLifted : Rep ℤ Q :=
  Rep.trivial ℤ Q (ULift (ZMod p))

omit [DiscreteTopology Q] in
/-- Dehomogenization intertwines the degree-one differentials. -/
theorem dehomogenizeOne_d
    (c : (trivialZModPCochainsLifted p Q).X 1) :
    dehomogenizeTwo
        ((trivialZModPCochainsLifted p Q).d 1 2 c) =
      groupCohomology.d₁₂ (ordinaryTrivialZModPLifted (p := p) (Q := Q))
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
  simp [d_succ, d_zero, hom_sub, ContIntertwiningMap.sub_apply,
    coind₁ι_toFun, coind₁Map_toFun]
  have hc := congrArg (fun t ↦ t g (g * h)) (c.2 g)
  change c.1 (g⁻¹ * g) (g⁻¹ * (g * h)) = c.1 g (g * h) at hc
  have hc' : c.1 1 h = c.1 g (g * h) := by simpa using hc
  rw [← hc']
  abel

omit [DiscreteTopology Q] in
/-- Dehomogenization intertwines the degree-two differentials. -/
theorem dehomogenizeTwo_d
    (c : (trivialZModPCochainsLifted p Q).X 2) :
    dehomogenizeThree
        ((trivialZModPCochainsLifted p Q).d 2 3 c) =
      groupCohomology.d₂₃ (ordinaryTrivialZModPLifted (p := p) (Q := Q))
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
  simp [d_succ, d_zero, hom_sub, ContIntertwiningMap.sub_apply,
    coind₁ι_toFun, coind₁Map_toFun]
  have hc := congrArg (fun t ↦ t g (g * h) (g * h * k)) (c.2 g)
  change c.1 (g⁻¹ * g) (g⁻¹ * (g * h))
      (g⁻¹ * (g * h * k)) = c.1 g (g * h) (g * h * k) at hc
  have hc' : c.1 1 h (h * k) = c.1 g (g * h) (g * h * k) := by
    simpa [mul_assoc] using hc
  rw [← hc']
  rw [show g * h * k = g * (h * k) by group]
  abel

/-- Forget topology and the `ZMod p`-linear structure, retaining the
underlying additive group. -/
abbrev continuousCochainsToAddCommGrp (p : ℕ) :
    TopModuleCat (ZMod p) ⥤ AddCommGrpCat :=
  forget₂ (TopModuleCat (ZMod p)) (ModuleCat (ZMod p)) ⋙
    forget₂ (ModuleCat (ZMod p)) AddCommGrpCat

/-- Forget the `Int`-linear structure on ordinary group cochains. -/
abbrev ordinaryCochainsToAddCommGrp : ModuleCat ℤ ⥤ AddCommGrpCat :=
  forget₂ (ModuleCat ℤ) AddCommGrpCat

/-- The degree-one cochain equivalence as an additive-group isomorphism. -/
noncomputable def homogeneousOneCochainAddCommGrpIso :
    (continuousCochainsToAddCommGrp p).obj
        ((trivialZModPCochainsLifted p Q).X 1) ≅
      (ordinaryCochainsToAddCommGrp).obj
        (ModuleCat.of ℤ (Q → ULift (ZMod p))) :=
  homogeneousOneCochainAddEquiv.toAddCommGrpIso

/-- The degree-two cochain equivalence as an additive-group isomorphism. -/
noncomputable def homogeneousTwoCochainAddCommGrpIso :
    (continuousCochainsToAddCommGrp p).obj
        ((trivialZModPCochainsLifted p Q).X 2) ≅
      (ordinaryCochainsToAddCommGrp).obj
        (ModuleCat.of ℤ (Q × Q → ULift (ZMod p))) :=
  homogeneousTwoCochainAddEquiv.toAddCommGrpIso

/-- The degree-three cochain equivalence as an additive-group isomorphism. -/
noncomputable def homogeneousThreeCochainAddCommGrpIso :
    (continuousCochainsToAddCommGrp p).obj
        ((trivialZModPCochainsLifted p Q).X 3) ≅
      (ordinaryCochainsToAddCommGrp).obj
        (ModuleCat.of ℤ (Q × Q × Q → ULift (ZMod p))) :=
  homogeneousThreeCochainAddEquiv.toAddCommGrpIso

/-- For a discrete group, the homogeneous continuous degree-two short
complex is the ordinary inhomogeneous one after forgetting structure. -/
noncomputable def discreteH2ShortComplexIso :
    ((trivialZModPCochainsLifted p Q).sc' 1 2 3).map
        (continuousCochainsToAddCommGrp p) ≅
      (groupCohomology.shortComplexH2
          (ordinaryTrivialZModPLifted (p := p) (Q := Q))).map
        ordinaryCochainsToAddCommGrp := by
  refine ShortComplex.isoMk
    (homogeneousOneCochainAddCommGrpIso (p := p) (Q := Q))
    (homogeneousTwoCochainAddCommGrpIso (p := p) (Q := Q))
    (homogeneousThreeCochainAddCommGrpIso (p := p) (Q := Q)) ?_ ?_
  · ext c
    exact (dehomogenizeOne_d (p := p) (Q := Q) c).symm
  · ext c
    exact (dehomogenizeTwo_d (p := p) (Q := Q) c).symm

end

end ClassFieldTower.Cohomology
