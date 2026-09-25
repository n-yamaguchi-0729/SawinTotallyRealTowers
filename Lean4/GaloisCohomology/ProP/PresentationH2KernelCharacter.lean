/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.InvariantKernelH1
import GaloisCohomology.ProP.PresentationH2Primitive

set_option autoImplicit false
/-!
# Kernel characters extracted from presentation degree-two classes

The normalized free-source primitive restricts to a continuous conjugation-invariant character
of the presentation kernel.  The construction is linear in the degree-two cohomology class.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups
open PresentationH2Aux

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {d r : ℕ}
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}

local instance presentationContinuousH1Module
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    Module (ZMod p) (ContinuousH1ZMod (p := p) (G := H)) :=
  continuousH1ZModModule

namespace PresentationH2Aux

/-- The normalized inhomogeneous value of the chosen free-source primitive. -/
def presentationNormalizedPrimitiveValue
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (f : sourceData.carrier) : ZMod p :=
  ((presentationPrimitive P x).1 1 f - (presentationPrimitive P x).1 1 1).down

theorem presentationPrimitive_base
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2) :
    (presentationPrimitive P x).1 1 1 =
      (((Cohomology.trivialZModPCochainsLifted p G).iCycles 2).hom
        (targetCocycleSection x)).1 1 1 1 := by
  simpa using presentationPrimitive_boundary_apply P x 1 1 1

theorem presentationNormalizedPrimitive_mul_of_left_kernel
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (a b : sourceData.carrier) (ha : P.quotient a = 1) :
    presentationNormalizedPrimitiveValue P x (a * b) =
      presentationNormalizedPrimitiveValue P x a +
        presentationNormalizedPrimitiveValue P x b := by
  have hboundary := presentationPrimitive_boundary_apply P x 1 a (a * b)
  have hinv := presentationPrimitive_leftInvariant P x a a (a * b)
  have hinv' : (presentationPrimitive P x).1 a (a * b) =
      (presentationPrimitive P x).1 1 b := by
    rw [← hinv]
    congr 2
    all_goals group
  have hq1 : P.quotient 1 = 1 := P.quotient.map_one
  have hqab : P.quotient (a * b) = P.quotient a * P.quotient b := P.quotient.map_mul a b
  rw [hinv', hq1, ha, hqab, ha, one_mul,
    homogeneousTwoCocycle_one_one] at hboundary
  have hbase := presentationPrimitive_base P x
  rw [← hbase] at hboundary
  unfold presentationNormalizedPrimitiveValue
  have hu :
      (presentationPrimitive P x).1 1 (a * b) -
          (presentationPrimitive P x).1 1 1 =
        ((presentationPrimitive P x).1 1 a -
            (presentationPrimitive P x).1 1 1) +
          ((presentationPrimitive P x).1 1 b -
            (presentationPrimitive P x).1 1 1) := by
    have hdiff :
        (presentationPrimitive P x).1 1 b -
            (presentationPrimitive P x).1 1 1 =
          (presentationPrimitive P x).1 1 (a * b) -
            (presentationPrimitive P x).1 1 a := by
      apply (sub_eq_iff_eq_add).2
      calc
        _ = (presentationPrimitive P x).1 1 1 +
              ((presentationPrimitive P x).1 1 (a * b) -
                (presentationPrimitive P x).1 1 a) :=
          (sub_eq_iff_eq_add.mp hboundary)
        _ = _ := add_comm _ _
    calc
      _ = ((presentationPrimitive P x).1 1 (a * b) -
            (presentationPrimitive P x).1 1 a) +
          ((presentationPrimitive P x).1 1 a -
            (presentationPrimitive P x).1 1 1) := by abel
      _ = ((presentationPrimitive P x).1 1 b -
            (presentationPrimitive P x).1 1 1) +
          ((presentationPrimitive P x).1 1 a -
            (presentationPrimitive P x).1 1 1) := by rw [← hdiff]
      _ = _ := add_comm _ _
  have hd := congrArg ULift.down hu
  change
    ((presentationPrimitive P x).1 1 (a * b) -
        (presentationPrimitive P x).1 1 1).down =
      ((presentationPrimitive P x).1 1 a -
          (presentationPrimitive P x).1 1 1).down +
        ((presentationPrimitive P x).1 1 b -
          (presentationPrimitive P x).1 1 1).down at hd
  exact hd

theorem presentationNormalizedPrimitive_mul_of_right_kernel
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (a b : sourceData.carrier) (hb : P.quotient b = 1) :
    presentationNormalizedPrimitiveValue P x (a * b) =
      presentationNormalizedPrimitiveValue P x a +
        presentationNormalizedPrimitiveValue P x b := by
  have hboundary := presentationPrimitive_boundary_apply P x 1 a (a * b)
  have hinv := presentationPrimitive_leftInvariant P x a a (a * b)
  have hinv' : (presentationPrimitive P x).1 a (a * b) =
      (presentationPrimitive P x).1 1 b := by
    rw [← hinv]
    congr 2
    all_goals group
  have hq1 : P.quotient 1 = 1 := P.quotient.map_one
  have hqab : P.quotient (a * b) = P.quotient a * P.quotient b := P.quotient.map_mul a b
  rw [hinv', hq1, hqab, hb, mul_one,
    homogeneousTwoCocycle_one_diag] at hboundary
  have hbase := presentationPrimitive_base P x
  rw [← hbase] at hboundary
  unfold presentationNormalizedPrimitiveValue
  have hu :
      (presentationPrimitive P x).1 1 (a * b) -
          (presentationPrimitive P x).1 1 1 =
        ((presentationPrimitive P x).1 1 a -
            (presentationPrimitive P x).1 1 1) +
          ((presentationPrimitive P x).1 1 b -
            (presentationPrimitive P x).1 1 1) := by
    have hdiff :
        (presentationPrimitive P x).1 1 b -
            (presentationPrimitive P x).1 1 1 =
          (presentationPrimitive P x).1 1 (a * b) -
            (presentationPrimitive P x).1 1 a := by
      apply (sub_eq_iff_eq_add).2
      calc
        _ = (presentationPrimitive P x).1 1 1 +
              ((presentationPrimitive P x).1 1 (a * b) -
                (presentationPrimitive P x).1 1 a) :=
          (sub_eq_iff_eq_add.mp hboundary)
        _ = _ := add_comm _ _
    calc
      _ = ((presentationPrimitive P x).1 1 (a * b) -
            (presentationPrimitive P x).1 1 a) +
          ((presentationPrimitive P x).1 1 a -
            (presentationPrimitive P x).1 1 1) := by abel
      _ = ((presentationPrimitive P x).1 1 b -
            (presentationPrimitive P x).1 1 1) +
          ((presentationPrimitive P x).1 1 a -
            (presentationPrimitive P x).1 1 1) := by rw [← hdiff]
      _ = _ := add_comm _ _
  have hd := congrArg ULift.down hu
  change
    ((presentationPrimitive P x).1 1 (a * b) -
        (presentationPrimitive P x).1 1 1).down =
      ((presentationPrimitive P x).1 1 a -
          (presentationPrimitive P x).1 1 1).down +
        ((presentationPrimitive P x).1 1 b -
          (presentationPrimitive P x).1 1 1).down at hd
  exact hd

/-- The continuous kernel character extracted from a degree-two target class. -/
noncomputable def presentationKernelH1OfClass
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2) :
    ContinuousH1ZMod (p := p) (G := P.quotient.toMonoidHom.ker) where
  toFun n := presentationNormalizedPrimitiveValue P x n.toMul
  map_zero' := by
    change presentationNormalizedPrimitiveValue P x 1 = 0
    unfold presentationNormalizedPrimitiveValue
    rw [sub_self]
    rfl
  map_add' := by
    intro n m
    change presentationNormalizedPrimitiveValue P x ((n.toMul : _) * m.toMul) =
      presentationNormalizedPrimitiveValue P x n.toMul +
        presentationNormalizedPrimitiveValue P x m.toMul
    apply presentationNormalizedPrimitive_mul_of_left_kernel P x
    exact n.toMul.2
  continuous_toFun := by
    change Continuous fun n : P.quotient.toMonoidHom.ker ↦
      (((presentationPrimitive P x).1 1 (n : sourceData.carrier)) -
        (presentationPrimitive P x).1 1 1).down
    exact ((ContinuousLinearEquiv.ulift :
      ULift.{u} (ZMod p) ≃L[ZMod p] ZMod p).continuous).comp <|
        (((presentationPrimitive P x).1 1).continuous.comp continuous_subtype_val).sub
          continuous_const

theorem presentationKernelH1OfClass_invariant
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2)
    (f : sourceData.carrier) (n : P.quotient.toMonoidHom.ker) :
    presentationKernelH1OfClass P x
        (Additive.ofMul (MulAut.conjNormal f n)) =
      presentationKernelH1OfClass P x (Additive.ofMul n) := by
  have hn : P.quotient (n : sourceData.carrier) = 1 := n.2
  have hconj :
      P.quotient ((MulAut.conjNormal f n : P.quotient.toMonoidHom.ker) :
        sourceData.carrier) = 1 := (MulAut.conjNormal f n).2
  have hleft := presentationNormalizedPrimitive_mul_of_left_kernel P x
    (n : sourceData.carrier) f⁻¹ hn
  have hright := presentationNormalizedPrimitive_mul_of_right_kernel P x
    f⁻¹ ((MulAut.conjNormal f n : P.quotient.toMonoidHom.ker) : sourceData.carrier) hconj
  have hprod :
      (n : sourceData.carrier) * f⁻¹ =
        f⁻¹ * ((MulAut.conjNormal f n : P.quotient.toMonoidHom.ker) :
          sourceData.carrier) := by
    simp only [MulAut.conjNormal_apply]
    group
  rw [← hprod] at hright
  change presentationNormalizedPrimitiveValue P x
      ((MulAut.conjNormal f n : P.quotient.toMonoidHom.ker) : sourceData.carrier) =
    presentationNormalizedPrimitiveValue P x (n : sourceData.carrier)
  calc
    _ = presentationNormalizedPrimitiveValue P x ((n : sourceData.carrier) * f⁻¹) -
        presentationNormalizedPrimitiveValue P x f⁻¹ := by
      rw [hright]
      abel
    _ = _ := by
      rw [hleft]
      abel

/-- The extracted character, together with its free-source conjugation invariance. -/
noncomputable def presentationH2KernelClass
    (P : FiniteProPPresentation p d r sourceData G)
    (x : Cohomology.continuousCohomologyZModPLifted p G 2) :
    InvariantKernelH1 P :=
  ⟨presentationKernelH1OfClass P x, presentationKernelH1OfClass_invariant P x⟩

end PresentationH2Aux

/-- The linear map from target degree-two cohomology to invariant presentation-kernel classes. -/
noncomputable def presentationH2ToInvariantKernelH1
    (P : FiniteProPPresentation p d r sourceData G) :
    Cohomology.continuousCohomologyZModPLifted p G 2 →ₗ[ZMod p]
      InvariantKernelH1 P where
  toFun := presentationH2KernelClass P
  map_add' x y := by
    apply Subtype.ext
    ext n
    change presentationNormalizedPrimitiveValue P (x + y) n.toMul =
      presentationNormalizedPrimitiveValue P x n.toMul +
        presentationNormalizedPrimitiveValue P y n.toMul
    unfold presentationNormalizedPrimitiveValue
    rw [map_add]
    change
      (((presentationPrimitive P x).1 1 n.toMul +
          (presentationPrimitive P y).1 1 n.toMul) -
        ((presentationPrimitive P x).1 1 1 +
          (presentationPrimitive P y).1 1 1)).down = _
    have hu :
        ((presentationPrimitive P x).1 1 n.toMul +
            (presentationPrimitive P y).1 1 n.toMul) -
          ((presentationPrimitive P x).1 1 1 +
            (presentationPrimitive P y).1 1 1) =
        ((presentationPrimitive P x).1 1 n.toMul -
            (presentationPrimitive P x).1 1 1) +
          ((presentationPrimitive P y).1 1 n.toMul -
            (presentationPrimitive P y).1 1 1) := by abel
    have hd := congrArg ULift.down hu
    change _ =
      ((presentationPrimitive P x).1 1 n.toMul -
          (presentationPrimitive P x).1 1 1).down +
        ((presentationPrimitive P y).1 1 n.toMul -
          (presentationPrimitive P y).1 1 1).down at hd
    exact hd
  map_smul' a x := by
    apply Subtype.ext
    ext n
    let ev : ContinuousH1ZMod (p := p) (G := P.quotient.toMonoidHom.ker) →+ ZMod p :=
      { toFun := fun χ ↦ χ n
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
    change presentationNormalizedPrimitiveValue P (a • x) n.toMul =
      ev (a • (presentationH2KernelClass P x).1)
    rw [ZMod.map_smul ev]
    change presentationNormalizedPrimitiveValue P (a • x) n.toMul =
      a • presentationNormalizedPrimitiveValue P x n.toMul
    unfold presentationNormalizedPrimitiveValue
    rw [map_smul]
    change
      (a • (presentationPrimitive P x).1 1 n.toMul -
        a • (presentationPrimitive P x).1 1 1).down =
      a • ((presentationPrimitive P x).1 1 n.toMul -
        (presentationPrimitive P x).1 1 1).down
    rw [← smul_sub]
    rfl

end


end ClassFieldTower.ProP
