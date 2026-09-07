import ProCGroups.ProP.Zassenhaus.AugmentationFiltration
import ProCGroups.Completion.ProCIntegerPrimePower
import ProCGroups.FoxDifferential.Completed.Continuous.Topology

set_option autoImplicit false
/-!
# Continuous reduction of completed pro-p group algebras modulo p

The pro-`p` integral completed group algebra has both a coefficient index and a
finite group-quotient index.  Fixing the coefficient index at `p ^ 1` leaves a
compatible family over the group quotients.  Its inverse-limit lift is the
canonical continuous reduction map to the completed group algebra over
`ZMod p`.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open FoxDifferential
open ProCGroups
open ProCGroups.Completion
open ProCGroups.InverseSystems

noncomputable section

universe u

variable (p : ℕ) [Fact p.Prime]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The coefficient coordinate supplied by `pGroupPower p 1`, with modulus
definitionally normalized to `p`. -/
def modPCoefficientIndex :
    ProCIntegerIndex (FiniteGroupClass.pGroup p : FiniteGroupClass.{u}) where
  modulus := p
  positive := (Fact.out : Nat.Prime p).pos
  cyclic_mem := by
    have h := (ProCIntegerIndex.pGroupPower p 1).cyclic_mem
    change (FiniteGroupClass.pGroup p).MemAcrossUniverses
      (Multiplicative (ZMod (p ^ 1))) at h
    have hp : p ^ 1 = p := Nat.pow_one p
    rw [hp] at h
    exact h

@[simp]
theorem modPCoefficientIndex_modulus :
    (modPCoefficientIndex p :
      ProCIntegerIndex
        (FiniteGroupClass.pGroup p : FiniteGroupClass.{u})).modulus = p :=
  rfl

/-- Reduction to the fixed `p ^ 1` coefficient coordinate at one finite group
quotient stage. -/
def modPCoefficientReductionStageRingHom
    (U : CompletedGroupAlgebra.CompletedGroupAlgebraIndexInClass G
      (FiniteGroupClass.pGroup p)) :
    ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G →+*
      CompletedGroupAlgebraStageInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G U :=
  zcCompletedGroupAlgebraProjectionRingHom
    (FiniteGroupClass.pGroup p) G (modPCoefficientIndex p, U)

/-- The fixed-coefficient stage maps commute with refinement of finite
`p`-group quotients. -/
theorem modPCoefficientReductionStage_compatible :
    (completedGroupAlgebraSystemInClass
      (FiniteGroupClass.pGroup p) (ZMod p) G).CompatibleMaps
      (fun U => modPCoefficientReductionStageRingHom p G U) := by
  intro U V hUV
  funext x
  have hx := x.2
    (modPCoefficientIndex p, U)
    (modPCoefficientIndex p, V)
    ⟨le_rfl, hUV⟩
  have hsame := zcCompletedGroupAlgebraTransition_sameCoeff
    (FiniteGroupClass.pGroup p) G (modPCoefficientIndex p)
    (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV
  have hsx := congrFun (congrArg DFunLike.coe hsame)
    (zcCompletedGroupAlgebraProjection
      (FiniteGroupClass.pGroup p) G (modPCoefficientIndex p, V) x)
  exact hsx.symm.trans hx

/-- The additive inverse-limit lift of the fixed mod-`p` stage family. -/
def modPCoefficientReductionAddMonoidHom :
    ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G →+
      ModPCompletedGroupAlgebra p G where
  toFun :=
    (completedGroupAlgebraSystemInClass
      (FiniteGroupClass.pGroup p) (ZMod p) G).inverseLimitLift
      (fun U => modPCoefficientReductionStageRingHom p G U)
      (modPCoefficientReductionStage_compatible p G)
  map_zero' := by
    apply completedGroupAlgebraInClass_ext
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
    intro U
    exact map_zero (modPCoefficientReductionStageRingHom p G U)
  map_add' x y := by
    apply completedGroupAlgebraInClass_ext
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
    intro U
    exact map_add (modPCoefficientReductionStageRingHom p G U) x y

/-- Projection of the additive reduction lift is the chosen fixed-coefficient
stage map. -/
@[simp]
theorem completedGroupAlgebraProjectionInClass_modPCoefficientReductionAddMonoidHom
    (U : CompletedGroupAlgebra.CompletedGroupAlgebraIndexInClass G
      (FiniteGroupClass.pGroup p))
    (x : ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G) :
    completedGroupAlgebraProjectionInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G U
        (modPCoefficientReductionAddMonoidHom p G x) =
      modPCoefficientReductionStageRingHom p G U x :=
  rfl

/-- The additive reduction lift is continuous for the two inverse-limit
topologies. -/
theorem continuous_modPCoefficientReductionAddMonoidHom :
    Continuous (modPCoefficientReductionAddMonoidHom p G) := by
  let S := completedGroupAlgebraSystemInClass
    (FiniteGroupClass.pGroup p) (ZMod p) G
  change Continuous
    (S.inverseLimitLift
      (fun U => modPCoefficientReductionStageRingHom p G U)
      (modPCoefficientReductionStage_compatible p G))
  apply S.continuous_inverseLimitLift
  intro U
  let tfin : TopologicalSpace
      (CompletedGroupAlgebraStageInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G U) :=
    S.topologicalSpace U
  let tdisc : TopologicalSpace
      (CompletedGroupAlgebraStageInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G U) := ⊥
  let _ : Finite
      (CompletedGroupAlgebra.CompletedGroupAlgebraQuotientInClass
        G (FiniteGroupClass.pGroup p) U) :=
    CompletedGroupAlgebra.finite_completedGroupAlgebraQuotientInClass
      G (FiniteGroupClass.pGroup p) U
  have hdisc :
      letI : TopologicalSpace
          (CompletedGroupAlgebraStageInClass
            (FiniteGroupClass.pGroup p) (ZMod p) G U) := tfin
      DiscreteTopology
        (CompletedGroupAlgebraStageInClass
          (FiniteGroupClass.pGroup p) (ZMod p) G U) := by
    dsimp [tfin, S,
      CompletedGroupAlgebra.completedGroupAlgebraSystemInClass,
      CompletedGroupAlgebra.CompletedGroupAlgebraStageInClass]
    exact CompletedGroupAlgebra.finiteGroupAlgebraTopology_discrete_of_discrete_coeff
      (S := ZMod p) (CompletedGroupAlgebra.CompletedGroupAlgebraQuotientInClass
        G (FiniteGroupClass.pGroup p) U)
  have ht : tfin = tdisc := by
    dsimp [tdisc]
    exact hdisc.eq_bot
  have htop :
      FoxDifferential.instTopologicalSpaceZCCompletedGroupAlgebraStage
          (FiniteGroupClass.pGroup p) G (modPCoefficientIndex p, U) =
        tdisc := by
    dsimp [tdisc,
      FoxDifferential.instTopologicalSpaceZCCompletedGroupAlgebraStage]
    rfl
  have hcont :=
    FoxDifferential.continuous_zcCompletedGroupAlgebraProjectionRingHom
      (FiniteGroupClass.pGroup p) G (modPCoefficientIndex p, U)
  rw [htop] at hcont
  change @Continuous
    (ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G)
    (CompletedGroupAlgebraStageInClass
      (FiniteGroupClass.pGroup p) (ZMod p) G U)
    _ tfin (modPCoefficientReductionStageRingHom p G U)
  rw [ht]
  change @Continuous
    (ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G)
    (FoxDifferential.ZCCompletedGroupAlgebraStage
      (FiniteGroupClass.pGroup p) G (modPCoefficientIndex p, U))
    _ tdisc
    (FoxDifferential.zcCompletedGroupAlgebraProjectionRingHom
      (FiniteGroupClass.pGroup p) G (modPCoefficientIndex p, U))
  exact hcont

/-- The canonical continuous ring homomorphism reducing completed pro-`p`
integer coefficients modulo `p`. -/
def modPCoefficientReduction :
    ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G →+*
      ModPCompletedGroupAlgebra p G where
  toFun := modPCoefficientReductionAddMonoidHom p G
  map_zero' := map_zero (modPCoefficientReductionAddMonoidHom p G)
  map_one' := by
    apply completedGroupAlgebraInClass_ext
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
    intro U
    exact map_one (modPCoefficientReductionStageRingHom p G U)
  map_add' := map_add (modPCoefficientReductionAddMonoidHom p G)
  map_mul' := by
    intro x y
    apply completedGroupAlgebraInClass_ext
      (R := ZMod p) (G := G) (FiniteGroupClass.pGroup p)
    intro U
    exact map_mul (modPCoefficientReductionStageRingHom p G U) x y

/-- Projection of coefficient reduction is the fixed `p ^ 1` source
projection. -/
@[simp]
theorem completedGroupAlgebraProjectionInClass_modPCoefficientReduction
    (U : CompletedGroupAlgebra.CompletedGroupAlgebraIndexInClass G
      (FiniteGroupClass.pGroup p))
    (x : ZCCompletedGroupAlgebra (FiniteGroupClass.pGroup p) G) :
    completedGroupAlgebraProjectionInClass
        (FiniteGroupClass.pGroup p) (ZMod p) G U
        (modPCoefficientReduction p G x) =
      modPCoefficientReductionStageRingHom p G U x :=
  rfl

/-- Coefficient reduction is continuous. -/
theorem continuous_modPCoefficientReduction :
    Continuous (modPCoefficientReduction p G) :=
  continuous_modPCoefficientReductionAddMonoidHom p G

end

end ClassFieldTower.ProP
