import ProCGroups.FoxDifferential.Completed.Continuous.Universal.FiniteStage
import ProCGroups.InverseSystems.Basic

set_option autoImplicit false

/-!
# Fox differential: completed — continuous — universal — system

The principal declarations in this module are:

- `zcCompletedDifferentialModuleStageSystem`
  The inverse system of finite source, target, and coefficient stages of \(A_{\psi}(C)\).
- `zcCompletedDifferentialPreModuleStageSystem`
  The inverse system of finite pre-modules before quotienting by crossed-differential relations.
- `zcCompletedDifferentialModuleStageSystem_map_apply`
  The system map on completed differential modules is evaluated coordinatewise at each finite
  coefficient stage.
- `zcCompletedDifferentialModuleStageSystem_projection_compatible`
  Inverse-limit projections of the finite \(A_{\psi}(C)\) stage system are compatible with
  transition maps.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (C : ProCGroups.FiniteGroupClass.{u})
variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable (ψ : G →* H)

/-- The inverse system of finite source, target, and coefficient stages of \(A_{\psi}(C)\). -/
def zcCompletedDifferentialModuleStageSystem :
    InverseSystem (I := ZCCompletedDifferentialModuleIndex C ψ) where
  X := fun i => ZCCompletedDifferentialModuleStage C ψ i
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij => zcCompletedDifferentialModuleStageTransition C ψ hij
  continuous_map := by
    intro i j hij
    let : TopologicalSpace (ZCCompletedDifferentialModuleStage C ψ i) := ⊥
    let : TopologicalSpace (ZCCompletedDifferentialModuleStage C ψ j) := ⊥
    let : DiscreteTopology (ZCCompletedDifferentialModuleStage C ψ j) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (zcCompletedDifferentialModuleStageTransition_id C ψ i)) x
  map_comp := by
    intro i j k hij hjk
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (zcCompletedDifferentialModuleStageTransition_comp C ψ hij hjk)) x

/-- Addition in the finite-stage completed differential-module system is defined coordinatewise. -/
instance instAddCommGroupZCCompletedDifferentialModuleStageSystemStage
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    AddCommGroup ((zcCompletedDifferentialModuleStageSystem C ψ).X i) := by
  dsimp [zcCompletedDifferentialModuleStageSystem]
  infer_instance

/--
The inverse system of finite-stage group algebras has addition defined coordinatewise on
compatible families.
-/
instance instIsAddGroupSystemZCCompletedDifferentialModuleStageSystem :
    IsAddGroupSystem (zcCompletedDifferentialModuleStageSystem C ψ) where
  map_zero := by
    intro i j hij
    exact (zcCompletedDifferentialModuleStageTransition C ψ hij).map_zero
  map_add := by
    intro i j hij x y
    exact (zcCompletedDifferentialModuleStageTransition C ψ hij).map_add x y
  map_neg := by
    intro i j hij x
    exact map_neg (zcCompletedDifferentialModuleStageTransition C ψ hij) x

omit [IsTopologicalGroup G] in
/--
The system map on completed differential modules is evaluated coordinatewise at each finite
coefficient stage.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageSystem_map_apply
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j)
    (x : ZCCompletedDifferentialModuleStage C ψ j) :
    (zcCompletedDifferentialModuleStageSystem C ψ).map hij x =
      zcCompletedDifferentialModuleStageTransition C ψ hij x :=
  rfl

omit [IsTopologicalGroup G] in
/--
Inverse-limit projections of the finite \(A_{\psi}(C)\) stage system are compatible with
transition maps.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageSystem_projection_compatible
    (x : (zcCompletedDifferentialModuleStageSystem C ψ).inverseLimit)
    (i j : ZCCompletedDifferentialModuleIndex C ψ) (hij : i ≤ j) :
    zcCompletedDifferentialModuleStageTransition C ψ hij
        ((zcCompletedDifferentialModuleStageSystem C ψ).projection j x) =
      (zcCompletedDifferentialModuleStageSystem C ψ).projection i x :=
  (zcCompletedDifferentialModuleStageSystem C ψ).projection_compatible x i j hij

/--
The inverse system of finite pre-modules before quotienting by crossed-differential relations.
-/
def zcCompletedDifferentialPreModuleStageSystem :
    InverseSystem (I := ZCCompletedDifferentialModuleIndex C ψ) where
  X := fun i =>
    CrossedDifferentialPreModule
      (zcCompletedDifferentialModuleStageRing C ψ i)
      (zcCompletedDifferentialModuleStageSource C ψ i)
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij => zcCompletedDifferentialModulePreStageTransition C ψ hij
  continuous_map := by
    intro i j hij
    let : TopologicalSpace
        (CrossedDifferentialPreModule
          (zcCompletedDifferentialModuleStageRing C ψ i)
          (zcCompletedDifferentialModuleStageSource C ψ i)) := ⊥
    let : TopologicalSpace
        (CrossedDifferentialPreModule
          (zcCompletedDifferentialModuleStageRing C ψ j)
          (zcCompletedDifferentialModuleStageSource C ψ j)) := ⊥
    let : DiscreteTopology
        (CrossedDifferentialPreModule
          (zcCompletedDifferentialModuleStageRing C ψ j)
          (zcCompletedDifferentialModuleStageSource C ψ j)) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (zcCompletedDifferentialModulePreStageTransition_id C ψ i)) x
  map_comp := by
    intro i j k hij hjk
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (zcCompletedDifferentialModulePreStageTransition_comp C ψ hij hjk)) x

/-- Compatible inverse-limit families of finite pre-stage elements. -/
abbrev ZCCompletedDifferentialPreModuleStageFamily : Type u :=
  (zcCompletedDifferentialPreModuleStageSystem C ψ).inverseLimit

omit [IsTopologicalGroup G] in
/--
The finite pre-module inverse-system map evaluates as the explicit pre-stage transition.
-/
@[simp]
theorem zcCompletedDifferentialPreModuleStageSystem_map_apply
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j)
    (x : CrossedDifferentialPreModule
      (zcCompletedDifferentialModuleStageRing C ψ j)
      (zcCompletedDifferentialModuleStageSource C ψ j)) :
    (zcCompletedDifferentialPreModuleStageSystem C ψ).map hij x =
      zcCompletedDifferentialModulePreStageTransition C ψ hij x :=
  rfl

omit [IsTopologicalGroup G] in
/--
The explicit finite pre-stage reductions of a completed pre-module element are compatible with
finite transitions.
-/
theorem zcCompletedDifferentialPreModuleStageSystem_compatible_preStageMap :
    (zcCompletedDifferentialPreModuleStageSystem C ψ).CompatibleMaps
      (fun i : ZCCompletedDifferentialModuleIndex C ψ =>
        zcCompletedDifferentialModulePreStageMap C ψ i) := by
  intro i j hij
  funext x
  exact zcCompletedDifferentialModulePreStageTransition_preStageMap C ψ hij x

/--
The finite-stage family map sends a completed pre-module element to its compatible family of
finite source, target, and coefficient stages.
-/
def zcCompletedDifferentialPreModuleStageFamilyMap :
    CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G →
      ZCCompletedDifferentialPreModuleStageFamily C ψ :=
  (zcCompletedDifferentialPreModuleStageSystem C ψ).inverseLimitLift
    (fun i : ZCCompletedDifferentialModuleIndex C ψ =>
      zcCompletedDifferentialModulePreStageMap C ψ i)
    (zcCompletedDifferentialPreModuleStageSystem_compatible_preStageMap C ψ)

omit [IsTopologicalGroup G] in
/--
Projecting the finite-stage pre-module family map at a stage recovers the explicit pre-stage map
at that stage.
-/
@[simp]
theorem zcCompletedDifferentialPreModuleStageFamilyMap_projection
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :
    (zcCompletedDifferentialPreModuleStageSystem C ψ).projection i
        (zcCompletedDifferentialPreModuleStageFamilyMap C ψ x) =
      zcCompletedDifferentialModulePreStageMap C ψ i x :=
  rfl

end

end FoxDifferential
