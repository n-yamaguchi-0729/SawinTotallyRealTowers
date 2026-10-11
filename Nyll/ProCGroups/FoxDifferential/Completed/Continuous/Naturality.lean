/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.Continuous.Free.Rules

/-!
# Fox differential: completed — continuous — naturality

The principal declarations in this module are:

- `zcCompletedFoxSemidirectMapTarget`
  Target functoriality for completed Fox semidirect products.
- `zcCompletedFoxSemidirectMapTargetHom`
  Target functoriality for completed Fox semidirect products as a continuous homomorphism.
- `continuous_zcCompletedGroupAlgebraMap`
  The completed group-algebra map induced by a continuous target homomorphism is continuous.
- `zcCompletedGroupAlgebraMap_surjective_of_surjective`
  A surjective target homomorphism induces a surjective completed group-algebra map.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.Completion
open ProCGroups.InverseSystems
open ProCGroups.ProC
open scoped BigOperators

universe u v

section ContinuousTargetMaps

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (hC : ProCGroups.FiniteGroupClass.Hereditary C)
variable {H K : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- The completed group-algebra map induced by a continuous target homomorphism is continuous. -/
theorem continuous_zcCompletedGroupAlgebraMap (η : H →ₜ* K) :
    Continuous (zcCompletedGroupAlgebraMap C hC η) := by
  refine Continuous.subtype_mk (p := ZCCompletedGroupAlgebraCompatible C K)
    (continuous_pi fun i => ?_) (fun x => (zcCompletedGroupAlgebraMap C hC η x).2)
  let sourceIndex : ZCCompletedGroupAlgebraIndex C H :=
    (i.1, completedGroupAlgebraComapIndexInClass
      (G := H) (H := K) C hC η i.2)
  let : TopologicalSpace (ZCCompletedGroupAlgebraStage C H sourceIndex) := ⊥
  let : DiscreteTopology (ZCCompletedGroupAlgebraStage C H sourceIndex) := ⟨rfl⟩
  have hstage : Continuous (zcCompletedGroupAlgebraMapStage C hC η i) :=
    continuous_of_discreteTopology
  exact hstage.comp ((continuous_apply sourceIndex).comp continuous_subtype_val)

/-- A surjective target homomorphism induces a surjective completed group-algebra map. -/
theorem zcCompletedGroupAlgebraMap_surjective_of_surjective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (η : H →ₜ* K) (hη : Function.Surjective η) :
    Function.Surjective (zcCompletedGroupAlgebraMap C hC η) := by
  let S := zcCompletedGroupAlgebraSystem C K
  let ψ : ∀ i : ZCCompletedGroupAlgebraIndex C K,
      ZCCompletedGroupAlgebra C H → S.X i :=
    fun i x => zcCompletedGroupAlgebraProjection C K i
      (zcCompletedGroupAlgebraMap C hC η x)
  have hψcont : ∀ i, Continuous (ψ i) := by
    intro i
    exact (continuous_apply i).comp
      (continuous_subtype_val.comp (continuous_zcCompletedGroupAlgebraMap C hC η))
  have hψcompat : S.CompatibleMaps ψ := by
    intro i j hij
    funext x
    change zcCompletedGroupAlgebraTransition C K hij
        (zcCompletedGroupAlgebraProjection C K j
          (zcCompletedGroupAlgebraMap C hC η x)) =
      zcCompletedGroupAlgebraProjection C K i
        (zcCompletedGroupAlgebraMap C hC η x)
    exact (zcCompletedGroupAlgebraMap C hC η x).2 i j hij
  have hψsurj : ∀ i, Function.Surjective (ψ i) := by
    intro i y
    rcases zcCompletedGroupAlgebraMapStage_surjective_of_surjective
        C hC η hη i y with ⟨y₀, hy₀⟩
    rcases zcCompletedGroupAlgebraProjection_surjective C H
        (i.1, completedGroupAlgebraComapIndexInClass
          (G := H) (H := K) C hC η i.2) y₀ with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    dsimp [ψ]
    rw [hx, hy₀]
  let : Nonempty (ZCCompletedGroupAlgebraIndex C K) :=
    ⟨(ProCIntegerIndex.terminal (C := C) inferInstance, zcCompletedGroupAlgebraTopIndex C K)⟩
  have hdir : Directed (· ≤ ·)
      (id : ZCCompletedGroupAlgebraIndex C K → ZCCompletedGroupAlgebraIndex C K) := by
    intro i j
    rcases ProCIntegerIndex.directed_of_formation hForm i.1 j.1 with
      ⟨n, hin, hjn⟩
    rcases directed_openNormalSubgroupInClass
        (C := C) (G := K) hForm i.2 j.2 with
      ⟨U, hiU, hjU⟩
    exact ⟨(n, U), ⟨hin, hiU⟩, ⟨hjn, hjU⟩⟩
  let : ∀ i : ZCCompletedGroupAlgebraIndex C K, T2Space (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    change @T2Space (ZCCompletedGroupAlgebraStage C K i) ⊥
    exact @DiscreteTopology.toT2Space _ ⊥ ⟨rfl⟩
  have hlift : Function.Surjective (S.inverseLimitLift ψ hψcompat) :=
    S.surjective_inverseLimitLift ψ hψcont hψcompat hψsurj hdir
  intro y
  rcases hlift y with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  apply Subtype.ext
  funext i
  have hi := congrArg (fun z : S.inverseLimit => S.projection i z) hx
  convert hi using 1 <;> rfl

/-- A surjective completed group-algebra map is a quotient map. -/
theorem isQuotientMap_zcCompletedGroupAlgebraMap_of_surjective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (η : H →ₜ* K) (hη : Function.Surjective η) :
    Topology.IsQuotientMap (zcCompletedGroupAlgebraMap C hC η) :=
  Topology.IsQuotientMap.of_surjective_continuous
    (zcCompletedGroupAlgebraMap_surjective_of_surjective C hC hForm η hη)
    (continuous_zcCompletedGroupAlgebraMap C hC η)

/--
A surjective completed group-algebra map is an open quotient map as an additive-group
homomorphism.
-/
theorem isOpenQuotientMap_zcCompletedGroupAlgebraMap_of_surjective
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (η : H →ₜ* K) (hη : Function.Surjective η) :
    IsOpenQuotientMap (zcCompletedGroupAlgebraMap C hC η) :=
  AddMonoidHom.isOpenQuotientMap_of_isQuotientMap
    (isQuotientMap_zcCompletedGroupAlgebraMap_of_surjective C hC hForm η hη)

variable {X : Type v}

/-- The coordinatewise target map on completed Fox-coordinate vectors is continuous. -/
theorem continuous_zcFreeFoxCoordinatesMap (η : H →ₜ* K) :
    Continuous (zcFreeFoxCoordinatesMap (X := X) C hC η) := by
  refine continuous_pi fun x => ?_
  exact (continuous_zcCompletedGroupAlgebraMap C hC η).comp (continuous_apply x)

end ContinuousTargetMaps

section SourceBoundaryNaturality

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (hC : ProCGroups.FiniteGroupClass.Hereditary C)
variable {X H K : Type u} [Fintype X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- Source-shaped completed Fox boundary maps are natural in the target group. -/
theorem freeProCZCCompletedFoxBoundary_mapTarget
    (η : H →ₜ* K) (φ : X → H)
    (v : ZCFreeFoxCoordinates C (X := X) (H := H)) :
    zcCompletedGroupAlgebraMap C hC η (freeProCZCCompletedFoxBoundary C φ v) =
      freeProCZCCompletedFoxBoundary C (fun x : X => η (φ x))
        (zcFreeFoxCoordinatesMap (X := X) C hC η v) := by
  simp only [freeProCZCCompletedFoxBoundary_apply, map_sum, map_mul, map_sub,
    zcCompletedGroupAlgebraMap_groupLike, map_one, zcFreeFoxCoordinatesMap]

end SourceBoundaryNaturality

section SemidirectTargetMap

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (hC : ProCGroups.FiniteGroupClass.Hereditary C)
variable {X H K : Type u} [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- Target functoriality for completed Fox semidirect products. -/
def zcCompletedFoxSemidirectMapTarget (η : H →ₜ* K) :
    ZCCompletedFoxSemidirect C X H →* ZCCompletedFoxSemidirect C X K where
  toFun a :=
    { left := zcFreeFoxCoordinatesMap (X := X) C hC η a.left
      right := η a.right }
  map_one' := by
    ext x
    · simp only [ZCCompletedFoxSemidirect.one_left, zcFreeFoxCoordinatesMap_apply,
        Pi.zero_apply, map_zero, zcCompletedGroupAlgebraProjection_zero]
    · simp only [ZCCompletedFoxSemidirect.one_right, map_one]
  map_mul' a b := by
    ext x
    · simp only [ZCCompletedFoxSemidirect.mul_left, zcFreeFoxCoordinatesMap_apply,
        Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul,
        zcCompletedGroupAlgebraMap_groupLike, zcCompletedGroupAlgebraProjection_add,
        zcCompletedGroupAlgebraProjection_map, zcCompletedGroupAlgebraProjection_mul,
        zcCompletedGroupAlgebraProjection_groupLike,
        MonoidAlgebra.coeff_add]
    · simp only [ZCCompletedFoxSemidirect.mul_right, map_mul]

omit [DecidableEq X] in
/--
This declaration identifies the left component of the target map on completed Fox semidirect
products.
-/
@[simp]
theorem zcCompletedFoxSemidirectMapTarget_left
    (η : H →ₜ* K) (a : ZCCompletedFoxSemidirect C X H) :
    (zcCompletedFoxSemidirectMapTarget (X := X) C hC η a).left =
      zcFreeFoxCoordinatesMap (X := X) C hC η a.left :=
  rfl

omit [DecidableEq X] in
/--
This declaration identifies the right component of the target map on completed Fox semidirect
products.
-/
@[simp]
theorem zcCompletedFoxSemidirectMapTarget_right
    (η : H →ₜ* K) (a : ZCCompletedFoxSemidirect C X H) :
    (zcCompletedFoxSemidirectMapTarget (X := X) C hC η a).right = η a.right :=
  rfl

omit [DecidableEq X] in
/-- The target map on completed Fox semidirect products is continuous. -/
theorem continuous_zcCompletedFoxSemidirectMapTarget
    (η : H →ₜ* K) :
    Continuous (zcCompletedFoxSemidirectMapTarget (X := X) C hC η) := by
  rw [continuous_induced_rng]
  refine (continuous_zcFreeFoxCoordinatesMap (X := X) C hC η).comp
      (continuous_zcCompletedFoxSemidirect_left C X H) |>.prodMk ?_
  exact η.continuous_toFun.comp (continuous_zcCompletedFoxSemidirect_right C X H)

/-- Target functoriality for completed Fox semidirect products as a continuous homomorphism. -/
def zcCompletedFoxSemidirectMapTargetHom (η : H →ₜ* K) :
    ZCCompletedFoxSemidirect C X H →ₜ* ZCCompletedFoxSemidirect C X K where
  toMonoidHom := zcCompletedFoxSemidirectMapTarget (X := X) C hC η
  continuous_toFun := continuous_zcCompletedFoxSemidirectMapTarget (X := X) C hC η

omit [DecidableEq X] in
/-- The continuous target map has the expected underlying homomorphism. -/
@[simp]
theorem zcCompletedFoxSemidirectMapTargetHom_toMonoidHom
    (η : H →ₜ* K) :
    (zcCompletedFoxSemidirectMapTargetHom (X := X) C hC η).toMonoidHom =
      zcCompletedFoxSemidirectMapTarget (X := X) C hC η :=
  rfl

omit [DecidableEq X] in
/--
This declaration identifies the left component of the continuous target map on completed Fox
semidirect products.
-/
@[simp]
theorem zcCompletedFoxSemidirectMapTargetHom_left
    (η : H →ₜ* K) (a : ZCCompletedFoxSemidirect C X H) :
    (zcCompletedFoxSemidirectMapTargetHom (X := X) C hC η a).left =
      zcFreeFoxCoordinatesMap (X := X) C hC η a.left :=
  rfl

omit [DecidableEq X] in
/--
This declaration identifies the right component of the continuous target map on completed Fox
semidirect products.
-/
@[simp]
theorem zcCompletedFoxSemidirectMapTargetHom_right
    (η : H →ₜ* K) (a : ZCCompletedFoxSemidirect C X H) :
    (zcCompletedFoxSemidirectMapTargetHom (X := X) C hC η a).right = η a.right :=
  rfl

end SemidirectTargetMap

section SourceNaturality

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable (hC : ProCGroups.FiniteGroupClass.Hereditary C)
include hC
variable {X F H K : Type u}
variable [Fintype X] [DecidableEq X] [TopologicalSpace X] [DiscreteTopology X]
variable [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
variable [CompactSpace (ZCCompletedFoxSemidirect C X H)]
variable [T2Space (ZCCompletedFoxSemidirect C X H)]
variable [TotallyDisconnectedSpace (ZCCompletedFoxSemidirect C X H)]
variable [CompactSpace (ZCCompletedFoxSemidirect C X K)]
variable [T2Space (ZCCompletedFoxSemidirect C X K)]
variable [TotallyDisconnectedSpace (ZCCompletedFoxSemidirect C X K)]

omit [Fintype X] in
/-- Target naturality of the canonical completed Fox semidirect lift. -/
theorem freeProCZCCompletedFoxSemidirectLift_mapTarget
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htargetH :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (htargetK :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X K))
    (η : H →ₜ* K) (φ : X → H) (g : F) :
    zcCompletedFoxSemidirectMapTarget (X := X) C hC η
        (freeProCZCCompletedFoxSemidirectLift
          (C := C) hι htargetH φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ) g) =
      freeProCZCCompletedFoxSemidirectLift
        (C := C) hι htargetK (fun x : X => η (φ x))
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X K (fun x :
            X => η (φ x))) g := by
  let hφH : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φ) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ
  let φK : X → K := fun x => η (φ x)
  let hφK : Continuous (freeProCZCCompletedFoxSemidirectGenerator (C := C) φK) :=
    continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X K φK
  let f : F →* ZCCompletedFoxSemidirect C X K :=
    (zcCompletedFoxSemidirectMapTarget (X := X) C hC η).comp
      (freeProCZCCompletedFoxSemidirectLift
        (C := C) hι htargetH φ hφH)
  let h : F →* ZCCompletedFoxSemidirect C X K :=
    freeProCZCCompletedFoxSemidirectLift
      (C := C) hι htargetK φK hφK
  have hf_continuous : Continuous f :=
    (continuous_zcCompletedFoxSemidirectMapTarget
      (X := X) C hC η).comp
      (continuous_freeProCZCCompletedFoxSemidirectLift
        (C := C) hι htargetH φ hφH)
  have hh_continuous : Continuous h :=
    continuous_freeProCZCCompletedFoxSemidirectLift
      (C := C) hι htargetK φK hφK
  have hfg : ∀ x : X, f (ι x) = h (ι x) := by
    intro x
    change
      zcCompletedFoxSemidirectMapTarget (X := X) C hC η
          (freeProCZCCompletedFoxSemidirectLift
            (C := C) hι htargetH φ hφH (ι x)) =
        freeProCZCCompletedFoxSemidirectLift
          (C := C) hι htargetK φK hφK (ι x)
    rw [freeProCZCCompletedFoxSemidirectLift_generator,
      freeProCZCCompletedFoxSemidirectLift_generator]
    apply ZCCompletedFoxSemidirect.ext
    · funext y
      by_cases hxy : x = y
      · subst y
        simp only [zcCompletedFoxSemidirectMapTarget_left, zcFreeFoxCoordinatesMap,
          freeProCZCCompletedFoxSemidirectGenerator_left, Pi.single_eq_same, map_one]
      · simp only [zcCompletedFoxSemidirectMapTarget_left, zcFreeFoxCoordinatesMap,
          freeProCZCCompletedFoxSemidirectGenerator_left, ne_eq, hxy, not_false_eq_true,
          Pi.single_eq_of_ne', map_zero]
    · simp only [zcCompletedFoxSemidirectMapTarget_right,
        freeProCZCCompletedFoxSemidirectGenerator_right, φK]
  have hfh : f = h := hι.hom_ext htargetK hf_continuous hh_continuous hfg
  exact congrFun (congrArg DFunLike.coe hfh) g

omit [Fintype X] in
/-- Continuous-hom form of target naturality for the canonical completed Fox semidirect lift. -/
theorem freeProCZCCompletedFoxSemidirectLiftHom_mapTarget
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htargetH :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (htargetK :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X K))
    (η : H →ₜ* K) (φ : X → H) :
    (zcCompletedFoxSemidirectMapTargetHom (X := X) C hC η).comp
        (freeProCZCCompletedFoxSemidirectLiftHom
          (C := C) hι htargetH φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ)) =
      freeProCZCCompletedFoxSemidirectLiftHom
        (C := C) hι htargetK (fun x : X => η (φ x))
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X K (fun x :
            X => η (φ x))) := by
  apply ContinuousMonoidHom.ext
  intro g
  exact freeProCZCCompletedFoxSemidirectLift_mapTarget
    (C := C) (X := X) (F := F) (H := H) (K := K)
    hC hι htargetH htargetK η φ g

omit [Fintype X] in
/-- Target naturality of the right homomorphism of the canonical completed Fox lift. -/
theorem freeProCZCCompletedFoxRightHom_mapTarget
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htargetH :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (htargetK :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X K))
    (η : H →ₜ* K) (φ : X → H) :
    freeProCZCCompletedFoxRightHom
        (C := C) hι htargetK (fun x : X => η (φ x))
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X K (fun x :
            X => η (φ x))) =
      η.toMonoidHom.comp
        (freeProCZCCompletedFoxRightHom
          (C := C) hι htargetH φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ)) := by
  ext g
  have h := congrArg ZCCompletedFoxSemidirect.right
    (freeProCZCCompletedFoxSemidirectLift_mapTarget
      (C := C) (X := X) (F := F) (H := H) (K := K)
      hC hι htargetH htargetK η φ g)
  simpa [freeProCZCCompletedFoxRightHom_apply, MonoidHom.comp_apply] using h.symm

omit [Fintype X] in
/-- Target naturality of the derivative vector of the canonical completed Fox lift. -/
theorem freeProCZCCompletedFoxDerivativeVector_mapTarget
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htargetH :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (htargetK :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X K))
    (η : H →ₜ* K) (φ : X → H) (g : F) :
    freeProCZCCompletedFoxDerivativeVector
        (C := C) hι htargetK (fun x : X => η (φ x))
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X K (fun x :
            X => η (φ x))) g =
      zcFreeFoxCoordinatesMap (X := X) C hC η
        (freeProCZCCompletedFoxDerivativeVector
          (C := C) hι htargetH φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ) g) := by
  have h := congrArg ZCCompletedFoxSemidirect.left
    (freeProCZCCompletedFoxSemidirectLift_mapTarget
      (C := C) (X := X) (F := F) (H := H) (K := K)
      hC hι htargetH htargetK η φ g)
  convert h.symm using 1 <;> rfl

omit [Fintype X] in
/-- Target naturality for the canonical completed Fox derivative holds componentwise. -/
theorem freeProCZCCompletedFoxDerivativeVector_mapTarget_apply
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htargetH :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (htargetK :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X K))
    (η : H →ₜ* K) (φ : X → H) (g : F) (x : X) :
    freeProCZCCompletedFoxDerivativeVector
        (C := C) hι htargetK (fun x : X => η (φ x))
        (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X K (fun x :
            X => η (φ x))) g x =
      zcCompletedGroupAlgebraMap C hC η
        (freeProCZCCompletedFoxDerivativeVector
          (C := C) hι htargetH φ
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ) g x)
              := by
  have h := congrFun
    (freeProCZCCompletedFoxDerivativeVector_mapTarget
      (C := C) (X := X) (F := F) (H := H) (K := K)
      hC hι htargetH htargetK η φ g) x
  simpa [zcFreeFoxCoordinatesMap] using h

/--
Target naturality for the source-shaped boundary applied to the canonical completed Fox
derivative vector.
-/
theorem freeProCZCCompletedFoxBoundary_mapTarget_of_derivativeVector
    {ι : X → F}
    (hι : ProCGroups.FreeProC.IsFreeProCGroup (C := C) ι)
    (htargetH :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H))
    (htargetK :
    ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X K))
    (η : H →ₜ* K) (φ : X → H) (g : F) :
    zcCompletedGroupAlgebraMap C hC η
        (freeProCZCCompletedFoxBoundary C φ
          (freeProCZCCompletedFoxDerivativeVector
            (C := C) hι htargetH φ
            (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X H φ) g)) =
      freeProCZCCompletedFoxBoundary C (fun x : X => η (φ x))
        (freeProCZCCompletedFoxDerivativeVector
          (C := C) hι htargetK (fun x : X => η (φ x))
          (continuous_freeProCZCCompletedFoxSemidirectGenerator_of_discrete (C := C) X K (fun x
              : X => η (φ x))) g) := by
  rw [freeProCZCCompletedFoxBoundary_mapTarget]
  rw [← freeProCZCCompletedFoxDerivativeVector_mapTarget
    (C := C) (X := X) (F := F) (H := H) (K := K)
    hC hι htargetH htargetK η φ g]

end SourceNaturality

end

end FoxDifferential
