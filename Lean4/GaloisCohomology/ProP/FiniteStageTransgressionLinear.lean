/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.FiniteStageTransgression
import GaloisCohomology.ProP.FiniteTransgressionLinear
import Mathlib.LinearAlgebra.LinearIndependent.Basic

set_option autoImplicit false
/-!
# Linear finite-stage transgression

Defines finite-stage inflation as a linear map, composes it with the explicit finite
transgression map, and transports the no-extendable-combination independence criterion across
injective degree-two inflation.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups ProCGroups.ProC

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]

local instance inflatedLinearStageTargetTopology
    (R : ClosedSubgroup F)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    TopologicalSpace
      ((F ⧸ (U.1 : Subgroup F)) ⧸ finiteStageImage R U) := ⊥

local instance inflatedLinearStageTargetDiscrete
    (R : ClosedSubgroup F)
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    DiscreteTopology
      ((F ⧸ (U.1 : Subgroup F)) ⧸ finiteStageImage R U) :=
  discreteTopology_bot _

variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]

/-- Inflation from the finite-stage quotient to the original quotient. -/
noncomputable def finiteStageInflationLinearMap
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    ClassFieldTower.Cohomology.continuousCohomologyZModPLifted p
        ((F ⧸ (U.1 : Subgroup F)) ⧸ finiteStageImage R U) 2 →ₗ[ZMod p]
      ClassFieldTower.Cohomology.continuousCohomologyZModPLifted p
        (F ⧸ (R : Subgroup F)) 2 :=
  (ClassFieldTower.Cohomology.continuousCohomologyZModPMapLifted p
    (finiteStageQuotientMap R U) 2).hom.toLinearMap

/-- Finite transgression followed by inflation to `H²(F/R, ZMod p)`. -/
noncomputable def inflatedFiniteTransgressionLinearMap
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    ClassFieldTower.Cohomology.InvariantFiniteCharacter (p := p)
        (finiteStageImage R U) →ₗ[ZMod p]
      ClassFieldTower.Cohomology.continuousCohomologyZModPLifted p
        (F ⧸ (R : Subgroup F)) 2 :=
  (finiteStageInflationLinearMap R U).comp
    (ClassFieldTower.Cohomology.finiteTransgressionLinearMap
      (p := p) (finiteStageImage R U))

omit [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F] in
@[simp]
theorem inflatedFiniteTransgressionLinearMap_apply
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (χ : ClassFieldTower.Cohomology.InvariantFiniteCharacter (p := p)
      (finiteStageImage R U)) :
    inflatedFiniteTransgressionLinearMap R U χ =
      inflatedFiniteTransgressionClass R U
        (ClassFieldTower.Cohomology.InvariantFiniteCharacter.toMonoidHom
          (finiteStageImage R U) χ)
        (ClassFieldTower.Cohomology.InvariantFiniteCharacter.isInvariant
          (finiteStageImage R U) χ) :=
  rfl

omit [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F] in
@[simp]
theorem inflatedFiniteTransgressionLinearMap_zero
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F) :
    inflatedFiniteTransgressionLinearMap R U
      (0 : ClassFieldTower.Cohomology.InvariantFiniteCharacter (p := p)
        (finiteStageImage R U)) = 0 :=
  map_zero (inflatedFiniteTransgressionLinearMap R U)

omit [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F] in
@[simp]
theorem inflatedFiniteTransgressionLinearMap_add
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (χ ψ : ClassFieldTower.Cohomology.InvariantFiniteCharacter (p := p)
      (finiteStageImage R U)) :
    inflatedFiniteTransgressionLinearMap R U (χ + ψ) =
      inflatedFiniteTransgressionLinearMap R U χ +
        inflatedFiniteTransgressionLinearMap R U ψ :=
  map_add (inflatedFiniteTransgressionLinearMap R U) χ ψ

omit [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F] in
@[simp]
theorem inflatedFiniteTransgressionLinearMap_smul
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (a : ZMod p)
    (χ : ClassFieldTower.Cohomology.InvariantFiniteCharacter (p := p)
      (finiteStageImage R U)) :
    inflatedFiniteTransgressionLinearMap R U (a • χ) =
      a • inflatedFiniteTransgressionLinearMap R U χ :=
  map_smul (inflatedFiniteTransgressionLinearMap R U) a χ

omit [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F] in
/-- Inflation preserves the finite-stage independence criterion when it is injective in degree
two. -/
theorem linearIndependent_inflatedFiniteTransgressionClass_of_injective
    {ι : Type*}
    (R : ClosedSubgroup F) [R.Normal]
    (U : OpenNormalSubgroupInClass (FiniteGroupClass.pGroup p) F)
    (hinfl : Function.Injective (finiteStageInflationLinearMap R U))
    (v : ι → ClassFieldTower.Cohomology.InvariantFiniteCharacter (p := p)
      (finiteStageImage R U))
    (hno : ∀ l : ι →₀ ZMod p,
      ClassFieldTower.Cohomology.InvariantFiniteCharacter.ExtendsToAmbient
        (finiteStageImage R U)
        (Finsupp.linearCombination (ZMod p) v l) → l = 0) :
    LinearIndependent (ZMod p) (fun i ↦ inflatedFiniteTransgressionClass R U
      (ClassFieldTower.Cohomology.InvariantFiniteCharacter.toMonoidHom
        (finiteStageImage R U) (v i))
      (ClassFieldTower.Cohomology.InvariantFiniteCharacter.isInvariant
        (finiteStageImage R U) (v i))) := by
  have hbase :=
    ClassFieldTower.Cohomology.linearIndependent_finiteTransgressionLinearMap_of_no_extendableCombination
      (finiteStageImage R U) v hno
  have himage := hbase.map' (finiteStageInflationLinearMap R U)
    (LinearMap.ker_eq_bot.mpr hinfl)
  change LinearIndependent (ZMod p)
    (fun i ↦ inflatedFiniteTransgressionLinearMap R U (v i)) at himage
  simpa only [inflatedFiniteTransgressionLinearMap_apply] using himage

end


end ClassFieldTower.ProP
