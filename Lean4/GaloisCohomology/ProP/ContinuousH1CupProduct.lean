/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.ContinuousH1CupCochain
import GaloisCohomology.ProP.FiniteTransgression

set_option autoImplicit false
/-!
# The continuous cup product of two trivial mod-p characters

This file packages the explicit canonical character cup cocycle as a
degree-two continuous cohomology class and as a bilinear map.
-/

open CategoryTheory TopRep ContRepresentation
open ClassFieldTower.ProP
open scoped Topology

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

variable {p : ℕ}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance continuousH1CupProductContinuousSMulULiftZMod :
    ContinuousSMul (ZMod p) (ULift.{u} (ZMod p)) :=
  ContinuousSMul.induced ULift.moduleEquiv.toLinearMap

local instance continuousH1CupProductModule :
    Module (ZMod p) (ContinuousH1ZMod (p := p) (G := G)) :=
  continuousH1ZModModule

/-- The degree-two cocycle represented by the canonical character cup
cochain. -/
noncomputable def continuousH1CupHomogeneousTwoCocycleLifted
    (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    trivialZModPCocyclesLifted p G 2 :=
  homogeneousCocycleOfElement (trivialZModPLifted p G) 2
    (continuousH1CupHomogeneousTwoCochainLifted χ ψ)
    (continuousH1CupHomogeneousTwoCochainLifted_mem_cycles χ ψ)

@[simp]
theorem iCycles_continuousH1CupHomogeneousTwoCocycleLifted
    (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    (trivialZModPCochainsLifted p G).iCycles 2
        (continuousH1CupHomogeneousTwoCocycleLifted χ ψ) =
      continuousH1CupHomogeneousTwoCochainLifted χ ψ :=
  iCycles_homogeneousCocycleOfElement _ _ _ _

theorem continuousH1CupHomogeneousTwoCocycleLifted_add_left
    (χ χ' ψ : ContinuousH1ZMod (p := p) (G := G)) :
    continuousH1CupHomogeneousTwoCocycleLifted (χ + χ') ψ =
      continuousH1CupHomogeneousTwoCocycleLifted χ ψ +
        continuousH1CupHomogeneousTwoCocycleLifted χ' ψ := by
  apply topModule_mono_injective_lifted
    ((trivialZModPCochainsLifted p G).iCycles 2)
  rw [map_add, iCycles_continuousH1CupHomogeneousTwoCocycleLifted,
    iCycles_continuousH1CupHomogeneousTwoCocycleLifted,
    iCycles_continuousH1CupHomogeneousTwoCocycleLifted]
  exact continuousH1CupHomogeneousTwoCochainLifted_add_left χ χ' ψ

theorem continuousH1CupHomogeneousTwoCocycleLifted_add_right
    (χ ψ ψ' : ContinuousH1ZMod (p := p) (G := G)) :
    continuousH1CupHomogeneousTwoCocycleLifted χ (ψ + ψ') =
      continuousH1CupHomogeneousTwoCocycleLifted χ ψ +
        continuousH1CupHomogeneousTwoCocycleLifted χ ψ' := by
  apply topModule_mono_injective_lifted
    ((trivialZModPCochainsLifted p G).iCycles 2)
  rw [map_add, iCycles_continuousH1CupHomogeneousTwoCocycleLifted,
    iCycles_continuousH1CupHomogeneousTwoCocycleLifted,
    iCycles_continuousH1CupHomogeneousTwoCocycleLifted]
  exact continuousH1CupHomogeneousTwoCochainLifted_add_right χ ψ ψ'

theorem continuousH1CupHomogeneousTwoCocycleLifted_smul_left
    (a : ZMod p) (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    continuousH1CupHomogeneousTwoCocycleLifted (a • χ) ψ =
      a • continuousH1CupHomogeneousTwoCocycleLifted χ ψ := by
  apply topModule_mono_injective_lifted
    ((trivialZModPCochainsLifted p G).iCycles 2)
  rw [map_smul, iCycles_continuousH1CupHomogeneousTwoCocycleLifted,
    iCycles_continuousH1CupHomogeneousTwoCocycleLifted]
  exact continuousH1CupHomogeneousTwoCochainLifted_smul_left a χ ψ

theorem continuousH1CupHomogeneousTwoCocycleLifted_smul_right
    (a : ZMod p) (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    continuousH1CupHomogeneousTwoCocycleLifted χ (a • ψ) =
      a • continuousH1CupHomogeneousTwoCocycleLifted χ ψ := by
  apply topModule_mono_injective_lifted
    ((trivialZModPCochainsLifted p G).iCycles 2)
  rw [map_smul, iCycles_continuousH1CupHomogeneousTwoCocycleLifted,
    iCycles_continuousH1CupHomogeneousTwoCocycleLifted]
  exact continuousH1CupHomogeneousTwoCochainLifted_smul_right a χ ψ

/-- The degree-two continuous cohomology class of the canonical character
cup cocycle. -/
noncomputable def continuousH1CupClassLifted
    (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    continuousCohomologyZModPLifted p G 2 :=
  ContinuousCohomology.π (trivialZModPLifted p G) 2
    (continuousH1CupHomogeneousTwoCocycleLifted χ ψ)

theorem continuousH1CupClassLifted_add_left
    (χ χ' ψ : ContinuousH1ZMod (p := p) (G := G)) :
    continuousH1CupClassLifted (χ + χ') ψ =
      continuousH1CupClassLifted χ ψ + continuousH1CupClassLifted χ' ψ := by
  change
    ContinuousCohomology.π (trivialZModPLifted p G) 2
        (continuousH1CupHomogeneousTwoCocycleLifted (χ + χ') ψ) =
      ContinuousCohomology.π (trivialZModPLifted p G) 2
          (continuousH1CupHomogeneousTwoCocycleLifted χ ψ) +
        ContinuousCohomology.π (trivialZModPLifted p G) 2
          (continuousH1CupHomogeneousTwoCocycleLifted χ' ψ)
  rw [continuousH1CupHomogeneousTwoCocycleLifted_add_left, map_add]

theorem continuousH1CupClassLifted_add_right
    (χ ψ ψ' : ContinuousH1ZMod (p := p) (G := G)) :
    continuousH1CupClassLifted χ (ψ + ψ') =
      continuousH1CupClassLifted χ ψ + continuousH1CupClassLifted χ ψ' := by
  change
    ContinuousCohomology.π (trivialZModPLifted p G) 2
        (continuousH1CupHomogeneousTwoCocycleLifted χ (ψ + ψ')) =
      ContinuousCohomology.π (trivialZModPLifted p G) 2
          (continuousH1CupHomogeneousTwoCocycleLifted χ ψ) +
        ContinuousCohomology.π (trivialZModPLifted p G) 2
          (continuousH1CupHomogeneousTwoCocycleLifted χ ψ')
  rw [continuousH1CupHomogeneousTwoCocycleLifted_add_right, map_add]

theorem continuousH1CupClassLifted_smul_left
    (a : ZMod p) (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    continuousH1CupClassLifted (a • χ) ψ =
      a • continuousH1CupClassLifted χ ψ := by
  change
    ContinuousCohomology.π (trivialZModPLifted p G) 2
        (continuousH1CupHomogeneousTwoCocycleLifted (a • χ) ψ) =
      a • ContinuousCohomology.π (trivialZModPLifted p G) 2
        (continuousH1CupHomogeneousTwoCocycleLifted χ ψ)
  rw [continuousH1CupHomogeneousTwoCocycleLifted_smul_left, map_smul]

theorem continuousH1CupClassLifted_smul_right
    (a : ZMod p) (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    continuousH1CupClassLifted χ (a • ψ) =
      a • continuousH1CupClassLifted χ ψ := by
  change
    ContinuousCohomology.π (trivialZModPLifted p G) 2
        (continuousH1CupHomogeneousTwoCocycleLifted χ (a • ψ)) =
      a • ContinuousCohomology.π (trivialZModPLifted p G) 2
        (continuousH1CupHomogeneousTwoCocycleLifted χ ψ)
  rw [continuousH1CupHomogeneousTwoCocycleLifted_smul_right, map_smul]

/-- The continuous cup product of two trivial mod-`p` degree-one classes,
curried as a bilinear map into lifted degree-two cohomology. -/
noncomputable def continuousH1CupProductLifted :
    ContinuousH1ZMod (p := p) (G := G) →ₗ[ZMod p]
      ContinuousH1ZMod (p := p) (G := G) →ₗ[ZMod p]
        continuousCohomologyZModPLifted p G 2 :=
  { toFun := fun χ ↦
      { toFun := continuousH1CupClassLifted χ
        map_add' := fun ψ ψ' ↦ continuousH1CupClassLifted_add_right χ ψ ψ'
        map_smul' := fun a ψ ↦ continuousH1CupClassLifted_smul_right a χ ψ }
    map_add' := by
      intro χ χ'
      ext ψ
      exact continuousH1CupClassLifted_add_left χ χ' ψ
    map_smul' := by
      intro a χ
      ext ψ
      exact continuousH1CupClassLifted_smul_left a χ ψ }

@[simp]
theorem continuousH1CupProductLifted_apply
    (χ ψ : ContinuousH1ZMod (p := p) (G := G)) :
    continuousH1CupProductLifted χ ψ =
      continuousH1CupClassLifted χ ψ :=
  rfl

end

end ClassFieldTower.Cohomology
