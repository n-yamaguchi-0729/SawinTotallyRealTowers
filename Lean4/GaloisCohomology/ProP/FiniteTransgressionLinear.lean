/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.FiniteTransgressionKernel
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.LinearIndependent.Defs

set_option autoImplicit false
/-!
# Linearity of finite transgression

Packages ambient-conjugation-invariant finite characters as a `ZMod p`-module and proves that
the explicit finite transgression construction is linear.  The kernel extension theorem then gives
a criterion for linear independence of finite families of transgression classes.
-/

open CategoryTheory TopRep ContRepresentation
open scoped Topology

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

variable {p : ℕ}
variable {P : Type u} [Group P]

local instance linearQuotientTopology (N : Subgroup P) : TopologicalSpace (P ⧸ N) := ⊥
local instance linearQuotientDiscrete (N : Subgroup P) : DiscreteTopology (P ⧸ N) :=
  discreteTopology_bot _

/-- Additive presentation of `ZMod p`-valued group characters. -/
abbrev FiniteCharacter (p : ℕ) (N : Type u) [Monoid N] :=
  Additive (MonoidHom N (Multiplicative (ZMod p)))

noncomputable instance finiteCharacterModule (N : Type u) [Monoid N] :
    Module (ZMod p) (FiniteCharacter p N) :=
  AddCommGroup.zmodModule <| by
    intro χ
    ext n
    change Multiplicative.ofAdd (p • (χ.toMul n).toAdd) = 1
    simp

/-- Ambient-conjugation-invariant finite characters, as an additive subgroup. -/
def invariantFiniteCharacterAddSubgroup (N : Subgroup P) [N.Normal] :
    AddSubgroup (FiniteCharacter p N) where
  carrier := {χ | ∀ (g : P) (n : N),
    χ.toMul (MulAut.conjNormal g n) = χ.toMul n}
  zero_mem' := by
    intro g n
    rfl
  add_mem' := by
    intro χ ψ hχ hψ g n
    change χ.toMul (MulAut.conjNormal g n) * ψ.toMul (MulAut.conjNormal g n) =
      χ.toMul n * ψ.toMul n
    rw [hχ g n, hψ g n]
  neg_mem' := by
    intro χ hχ g n
    change (χ.toMul (MulAut.conjNormal g n))⁻¹ = (χ.toMul n)⁻¹
    rw [hχ g n]

/-- Ambient-conjugation-invariant finite characters, as a `ZMod p`-module. -/
noncomputable def invariantFiniteCharacterSubmodule (N : Subgroup P) [N.Normal] :
    Submodule (ZMod p) (FiniteCharacter p N) :=
  AddSubgroup.toZModSubmodule p (invariantFiniteCharacterAddSubgroup N)

/-- An ambient-conjugation-invariant finite character. -/
abbrev InvariantFiniteCharacter (N : Subgroup P) [N.Normal] :=
  invariantFiniteCharacterSubmodule (p := p) N

/-- The multiplicative presentation of an invariant finite character. -/
def InvariantFiniteCharacter.toMonoidHom (N : Subgroup P) [N.Normal]
    (χ : InvariantFiniteCharacter (p := p) N) :
    MonoidHom N (Multiplicative (ZMod p)) :=
  χ.1.toMul

theorem InvariantFiniteCharacter.isInvariant (N : Subgroup P) [N.Normal]
    (χ : InvariantFiniteCharacter (p := p) N) :
    ∀ (g : P) (n : N),
      InvariantFiniteCharacter.toMonoidHom N χ (MulAut.conjNormal g n) =
        InvariantFiniteCharacter.toMonoidHom N χ n :=
  χ.2

@[simp]
theorem transgressionFactor_zero (N : Subgroup P) [N.Normal]
    (q r : P ⧸ N) :
    transgressionFactor N
      ((0 : FiniteCharacter p N).toMul) q r = 0 := by
  simp [transgressionFactor]

@[simp]
theorem transgressionFactor_add (N : Subgroup P) [N.Normal]
    (χ ψ : FiniteCharacter p N) (q r : P ⧸ N) :
    transgressionFactor N ((χ + ψ).toMul) q r =
      transgressionFactor N χ.toMul q r +
        transgressionFactor N ψ.toMul q r := by
  simp [transgressionFactor]

@[simp]
theorem transgressionHomogeneousCochain_zero (N : Subgroup P) [N.Normal] :
    transgressionHomogeneousCochain N
      ((0 : FiniteCharacter p N).toMul) = 0 := by
  apply Subtype.ext
  change (transgressionHomogeneousCochain N
      ((0 : FiniteCharacter p N).toMul)).1 =
    (0 : C(P ⧸ N, C(P ⧸ N, C(P ⧸ N, ULift.{u} (ZMod p)))))
  ext a b c
  change ULift.up (transgressionFactor N
    ((0 : FiniteCharacter p N).toMul) (a⁻¹ * b) (b⁻¹ * c)) = 0
  rw [transgressionFactor_zero]
  rfl

@[simp]
theorem transgressionHomogeneousCochain_add (N : Subgroup P) [N.Normal]
    (χ ψ : FiniteCharacter p N) :
    transgressionHomogeneousCochain N ((χ + ψ).toMul) =
      transgressionHomogeneousCochain N χ.toMul +
        transgressionHomogeneousCochain N ψ.toMul := by
  apply Subtype.ext
  change (transgressionHomogeneousCochain N ((χ + ψ).toMul)).1 =
    (transgressionHomogeneousCochain N χ.toMul).1 +
      (transgressionHomogeneousCochain N ψ.toMul).1
  ext a b c
  change ULift.up (transgressionFactor N ((χ + ψ).toMul)
      (a⁻¹ * b) (b⁻¹ * c)) =
    ULift.up (transgressionFactor N χ.toMul (a⁻¹ * b) (b⁻¹ * c)) +
      ULift.up (transgressionFactor N ψ.toMul (a⁻¹ * b) (b⁻¹ * c))
  rw [transgressionFactor_add]
  rfl

@[simp]
theorem transgressionHomogeneousCocycle_zero (N : Subgroup P) [N.Normal] :
    transgressionHomogeneousCocycle N
      (InvariantFiniteCharacter.toMonoidHom N
        (0 : InvariantFiniteCharacter (p := p) N))
      (InvariantFiniteCharacter.isInvariant N 0) = 0 := by
  let A := trivialZModPLifted p (P ⧸ N)
  let K := TopRep.homogeneousCochains A
  let F := forget₂ (TopModuleCat (ZMod p)) (ModuleCat (ZMod p))
  apply (ModuleCat.mono_iff_injective (F.map (K.iCycles 2))).1 inferInstance
  change (K.iCycles 2).hom _ = (K.iCycles 2).hom _
  rw [iCycles_transgressionHomogeneousCocycle, map_zero]
  exact transgressionHomogeneousCochain_zero N

@[simp]
theorem transgressionHomogeneousCocycle_add (N : Subgroup P) [N.Normal]
    (χ ψ : InvariantFiniteCharacter (p := p) N) :
    transgressionHomogeneousCocycle N
        (InvariantFiniteCharacter.toMonoidHom N (χ + ψ))
        (InvariantFiniteCharacter.isInvariant N (χ + ψ)) =
      transgressionHomogeneousCocycle N
          (InvariantFiniteCharacter.toMonoidHom N χ)
          (InvariantFiniteCharacter.isInvariant N χ) +
        transgressionHomogeneousCocycle N
          (InvariantFiniteCharacter.toMonoidHom N ψ)
          (InvariantFiniteCharacter.isInvariant N ψ) := by
  let A := trivialZModPLifted p (P ⧸ N)
  let K := TopRep.homogeneousCochains A
  let F := forget₂ (TopModuleCat (ZMod p)) (ModuleCat (ZMod p))
  apply (ModuleCat.mono_iff_injective (F.map (K.iCycles 2))).1 inferInstance
  change (K.iCycles 2).hom _ = (K.iCycles 2).hom _
  rw [iCycles_transgressionHomogeneousCocycle, map_add,
    iCycles_transgressionHomogeneousCocycle,
    iCycles_transgressionHomogeneousCocycle]
  exact transgressionHomogeneousCochain_add N χ.1 ψ.1

@[simp]
theorem finiteTransgressionClass_zero (N : Subgroup P) [N.Normal] :
    finiteTransgressionClass N
      (InvariantFiniteCharacter.toMonoidHom N
        (0 : InvariantFiniteCharacter (p := p) N))
      (InvariantFiniteCharacter.isInvariant N 0) = 0 := by
  unfold finiteTransgressionClass
  rw [transgressionHomogeneousCocycle_zero, map_zero]

@[simp]
theorem finiteTransgressionClass_add (N : Subgroup P) [N.Normal]
    (χ ψ : InvariantFiniteCharacter (p := p) N) :
    finiteTransgressionClass N
        (InvariantFiniteCharacter.toMonoidHom N (χ + ψ))
        (InvariantFiniteCharacter.isInvariant N (χ + ψ)) =
      finiteTransgressionClass N
          (InvariantFiniteCharacter.toMonoidHom N χ)
          (InvariantFiniteCharacter.isInvariant N χ) +
        finiteTransgressionClass N
          (InvariantFiniteCharacter.toMonoidHom N ψ)
          (InvariantFiniteCharacter.isInvariant N ψ) := by
  unfold finiteTransgressionClass
  rw [transgressionHomogeneousCocycle_add, map_add]

/-- Finite transgression as an additive homomorphism. -/
noncomputable def finiteTransgressionAddHom (N : Subgroup P) [N.Normal] :
    InvariantFiniteCharacter (p := p) N →+
      continuousCohomologyZModPLifted p (P ⧸ N) 2 where
  toFun χ := finiteTransgressionClass N
    (InvariantFiniteCharacter.toMonoidHom N χ)
    (InvariantFiniteCharacter.isInvariant N χ)
  map_zero' := finiteTransgressionClass_zero N
  map_add' := finiteTransgressionClass_add N

/-- Finite transgression as a `ZMod p`-linear map. -/
noncomputable def finiteTransgressionLinearMap (N : Subgroup P) [N.Normal] :
    InvariantFiniteCharacter (p := p) N →ₗ[ZMod p]
      continuousCohomologyZModPLifted p (P ⧸ N) 2 :=
  (finiteTransgressionAddHom N).toZModLinearMap p

@[simp]
theorem finiteTransgressionLinearMap_apply (N : Subgroup P) [N.Normal]
    (χ : InvariantFiniteCharacter (p := p) N) :
    finiteTransgressionLinearMap N χ = finiteTransgressionClass N
      (InvariantFiniteCharacter.toMonoidHom N χ)
      (InvariantFiniteCharacter.isInvariant N χ) :=
  rfl

@[simp]
theorem finiteTransgressionLinearMap_zero (N : Subgroup P) [N.Normal] :
    finiteTransgressionLinearMap N
      (0 : InvariantFiniteCharacter (p := p) N) = 0 :=
  map_zero (finiteTransgressionLinearMap N)

@[simp]
theorem finiteTransgressionLinearMap_add (N : Subgroup P) [N.Normal]
    (χ ψ : InvariantFiniteCharacter (p := p) N) :
    finiteTransgressionLinearMap N (χ + ψ) =
      finiteTransgressionLinearMap N χ + finiteTransgressionLinearMap N ψ :=
  map_add (finiteTransgressionLinearMap N) χ ψ

@[simp]
theorem finiteTransgressionLinearMap_smul (N : Subgroup P) [N.Normal]
    (a : ZMod p) (χ : InvariantFiniteCharacter (p := p) N) :
    finiteTransgressionLinearMap N (a • χ) =
      a • finiteTransgressionLinearMap N χ :=
  map_smul (finiteTransgressionLinearMap N) a χ

/-- A character extends to the ambient group if it is the restriction of an ambient character. -/
def InvariantFiniteCharacter.ExtendsToAmbient (N : Subgroup P) [N.Normal]
    (χ : InvariantFiniteCharacter (p := p) N) : Prop :=
  ∃ ψ : MonoidHom P (Multiplicative (ZMod p)),
    ψ.comp N.subtype = InvariantFiniteCharacter.toMonoidHom N χ

/-- The kernel of finite transgression consists of extendable invariant characters. -/
theorem InvariantFiniteCharacter.extendsToAmbient_of_transgression_eq_zero
    (N : Subgroup P) [N.Normal]
    (χ : InvariantFiniteCharacter (p := p) N)
    (hχ : finiteTransgressionLinearMap N χ = 0) :
    InvariantFiniteCharacter.ExtendsToAmbient N χ := by
  exact exists_extension_of_finiteTransgressionClass_eq_zero N
    (InvariantFiniteCharacter.toMonoidHom N χ)
    (InvariantFiniteCharacter.isInvariant N χ)
    (by simpa only [finiteTransgressionLinearMap_apply] using hχ)

/-- A family has linearly independent transgression classes if no nonzero finite linear
combination of its characters extends to the ambient group. -/
theorem linearIndependent_finiteTransgressionLinearMap_of_no_extendableCombination
    {ι : Type*} (N : Subgroup P) [N.Normal]
    (v : ι → InvariantFiniteCharacter (p := p) N)
    (hno : ∀ l : ι →₀ ZMod p,
      InvariantFiniteCharacter.ExtendsToAmbient N
        (Finsupp.linearCombination (ZMod p) v l) → l = 0) :
    LinearIndependent (ZMod p) (fun i ↦ finiteTransgressionLinearMap N (v i)) := by
  rw [linearIndependent_iff]
  intro l hl
  apply hno l
  apply InvariantFiniteCharacter.extendsToAmbient_of_transgression_eq_zero N
  rw [LinearMap.map_finsupp_linearCombination]
  exact hl

/-- The preceding criterion, stated directly for explicit finite transgression classes. -/
theorem linearIndependent_finiteTransgressionClass_of_no_extendableCombination
    {ι : Type*} (N : Subgroup P) [N.Normal]
    (v : ι → InvariantFiniteCharacter (p := p) N)
    (hno : ∀ l : ι →₀ ZMod p,
      InvariantFiniteCharacter.ExtendsToAmbient N
        (Finsupp.linearCombination (ZMod p) v l) → l = 0) :
    LinearIndependent (ZMod p) (fun i ↦ finiteTransgressionClass N
      (InvariantFiniteCharacter.toMonoidHom N (v i))
      (InvariantFiniteCharacter.isInvariant N (v i))) := by
  simpa only [finiteTransgressionLinearMap_apply] using
    linearIndependent_finiteTransgressionLinearMap_of_no_extendableCombination N v hno

end


end ClassFieldTower.Cohomology
