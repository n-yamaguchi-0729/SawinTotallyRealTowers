/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalTopology
public import Nyll.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup

/-!
# Finite ray-modulus data

This file contains the finite local data used by ray congruence subgroups.
A full modulus, including a selected set of real places, is defined in
`AlgebraicNumberTheory.RayClass.FullModulus`.
-/



@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace RayClass

/-- A finite ray modulus. Its finite support records the prime powers
dividing the modulus. -/
abbrev FiniteModulus (K : Type*) [Field K] [NumberField K] :=
  HeightOneSpectrum (𝓞 K) →₀ ℕ

/-- Positivity at a real infinite place.  At a complex place the condition
is vacuous, so this is the whole local multiplicative group. -/
def infinitePositiveSubgroup (v : InfinitePlace K) :
    Subgroup v.Completionˣ where
  carrier := {x | ∀ hv : v.IsReal,
    0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
      hv (x : v.Completion)}
  one_mem' hv := by
    change 0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal hv 1
    rw [map_one]
    exact zero_lt_one
  mul_mem' {x y} hx hy hv := by
    change 0 <
      NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
        hv ((x : v.Completion) * (y : v.Completion))
    rw [map_mul]
    exact mul_pos (hx hv) (hy hv)
  inv_mem' {x} hx hv := by
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact inv_pos.mpr (hx hv)

omit [NumberField K] in
@[simp]
theorem mem_infinitePositiveSubgroup_iff
    (v : InfinitePlace K) (x : v.Completionˣ) :
    x ∈ infinitePositiveSubgroup v ↔
      ∀ hv : v.IsReal,
        0 < NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal
          hv (x : v.Completion) :=
  Iff.rfl

/-- The finite idele congruence subgroup attached to a modulus. -/
def finiteCongruenceSubgroup (m : FiniteModulus K) :
    Subgroup (FiniteIdeleGroup K) where
  carrier := {a | ∀ v, a v ∈ ClassFieldTheory.rayLocalHigherUnitGroup v (m v)}
  one_mem' v := (ClassFieldTheory.rayLocalHigherUnitGroup v (m v)).one_mem
  mul_mem' ha hb v :=
    (ClassFieldTheory.rayLocalHigherUnitGroup v (m v)).mul_mem (ha v) (hb v)
  inv_mem' ha v :=
    (ClassFieldTheory.rayLocalHigherUnitGroup v (m v)).inv_mem (ha v)

@[simp]
theorem mem_finiteCongruenceSubgroup_iff
    (m : FiniteModulus K) (a : FiniteIdeleGroup K) :
    a ∈ finiteCongruenceSubgroup m ↔
      ∀ v, a v ∈ ClassFieldTheory.rayLocalHigherUnitGroup v (m v) :=
  Iff.rfl

/-- Ideles positive at every real infinite place. -/
def narrowInfiniteCongruenceSubgroup :
    Subgroup (InfiniteIdeleGroup K) :=
  Subgroup.comap ContinuousMulEquiv.piUnits.toMonoidHom
    (Subgroup.pi Set.univ (fun v => infinitePositiveSubgroup v))

omit [NumberField K] in
@[simp]
theorem mem_narrowInfiniteCongruenceSubgroup_iff
    (a : InfiniteIdeleGroup K) :
    a ∈ narrowInfiniteCongruenceSubgroup (K := K) ↔
      ∀ v, ContinuousMulEquiv.piUnits a v ∈
        infinitePositiveSubgroup v := by
  change ContinuousMulEquiv.piUnits a ∈
      Subgroup.pi Set.univ (fun v => infinitePositiveSubgroup v) ↔ _
  rw [Subgroup.mem_pi]
  simp only [Set.mem_univ, true_implies]

end RayClass
