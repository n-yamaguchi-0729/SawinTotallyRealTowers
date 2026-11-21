/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-!
# Higher-unit subgroups at finite places
-/



@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

/-- Reduction of a local integral unit modulo the `n`-th power of the maximal
ideal. -/
def rayLocalHigherUnitMap
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    (v.adicCompletionIntegers K).units →*
      ((v.adicCompletionIntegers K) ⧸
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n)ˣ :=
  (Units.map
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)) ^ n)).toMonoidHom).comp
    (v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType.toMonoidHom

/-- The `n`-th higher-unit subgroup at a finite place. -/
def rayLocalHigherUnitGroup
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Subgroup (v.adicCompletion K)ˣ :=
  Subgroup.map
    (v.adicCompletionIntegers K).units.subtype
    (rayLocalHigherUnitMap v n).ker

/-- Membership is equivalent to having an integral-unit representative reducing to one. -/
theorem mem_rayLocalHigherUnitGroup_iff_reduction_eq_one
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (x : (v.adicCompletion K)ˣ) :
    x ∈ rayLocalHigherUnitGroup v n ↔
      ∃ y : (v.adicCompletionIntegers K).units,
        (y : (v.adicCompletion K)ˣ) = x ∧
        rayLocalHigherUnitMap v n y = 1 := by
  change x ∈ Subgroup.map (v.adicCompletionIntegers K).units.subtype
    (rayLocalHigherUnitMap v n).ker ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, rfl, MonoidHom.mem_ker.mp hy⟩
  · rintro ⟨y, rfl, hy⟩
    exact ⟨y, MonoidHom.mem_ker.mpr hy, rfl⟩

/-- Every higher local unit is an integral unit. -/
theorem rayLocalHigherUnitGroup_le_integralUnits
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    rayLocalHigherUnitGroup v n ≤
      (v.adicCompletionIntegers K).units := by
  intro x hx
  rw [mem_rayLocalHigherUnitGroup_iff_reduction_eq_one] at hx
  obtain ⟨y, rfl, _⟩ := hx
  exact y.property

/-- The zeroth higher unit group is the full group of local integral
units. -/
theorem rayLocalHigherUnitGroup_zero
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    rayLocalHigherUnitGroup v 0 =
      (v.adicCompletionIntegers K).units := by
  ext x
  rw [mem_rayLocalHigherUnitGroup_iff_reduction_eq_one]
  constructor
  · rintro ⟨y, rfl, _hy⟩
    exact y.property
  · intro hx
    let y : (v.adicCompletionIntegers K).units := ⟨x, hx⟩
    refine ⟨y, rfl, ?_⟩
    change Units.map
      (Ideal.Quotient.mk
        ((IsLocalRing.maximalIdeal
          (v.adicCompletionIntegers K)) ^ 0)).toMonoidHom
        ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y) =
      1
    let : Subsingleton
        ((v.adicCompletionIntegers K) ⧸
          (IsLocalRing.maximalIdeal
            (v.adicCompletionIntegers K)) ^ 0) :=
      Ideal.Quotient.subsingleton_iff.mpr (by rw [pow_zero, Ideal.one_eq_top])
    apply Units.ext
    exact Subsingleton.elim _ _

/-- The integral representative of a unit in a finite completion. -/
def rayLocalIntegralValue
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    (y : (v.adicCompletionIntegers K).units) :
    v.adicCompletionIntegers K :=
  ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y :
    (v.adicCompletionIntegers K)ˣ).1

/-- Reduction modulo a maximal-ideal power maps a unit to one precisely when
its integral representative differs from one by an element of that power. -/
theorem rayLocalHigherUnitMap_eq_one_iff
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) (n : ℕ)
    (y : (v.adicCompletionIntegers K).units) :
    rayLocalHigherUnitMap v n y = 1 ↔
      rayLocalIntegralValue v y - 1 ∈
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n := by
  let I := (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) ^ n
  change Units.map (Ideal.Quotient.mk I).toMonoidHom
      ((v.adicCompletionIntegers K).toSubmonoid.unitsEquivUnitsType y) =
        1 ↔ _
  rw [Units.ext_iff]
  change Ideal.Quotient.mk I (rayLocalIntegralValue v y) =
      Ideal.Quotient.mk I 1 ↔ _
  exact Ideal.Quotient.mk_eq_mk_iff_sub_mem
    (I := I) (rayLocalIntegralValue v y)
      (1 : v.adicCompletionIntegers K)

/-- Deeper local congruence conditions give smaller higher-unit groups. -/
theorem rayLocalHigherUnitGroup_antitone
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K))
    {m n : ℕ} (hmn : m ≤ n) :
    rayLocalHigherUnitGroup v n ≤ rayLocalHigherUnitGroup v m := by
  intro x hx
  change x ∈ Subgroup.map
    (v.adicCompletionIntegers K).units.subtype
    (rayLocalHigherUnitMap v n).ker at hx
  change x ∈ Subgroup.map
    (v.adicCompletionIntegers K).units.subtype
    (rayLocalHigherUnitMap v m).ker
  rw [Subgroup.mem_map] at hx ⊢
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨y, ?_, rfl⟩
  change rayLocalHigherUnitMap v n y = 1 at hy
  change rayLocalHigherUnitMap v m y = 1
  rw [rayLocalHigherUnitMap_eq_one_iff] at hy ⊢
  exact Ideal.pow_le_pow_right hmn hy

end ClassFieldTheory
