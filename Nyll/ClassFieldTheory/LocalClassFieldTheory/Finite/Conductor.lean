/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups
public import Mathlib.FieldTheory.Galois.Abelian

/-!
# Norm conductors of finite separable local extensions

For a finite separable extension `L / K`, define its conductor exponent as the
least `n ≥ 0` for which the `n`-th principal-unit group of
`K` lies in the norm subgroup.  The conductor itself is the corresponding
power of the maximal ideal of the valuation ring of `K`.

The existence of this least exponent is not an extra hypothesis here.  It
follows from openness of the norm subgroup of the actual finite extension and
the principal-unit neighbourhood basis.
-/



@[expose] public section

universe u v w

noncomputable section

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory

/-- The field-level principal-unit filtration is antitone in its exponent. -/
theorem fieldPrincipalUnits_antitone
    (K : Type u) [Field K] [ValuativeRel K]
    {m n : ℕ} (hmn : m ≤ n) :
    LocalFieldTheory.fieldPrincipalUnits K n ≤ LocalFieldTheory.fieldPrincipalUnits K m :=
  Subgroup.map_mono (principalUnits_antitone K hmn)

/-- An open subgroup of the local unit group contains some field principal-unit group. -/
theorem exists_fieldPrincipalUnits_le_openSubgroup
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (H : Subgroup Kˣ) (hH : IsOpen (H : Set Kˣ)) :
    ∃ n : ℕ, fieldPrincipalUnits K n ≤ H := by
  obtain ⟨n, _hn, hle⟩ := exists_fieldPrincipalUnits_le_of_isOpen K H hH
  exact ⟨n, hle⟩

/-- The first principal-unit depth contained in an open subgroup. -/
def localConductorExponentOfOpenSubgroup
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (H : Subgroup Kˣ) (hH : IsOpen (H : Set Kˣ)) : ℕ := by
  classical
  exact Nat.find (exists_fieldPrincipalUnits_le_openSubgroup K H hH)

/-- A principal-unit step lies in the subgroup exactly from its conductor onward. -/
theorem localConductorExponentOfOpenSubgroup_le_iff
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] (H : Subgroup Kˣ) (hH : IsOpen (H : Set Kˣ)) (n : ℕ) :
    localConductorExponentOfOpenSubgroup K H hH ≤ n ↔ fieldPrincipalUnits K n ≤ H := by
  classical
  let hex := exists_fieldPrincipalUnits_le_openSubgroup K H hH
  change Nat.find hex ≤ n ↔ fieldPrincipalUnits K n ≤ H
  exact ⟨fun h => (fieldPrincipalUnits_antitone K h).trans (Nat.find_spec hex), Nat.find_min' hex⟩

/-- For an actual finite separable local extension, some principal-unit group
is contained in its norm subgroup. This supplies the least conductor
exponent. -/
theorem exists_fieldPrincipalUnits_le_normSubgroup
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    ∃ n : ℕ, LocalFieldTheory.fieldPrincipalUnits K n ≤ localNormSubgroup K L :=
  exists_fieldPrincipalUnits_le_openSubgroup K (localNormSubgroup K L)
    (localNormSubgroup_isOpen_of_isSeparable K L)

/-- The least principal-unit depth contained in the norm subgroup of the
finite separable extension `L / K`. -/
def localConductorExponent
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : ℕ :=
  localConductorExponentOfOpenSubgroup K (localNormSubgroup K L)
    (localNormSubgroup_isOpen_of_isSeparable K L)

/-- The principal-unit group at the conductor exponent is contained in the
norm subgroup. -/
theorem localConductorExponent_spec
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    LocalFieldTheory.fieldPrincipalUnits K (localConductorExponent K L) ≤
      localNormSubgroup K L := by
  exact (localConductorExponentOfOpenSubgroup_le_iff K (localNormSubgroup K L)
    (localNormSubgroup_isOpen_of_isSeparable K L) (localConductorExponent K L)).mp le_rfl

/-- Minimality of the conductor exponent. -/
theorem localConductorExponent_min
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    {n : ℕ} (hn : LocalFieldTheory.fieldPrincipalUnits K n ≤ localNormSubgroup K L) :
    localConductorExponent K L ≤ n := by
  exact (localConductorExponentOfOpenSubgroup_le_iff K (localNormSubgroup K L)
    (localNormSubgroup_isOpen_of_isSeparable K L) n).mpr hn

/-- A depth contains the conductor depth exactly when its principal units are
already norms.  This records both the defining property and its minimality. -/
theorem localConductorExponent_le_iff
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ) :
    localConductorExponent K L ≤ n ↔
      LocalFieldTheory.fieldPrincipalUnits K n ≤ localNormSubgroup K L := by
  constructor
  · intro hn
    exact (fieldPrincipalUnits_antitone K hn).trans
      (localConductorExponent_spec K L)
  · exact localConductorExponent_min K L

/-- Finite separable extensions with the same norm image have the same norm
conductor, in particular after passing to their maximal abelian subfields. -/
theorem localConductorExponent_eq_of_normSubgroup_eq
    (K : Type u) (L : Type v) (M : Type w) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [FiniteDimensional K L] [FiniteDimensional K M]
    [Algebra.IsSeparable K L] [Algebra.IsSeparable K M]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (h : localNormSubgroup K L = localNormSubgroup K M) :
    localConductorExponent K L = localConductorExponent K M := by
  apply le_antisymm
  · apply (localConductorExponent_le_iff K L _).mpr
    rw [h]
    exact localConductorExponent_spec K M
  · apply (localConductorExponent_le_iff K M _).mpr
    rw [← h]
    exact localConductorExponent_spec K L

/-- The conductor ideal `p_K ^ n`, where `n` is the least principal-unit
depth contained in the norm subgroup. -/
def localConductorIdeal
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Ideal 𝒪[K] :=
  𝓂[K] ^ localConductorExponent K L

/-- The conductor exponent is zero exactly when the whole unit group
`U_K = U_K^(0)` is contained in the norm subgroup. -/
theorem localConductorExponent_eq_zero_iff
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    localConductorExponent K L = 0 ↔
      LocalFieldTheory.fieldPrincipalUnits K 0 ≤ localNormSubgroup K L := by
  simpa using (localConductorExponent_le_iff K L 0)

/-- The conductor ideal is `1` exactly when its exponent is zero. -/
theorem localConductorIdeal_eq_one_iff_exponent_eq_zero
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    localConductorIdeal K L = 1 ↔ localConductorExponent K L = 0 := by
  simp [localConductorIdeal, Ideal.pow_eq_top_iff,
    (IsLocalRing.maximalIdeal.isMaximal 𝒪[K]).ne_top]

/-- The conductor-one criterion stated directly in terms of the norm subgroup
and `U_K = U_K^(0)`. -/
theorem localConductorIdeal_eq_one_iff
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    localConductorIdeal K L = 1 ↔
      LocalFieldTheory.fieldPrincipalUnits K 0 ≤ localNormSubgroup K L :=
  (localConductorIdeal_eq_one_iff_exponent_eq_zero K L).trans
    (localConductorExponent_eq_zero_iff K L)

end LocalClassFieldTheory
