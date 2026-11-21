/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.Equiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Equiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivAdeleTopology
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Algebra.Group.Units
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

/-!
# Idèle and idèle-class transport under a number-field equivalence

The continuous adele-ring transport induces continuous transport of units
and then of the quotient by principal idèles. These topological equivalences
have the previously defined algebraic maps as their underlying maps.
-/

@[expose] public section

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

universe u v

variable {K : Type u} {M : Type v}
  [Field K] [NumberField K] [Algebra ℚ K]
  [Field M] [NumberField M] [Algebra ℚ M]

/-- Adelic field-isomorphism transport is a topological group equivalence. -/
noncomputable def adeleCongrContinuousMulEquiv (e : K ≃ₐ[ℚ] M) :
    NumberField.AdeleRing (𝓞 K) K ≃ₜ*
      NumberField.AdeleRing (𝓞 M) M := by
  refine
    { toMulEquiv := (adeleCongr e).toMulEquiv
      continuous_toFun := continuous_adeleCongr e
      continuous_invFun := ?_ }
  change Continuous ((adeleCongr e).symm)
  rw [adeleCongr_symm]
  exact continuous_adeleCongr e.symm

namespace NumberField.IdeleGroup

/-- Continuous field transport is the units functor on the same adelic map. -/
noncomputable def congrContinuousMulEquiv (e : K ≃ₐ[ℚ] M) :
    NumberField.IdeleGroup (𝓞 K) K ≃ₜ* NumberField.IdeleGroup (𝓞 M) M :=
  Units.mapContinuousMulEquiv (adeleCongrContinuousMulEquiv e)

/-- The topological equivalence retains the canonical algebraic map. -/
theorem congrContinuousMulEquiv_toMulEquiv (e : K ≃ₐ[ℚ] M) :
    (congrContinuousMulEquiv e).toMulEquiv = congr e := rfl

end NumberField.IdeleGroup

namespace NumberField.IdeleClassGroup

/-- The standard principal-quotient equivalence with its quotient topology. -/
noncomputable def congrContinuousMulEquiv (e : K ≃ₐ[ℚ] M) :
    NumberField.IdeleClassGroup (𝓞 K) K ≃ₜ* NumberField.IdeleClassGroup (𝓞 M) M := by
  refine
    { toMulEquiv := congr e
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · apply (QuotientGroup.isQuotientMap_mk
      (NumberField.IdeleGroup.principalSubgroup (𝓞 K) K)).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp
      (NumberField.IdeleGroup.congrContinuousMulEquiv e).continuous
  · apply (QuotientGroup.isQuotientMap_mk
      (NumberField.IdeleGroup.principalSubgroup (𝓞 M) M)).continuous_iff.mpr
    exact QuotientGroup.continuous_mk.comp
      (NumberField.IdeleGroup.congrContinuousMulEquiv e).symm.continuous

/-- The continuous class equivalence retains the canonical quotient map. -/
theorem congrContinuousMulEquiv_toMulEquiv (e : K ≃ₐ[ℚ] M) :
    (congrContinuousMulEquiv e).toMulEquiv = congr e := rfl

end NumberField.IdeleClassGroup

/-- The existing idèle transport is an equivalence of topological groups. -/
noncomputable def ideleCongrContinuousMulEquiv (e : K ≃ₐ[ℚ] M) :
    IdeleGroup K ≃ₜ* IdeleGroup M :=
  NumberField.IdeleGroup.congrContinuousMulEquiv e

/-- The topological and algebraic transports of idèles agree. -/
@[simp]
theorem ideleCongrContinuousMulEquiv_apply
    (e : K ≃ₐ[ℚ] M) (a : IdeleGroup K) :
    ideleCongrContinuousMulEquiv e a = ideleCongr e a :=
  rfl

/-- The canonical continuous transport of idele classes. -/
noncomputable abbrev ideleClassCongrContinuousMulEquiv
    (e : K ≃ₐ[ℚ] M) :
    IdeleClassGroup K ≃ₜ* IdeleClassGroup M :=
  NumberField.IdeleClassGroup.congrContinuousMulEquiv e

/-- The topological and algebraic transports of idèle classes agree. -/
@[simp]
theorem ideleClassCongrContinuousMulEquiv_apply
    (e : K ≃ₐ[ℚ] M) (a : IdeleClassGroup K) :
    ideleClassCongrContinuousMulEquiv e a = ideleClassCongr e a :=
  rfl

end
