/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Cohomology.ContinuousMapFiniteStage
import Nyll.ProCGroups.ProC.InverseLimits.FiniteQuotients
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite

/-!
# Finite Galois stages for continuous functions in two variables

Finite discrete-valued continuous functions on a pair of Galois groups
factor through one actual finite Galois intermediate field.
-/

namespace GaloisCohomology
open scoped Topology
open ProCGroups ProCGroups.ProC
universe u v w
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]

/-- A common finite Galois stage controls both coordinates. -/
theorem exists_finiteGalois_factor_continuous_pair
    {Y : Type w} [TopologicalSpace Y] [Finite Y] [DiscreteTopology Y]
    (z : Gal(Ω/K) × Gal(Ω/K) → Y) (hz : Continuous z) :
    ∃ (E : FiniteGaloisIntermediateField K Ω) (zE : Gal(E/K) → Gal(E/K) → Y),
      ∀ σ τ : Gal(Ω/K), zE (AlgEquiv.restrictNormalHom E σ)
        (AlgEquiv.restrictNormalHom E τ) = z (σ, τ) := by
  classical
  obtain ⟨U, zU, _hzU, hfac⟩ :=
    ClassFieldTower.Cohomology.exists_openNormalSubgroupInClass_factor_continuousMap_finite
      FiniteGroupClass.allFinite_formation hasOpenNormalBasisInClass_allFinite z hz
  let j₁ : Gal(Ω/K) →ₜ* Gal(Ω/K) × Gal(Ω/K) :=
    { toFun := fun σ => (σ, 1)
      map_one' := rfl
      map_mul' := fun σ τ => by simp only [Prod.mk_mul_mk, one_mul]
      continuous_toFun := continuous_id.prodMk continuous_const }
  let j₂ : Gal(Ω/K) →ₜ* Gal(Ω/K) × Gal(Ω/K) :=
    { toFun := fun σ => (1, σ)
      map_one' := rfl
      map_mul' := fun σ τ => by simp only [Prod.mk_mul_mk, one_mul]
      continuous_toFun := continuous_const.prodMk continuous_id }
  let V : Set Gal(Ω/K) :=
    j₁ ⁻¹' ((U.1 : Subgroup (Gal(Ω/K) × Gal(Ω/K))) : Set (Gal(Ω/K) × Gal(Ω/K))) ∩
      j₂ ⁻¹' ((U.1 : Subgroup (Gal(Ω/K) × Gal(Ω/K))) : Set (Gal(Ω/K) × Gal(Ω/K)))
  have hVopen : IsOpen V :=
    ((openNormalSubgroup_isOpen U.1).preimage j₁.continuous).inter
      ((openNormalSubgroup_isOpen U.1).preimage j₂.continuous)
  have hVone : (1 : Gal(Ω/K)) ∈ V :=
    ⟨show j₁ 1 ∈ (U.1 : Subgroup _) from by rw [map_one]; exact Subgroup.one_mem _,
      show j₂ 1 ∈ (U.1 : Subgroup _) from by rw [map_one]; exact Subgroup.one_mem _⟩
  obtain ⟨E, hE⟩ := (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois
    (k := K) (K := Ω) V).mp (hVopen.mem_nhds hVone)
  let r : Gal(Ω/K) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hr : Function.Surjective r := AlgEquiv.restrictNormalHom_surjective Ω
  have hrel {σ τ : Gal(Ω/K)} (hστ : r σ = r τ) : σ * τ⁻¹ ∈ E.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker]
    change r (σ * τ⁻¹) = 1
    rw [map_mul, map_inv, hστ, mul_inv_cancel]
  have hfactor (σ τ σ' τ' : Gal(Ω/K))
      (hσ : r σ = r σ') (hτ : r τ = r τ') : z (σ, τ) = z (σ', τ') := by
    rw [congrFun hfac (σ, τ), congrFun hfac (σ', τ')]
    apply congrArg zU
    apply OpenNormalSubgroupInClass.quotientProj_eq_quotientProj_iff.mpr
    have hx : j₁ (σ * σ'⁻¹) ∈ (U.1 : Subgroup (Gal(Ω/K) × Gal(Ω/K))) :=
      (hE (hrel hσ)).1
    have hy : j₂ (τ * τ'⁻¹) ∈ (U.1 : Subgroup (Gal(Ω/K) × Gal(Ω/K))) :=
      (hE (hrel hτ)).2
    have hxy := (U.1 : Subgroup (Gal(Ω/K) × Gal(Ω/K))).mul_mem hx hy
    change (σ * σ'⁻¹, 1) * (1, τ * τ'⁻¹) ∈
      (U.1 : Subgroup (Gal(Ω/K) × Gal(Ω/K))) at hxy
    simpa only [div_eq_mul_inv, Prod.mk_mul_mk, mul_one, one_mul, Prod.inv_mk] using hxy
  let zE : Gal(E/K) → Gal(E/K) → Y :=
    fun σ τ => z ((hr σ).choose, (hr τ).choose)
  refine ⟨E, zE, ?_⟩
  intro σ τ
  exact hfactor _ _ σ τ (hr (r σ)).choose_spec (hr (r τ)).choose_spec

end GaloisCohomology
