/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ArtinSchreier.CohomologyVanishing
import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupTopology
import Mathlib.FieldTheory.Galois.Infinite

/-! # Vanishing of prime-field H² on open Galois subgroups -/

namespace ArtinSchreierTheory
universe u v
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

/-- Prime-field two-cocycles are coboundaries on every open Galois subgroup
in characteristic `p`. -/
theorem exists_zmod_primitive_of_two_cocycle_open
    (p : ℕ) [Fact p.Prime] [CharP Ω p]
    (H : OpenSubgroup Gal(Ω/K))
    (z : ↥(H : Subgroup Gal(Ω/K)) → ↥(H : Subgroup Gal(Ω/K)) → ZMod p)
    (hz : ∀ σ τ υ : (H : Subgroup Gal(Ω/K)),
      z σ (τ * υ) + z τ υ = z (σ * τ) υ + z σ τ)
    (hlc : IsLocallyConstant
      (fun x : ↥(H : Subgroup Gal(Ω/K)) × ↥(H : Subgroup Gal(Ω/K)) => z x.1 x.2)) :
    ∃ d : ↥(H : Subgroup Gal(Ω/K)) → ZMod p, IsLocallyConstant d ∧
      ∀ σ τ : (H : Subgroup Gal(Ω/K)), d τ - d (σ * τ) + d σ = z σ τ := by
  let E : IntermediateField K Ω := IntermediateField.fixedField (H : Subgroup Gal(Ω/K))
  let closedH : ClosedSubgroup Gal(Ω/K) := ⟨H.toSubgroup, H.isClosed⟩
  have hfix : E.fixingSubgroup = (H : Subgroup Gal(Ω/K)) :=
    InfiniteGalois.fixingSubgroup_fixedField closedH
  have : FiniteDimensional K E := (InfiniteGalois.isOpen_iff_finite E).mp (by
    rw [hfix]
    exact H.isOpen)
  let e₀ : (H : Subgroup Gal(Ω/K)) ≃ₜ* E.fixingSubgroup :=
    { toMulEquiv := MulEquiv.subgroupCongr hfix.symm
      continuous_toFun := Continuous.subtype_mk continuous_subtype_val
        (fun x => hfix.symm ▸ x.property)
      continuous_invFun := Continuous.subtype_mk continuous_subtype_val
        (fun x => hfix ▸ x.property) }
  let e : (H : Subgroup Gal(Ω/K)) ≃ₜ* Gal(Ω/E) :=
    e₀.trans (KummerTheory.fixingSubgroupContinuousEquiv E)
  let zE : Gal(Ω/E) → Gal(Ω/E) → ZMod p := fun σ τ => z (e.symm σ) (e.symm τ)
  have hzE (σ τ υ : Gal(Ω/E)) :
      zE σ (τ * υ) + zE τ υ = zE (σ * τ) υ + zE σ τ := by
    simpa only [zE, map_mul] using hz (e.symm σ) (e.symm τ) (e.symm υ)
  obtain ⟨dE, hdElc, hdE⟩ := exists_zmod_primitive_of_two_cocycle (K := E) p zE hzE
    (hlc.comp_continuous (e.symm.continuous.prodMap e.symm.continuous))
  refine ⟨fun σ => dE (e σ), hdElc.comp_continuous e.continuous, ?_⟩
  intro σ τ
  simpa only [map_mul, zE, e.symm_apply_apply] using hdE (e σ) (e τ)

end ArtinSchreierTheory
