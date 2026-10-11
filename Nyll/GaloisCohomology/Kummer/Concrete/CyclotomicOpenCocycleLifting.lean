/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.CyclotomicCocycleLifting
import Nyll.GaloisCohomology.Kummer.Concrete.FixedSubgroupTopology
import Mathlib.FieldTheory.Galois.Infinite

/-!
# Cyclotomic cocycle lifting on open Galois subgroups

The fixed field of an open subgroup is finite over the base. Its actual
relative Galois group supplies the cocycle lift without extra hypotheses.
-/

namespace KummerTheory
universe u v
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω] [IsSepClosed Ω]

/-- Finite cyclotomic cocycles lift on every open Galois subgroup. -/
theorem exists_cyclotomic_cocycle_lift_open
    (p : ℕ) [Fact p.Prime] [NeZero (p : Ω)]
    (H : OpenSubgroup Gal(Ω/K)) (k : ℕ)
    (c : ↥(H : Subgroup Gal(Ω/K)) → ZMod (p ^ 1))
    (hc : ∀ σ τ : (H : Subgroup Gal(Ω/K)), c (σ * τ) = c σ +
      ((cyclotomicCharacter Ω p σ.val.toRingEquiv : PadicInt p).toZModPow 1) * c τ)
    (hlc : IsLocallyConstant c) :
    ∃ d : ↥(H : Subgroup Gal(Ω/K)) → ZMod (p ^ (k + 1)),
      IsLocallyConstant d ∧
      (∀ σ τ : (H : Subgroup Gal(Ω/K)), d (σ * τ) = d σ +
        ((cyclotomicCharacter Ω p σ.val.toRingEquiv : PadicInt p).toZModPow (k + 1)) * d τ) ∧
      ∀ σ : (H : Subgroup Gal(Ω/K)),
        ZMod.castHom (pow_dvd_pow p (by omega : 1 ≤ k + 1))
          (ZMod (p ^ 1)) (d σ) = c σ := by
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
    e₀.trans (fixingSubgroupContinuousEquiv E)
  have he (σ : (H : Subgroup Gal(Ω/K))) : (e σ).toRingEquiv = σ.val.toRingEquiv := by
    rfl
  have hei (σ : Gal(Ω/E)) : (e.symm σ).val.toRingEquiv = σ.toRingEquiv := by
    rw [← he, e.apply_symm_apply]
  let cE : Gal(Ω/E) → ZMod (p ^ 1) := fun σ => c (e.symm σ)
  have hcE (σ τ : Gal(Ω/E)) : cE (σ * τ) = cE σ +
      ((cyclotomicCharacter Ω p σ.toRingEquiv : PadicInt p).toZModPow 1) * cE τ := by
    change c (e.symm (σ * τ)) = _
    rw [map_mul, hc, hei]
  obtain ⟨dE, hdElc, hdE, hred⟩ := exists_cyclotomic_cocycle_lift
    (K := E) p k cE hcE (hlc.comp_continuous e.symm.continuous)
  refine ⟨fun σ => dE (e σ), hdElc.comp_continuous e.continuous, ?_, ?_⟩
  · intro σ τ
    change dE (e (σ * τ)) = dE (e σ) +
      ((cyclotomicCharacter Ω p σ.val.toRingEquiv : PadicInt p).toZModPow (k + 1)) * dE (e τ)
    rw [map_mul, hdE, he]
  · intro σ
    exact (hred (e σ)).trans (congrArg c (e.symm_apply_apply σ))

end KummerTheory
