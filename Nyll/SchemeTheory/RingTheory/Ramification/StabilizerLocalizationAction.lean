/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.InertiaLocalization
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Ring.Action.End
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Ring.Equiv
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Stabilizer actions on prime localizations

Constructs the action of a prime stabilizer on the prime localization and computes it on
coefficients. It identifies localization inertia with the original ideal inertia inside the
stabilizer.
-/

noncomputable section

open scoped Pointwise

namespace SchemeTheory

universe u v

variable (B : Type u) [CommRing B]
variable (G : Type v) [Group G] [MulSemiringAction G B]
variable (Q : Ideal B) [Q.IsPrime]

omit [Q.IsPrime] in
/-- The individual original ring automorphism of a prime stabilizer element. -/
def stabilizerCoefficientRingEquiv (σ : MulAction.stabilizer G Q) : B ≃+* B :=
  RingEquiv.ofBijective (MulSemiringAction.toRingHom G B (σ : G))
    (MulDistribMulAction.toMulEquiv B (σ : G)).bijective

omit [Q.IsPrime] in
/-- The original stabilizer automorphism preserves the actual prime. -/
theorem stabilizerCoefficientRingEquiv_comap_eq (σ : MulAction.stabilizer G Q) :
    Q = Q.comap (stabilizerCoefficientRingEquiv B G Q σ).toRingHom := by
  apply Ideal.ext
  intro b
  change b ∈ Q ↔ (σ : G) • b ∈ Q
  have hmem : (σ : G) • b ∈ (σ : G) • Q ↔ (σ : G) • b ∈ Q := by
    rw [σ.property]
  exact (Ideal.smul_mem_pointwise_smul_iff (a := (σ : G)) (S := Q) (x := b)).symm.trans hmem

/-- The actual stabilizer automorphism on the literal prime localization. -/
def stabilizerLocalizationRingEquiv (σ : MulAction.stabilizer G Q) :
    Localization.AtPrime Q ≃+* Localization.AtPrime Q :=
  Localization.localRingEquiv Q Q (stabilizerCoefficientRingEquiv B G Q σ)
    (stabilizerCoefficientRingEquiv_comap_eq B G Q σ)

theorem stabilizerLocalizationRingEquiv_algebraMap
    (σ : MulAction.stabilizer G Q) (b : B) :
    stabilizerLocalizationRingEquiv B G Q σ (algebraMap B (Localization.AtPrime Q) b) =
      algebraMap B (Localization.AtPrime Q) ((σ : G) • b) :=
  Localization.localRingHom_to_map Q Q
    (stabilizerCoefficientRingEquiv B G Q σ).toRingHom
    (stabilizerCoefficientRingEquiv_comap_eq B G Q σ) b

/-- The actual localization automorphisms preserve identity and composition. -/
def stabilizerLocalizationRingAut :
    MulAction.stabilizer G Q →* (Localization.AtPrime Q ≃+* Localization.AtPrime Q) where
  toFun := stabilizerLocalizationRingEquiv B G Q
  map_one' := by
    apply RingEquiv.toRingHom_injective
    apply IsLocalization.ringHom_ext Q.primeCompl
    apply RingHom.ext
    intro b
    change stabilizerLocalizationRingEquiv B G Q 1
      (algebraMap B (Localization.AtPrime Q) b) = algebraMap B (Localization.AtPrime Q) b
    rw [stabilizerLocalizationRingEquiv_algebraMap]
    exact congrArg (algebraMap B (Localization.AtPrime Q)) (one_smul G b)
  map_mul' σ τ := by
    apply RingEquiv.toRingHom_injective
    apply IsLocalization.ringHom_ext Q.primeCompl
    apply RingHom.ext
    intro b
    change stabilizerLocalizationRingEquiv B G Q (σ * τ)
        (algebraMap B (Localization.AtPrime Q) b) =
      stabilizerLocalizationRingEquiv B G Q σ
        (stabilizerLocalizationRingEquiv B G Q τ
          (algebraMap B (Localization.AtPrime Q) b))
    rw [stabilizerLocalizationRingEquiv_algebraMap,
      stabilizerLocalizationRingEquiv_algebraMap,
      stabilizerLocalizationRingEquiv_algebraMap]
    exact congrArg (algebraMap B (Localization.AtPrime Q)) (mul_smul (σ : G) (τ : G) b)

/-- The canonical actual decomposition-group action on the prime localization. -/
instance stabilizerLocalizationMulSemiringAction :
    MulSemiringAction (MulAction.stabilizer G Q) (Localization.AtPrime Q) :=
  MulSemiringAction.compHom (Localization.AtPrime Q) (stabilizerLocalizationRingAut B G Q)

theorem stabilizerLocalization_smul_algebraMap
    (σ : MulAction.stabilizer G Q) (b : B) :
    σ • algebraMap B (Localization.AtPrime Q) b =
      algebraMap B (Localization.AtPrime Q) ((σ : G) • b) :=
  stabilizerLocalizationRingEquiv_algebraMap B G Q σ b

/-- The canonical action agrees with the already constructed individual
inertia-localization automorphism. -/
theorem stabilizerLocalizationRingEquiv_eq_inertiaLocalizationRingEquiv
    (σ : MulAction.stabilizer G Q) (hσ : (σ : G) ∈ Q.inertia G) :
    stabilizerLocalizationRingEquiv B G Q σ =
      inertiaLocalizationRingEquiv B Q (stabilizerCoefficientRingEquiv B G Q σ) hσ := rfl

omit [Group G] [MulSemiringAction G B] in
private theorem inertiaLocalizationRingEquiv_sub_mem_maximalIdeal
    (σ : B ≃+* B) (hσ : ∀ b : B, σ b - b ∈ Q) (x : Localization.AtPrime Q) :
    inertiaLocalizationRingEquiv B Q σ hσ x - x ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
  have hres := congrArg
    (fun f : Localization.AtPrime Q →+*
      IsLocalRing.ResidueField (Localization.AtPrime Q) => f x)
    (inertiaLocalizationRingEquiv_comp_residue B Q σ hσ)
  apply (IsLocalRing.residue_eq_zero_iff _).mp
  rw [map_sub]
  exact sub_eq_zero.mpr hres

/-- Actual localization inertia is exactly original ideal inertia inside the
actual prime stabilizer. -/
theorem stabilizerLocalization_mem_inertia_iff (σ : MulAction.stabilizer G Q) :
    σ ∈ (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).inertia (MulAction.stabilizer G Q) ↔
      (σ : G) ∈ Q.inertia G := by
  constructor
  · intro hσ b
    have hmem : algebraMap B (Localization.AtPrime Q) ((σ : G) • b - b) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
      rw [map_sub, ← stabilizerLocalization_smul_algebraMap]
      exact hσ (algebraMap B (Localization.AtPrime Q) b)
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff
      (Localization.AtPrime Q) Q ((σ : G) • b - b)).mp hmem
  · intro hσ x
    change stabilizerLocalizationRingEquiv B G Q σ x - x ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime Q)
    rw [stabilizerLocalizationRingEquiv_eq_inertiaLocalizationRingEquiv B G Q σ hσ]
    exact inertiaLocalizationRingEquiv_sub_mem_maximalIdeal B Q
      (stabilizerCoefficientRingEquiv B G Q σ) hσ x

theorem stabilizerLocalization_inertia_eq :
    (IsLocalRing.maximalIdeal (Localization.AtPrime Q)).inertia (MulAction.stabilizer G Q) =
      (Q.inertia G).subgroupOf (MulAction.stabilizer G Q) := by
  apply Subgroup.ext
  intro σ
  exact stabilizerLocalization_mem_inertia_iff B G Q σ

end SchemeTheory

end
