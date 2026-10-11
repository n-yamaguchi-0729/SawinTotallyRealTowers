/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Subalgebra.Tower
import Mathlib.Algebra.Group.Submonoid.Membership
import Mathlib.RingTheory.Extension.Presentation.Basic
import Mathlib.RingTheory.Extension.Presentation.Core
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Localization.AsSubring
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer


/-!
# Finitely presented models over actual principal localizations

Finitely many elements of a fraction field lie in a single principal
localization of the original domain. Use the existing common-denominator
construction and the actual localization subalgebra of the fraction field.

Applying this to the coefficients of an actual finite presentation constructs
a model over that principal localization. The model is finitely presented
over both the localization and the original ring, and its scalar extension
to the original fraction field is the original algebra. No finite
presentation of the entire fraction field over the original ring is assumed.

This is the finite-model prerequisite for [Stacks, Tag 0BSM](https://stacks.math.columbia.edu/tag/0BSM). Descent of the strict splitting isomorphism remains a separate step.
-/

noncomputable section

open scoped TensorProduct nonZeroDivisors

namespace SchemeTheory

universe u

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]

/-- A finite set of fractions is contained in one actual principal
localization subalgebra, which is finitely presented over the original ring. -/
theorem exists_principalLocalization_subalgebra_of_finset (s : Finset K) :
    ∃ (d : R), d ≠ 0 ∧ ∃ C : Subalgebra R K,
      IsLocalization.Away d C ∧ Algebra.FinitePresentation R C ∧
        ∀ x ∈ s, x ∈ C := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finset (R⁰) s
  have hpow : Submonoid.powers (d : R) ≤ R⁰ := Submonoid.powers_le.mpr d.property
  let C : Subalgebra R K :=
    Localization.subalgebra.ofField K (Submonoid.powers (d : R)) hpow
  have : IsLocalization.Away (d : R) C :=
    Localization.subalgebra.isLocalization_ofField K (Submonoid.powers (d : R)) hpow
  refine ⟨d, nonZeroDivisors.ne_zero d.property, C, inferInstance,
    IsLocalization.Away.finitePresentation (d : R), ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := hd x hx
  change ∃ (a' s' : R) (_ : s' ∈ Submonoid.powers (d : R)),
    x = algebraMap R K a' * (algebraMap R K s')⁻¹
  refine ⟨a, d, Submonoid.mem_powers (d : R), ?_⟩
  rw [← div_eq_mul_inv]
  apply (eq_div_iff (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.property)).mpr
  rw [ha, Algebra.smul_def]
  exact mul_comm x (algebraMap R K d)

/-- A finitely presented fraction-field algebra has an actual model over a
single principal localization. Its displayed base-ring algebra is compatible
with the localization algebra and is itself finitely presented. -/
theorem exists_principalLocalization_finitePresentation_model
    (B : Type u) [CommRing B] [Algebra K B] [Algebra.FinitePresentation K B] :
    ∃ (d : R), d ≠ 0 ∧ ∃ C : Subalgebra R K,
      IsLocalization.Away d C ∧ Algebra.FinitePresentation R C ∧
      ∃ (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra C B₀) (_ : Algebra R B₀),
        IsScalarTower R C B₀ ∧ Algebra.FinitePresentation C B₀ ∧
          Algebra.FinitePresentation R B₀ ∧ Nonempty ((K ⊗[C] B₀) ≃ₐ[K] B) := by
  classical
  let P := Algebra.Presentation.ofFinitePresentation K B
  obtain ⟨d, hd, C, hCloc, hCfp, hcoeff⟩ :=
    exists_principalLocalization_subalgebra_of_finset R K P.finite_coeffs.toFinset
  have : IsLocalization.Away d C := hCloc
  have : Algebra.FinitePresentation R C := hCfp
  have : P.HasCoeffs C := ⟨by
    intro x hx
    have hxC : x ∈ C := hcoeff x (P.finite_coeffs.mem_toFinset.mpr hx)
    exact ⟨⟨x, hxC⟩, rfl⟩⟩
  let B₀ := P.ModelOfHasCoeffs C
  have : Algebra.FinitePresentation C B₀ := inferInstance
  have : Algebra.FinitePresentation R B₀ := Algebra.FinitePresentation.trans R C B₀
  exact ⟨d, hd, C, hCloc, hCfp, B₀, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, ⟨P.tensorModelOfHasCoeffsEquiv C⟩⟩

end SchemeTheory
