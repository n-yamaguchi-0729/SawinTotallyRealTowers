/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.AutomorphismTransport
import Mathlib.Algebra.Group.Subgroup.Map

/-!
# Automorphisms of the concrete principal-unit groups

A field automorphism preserving the valuation ring restricts to every level
of the principal-unit filtration, with its original action on field elements.
-/

namespace LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup

universe u v

variable {K : Type u} [Field K]
variable (F : ValuationTheory.DiscreteValuationField.CompleteDVF.{u, v} K)

/-- Restriction of a valuation-ring-preserving automorphism to `U^n`. -/
noncomputable def equivOfPreserves
    (e : K ≃+* K)
    (hmem : ∀ x : K, x ∈ F.valuation.valuationSubring ↔ e x ∈ F.valuation.valuationSubring)
    (n : ℕ) : higherPrincipalUnitGroup F n ≃* higherPrincipalUnitGroup F n :=
  ((valuationSubringUnitEquivOfPreserves F e hmem).subgroupMap
    (higherPrincipalUnitGroup F n)).trans
      (MulEquiv.subgroupCongr
        (higherPrincipalUnitGroup_map_valuationSubringUnitEquivOfPreserves F e hmem n))

/-- The restricted automorphism retains the original action on field elements. -/
@[simp] theorem equivOfPreserves_apply_coe
    (e : K ≃+* K)
    (hmem : ∀ x : K, x ∈ F.valuation.valuationSubring ↔ e x ∈ F.valuation.valuationSubring)
    (n : ℕ) (a : higherPrincipalUnitGroup F n) :
    (((equivOfPreserves F e hmem n a : F.valuationSubringˣ) : F.valuationSubring) : K) =
      e (((a : F.valuationSubringˣ) : F.valuationSubring) : K) := by
  change (((valuationSubringUnitEquivOfPreserves F e hmem
    (a : F.valuationSubringˣ) : F.valuationSubringˣ) : F.valuationSubring) : K) =
      e (((a : F.valuationSubringˣ) : F.valuationSubring) : K)
  rw [valuationSubringUnitEquivOfPreserves_apply]
  rfl

/-- Restriction preserves the identity automorphism. -/
@[simp] theorem equivOfPreserves_refl (n : ℕ) :
    equivOfPreserves F (RingEquiv.refl K) (fun _ => Iff.rfl) n =
      MulEquiv.refl (higherPrincipalUnitGroup F n) := by
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  exact equivOfPreserves_apply_coe F (RingEquiv.refl K) (fun _ => Iff.rfl) n a

/-- Restriction preserves composition, with `e` applied before `f`. -/
theorem equivOfPreserves_trans
    (e f : K ≃+* K)
    (he : ∀ x : K, x ∈ F.valuation.valuationSubring ↔ e x ∈ F.valuation.valuationSubring)
    (hf : ∀ x : K, x ∈ F.valuation.valuationSubring ↔ f x ∈ F.valuation.valuationSubring)
    (n : ℕ) :
    equivOfPreserves F (e.trans f) (fun x => (he x).trans (hf (e x))) n =
      (equivOfPreserves F e he n).trans (equivOfPreserves F f hf n) := by
  apply MulEquiv.ext
  intro a
  apply Subtype.ext
  apply Units.ext
  apply Subtype.ext
  simp only [MulEquiv.trans_apply, equivOfPreserves_apply_coe, RingEquiv.trans_apply]

end LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup
