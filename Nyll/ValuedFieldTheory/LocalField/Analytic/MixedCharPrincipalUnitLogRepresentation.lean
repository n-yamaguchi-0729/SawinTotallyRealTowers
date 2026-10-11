/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharAutomorphismRepresentations
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogLinearity
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitLogEquivariance
import Mathlib.RepresentationTheory.Intertwining

/-!
# The actual principal-unit logarithm as an intertwining map

The logarithm is linear for the canonical p-adic module structures and
intertwines the actual valuation-preserving automorphisms. This supplies
its image as a subrepresentation without any image-stability hypothesis.
-/

noncomputable section

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u w

variable {K : Type u} [Field K] [CharZero K]
variable (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
  [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
  (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]

/-- The actual logarithm is linear over the canonical p-adic integer map. -/
def principalUnitLogLinearMapOfMixedChar :
    @LinearMap ℤ_[p] ℤ_[p] _ _ (RingHom.id ℤ_[p])
      (Additive (CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1)) K
      _ _ (principalUnitPadicModuleOfMixedChar v p) (padicIntToFieldOfMixedChar v p).toModule :=
  @LinearMap.mk ℤ_[p] ℤ_[p] _ _ (RingHom.id ℤ_[p])
    (Additive (CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1)) K
    _ _ (principalUnitPadicModuleOfMixedChar v p) (padicIntToFieldOfMixedChar v p).toModule
    (principalUnitLogOfMixedChar v p).toAdditiveLeft.toAddHom
    (fun a x => principalUnitLogOfMixedChar_padicPow v p a (Additive.toMul x))

/-- The linear map retains the original principal-unit logarithm. -/
@[simp] theorem principalUnitLogLinearMapOfMixedChar_apply
    (x : Additive (CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1)) :
    principalUnitLogLinearMapOfMixedChar v p x =
      (principalUnitLogOfMixedChar v p (Additive.toMul x)).toAdd := rfl

variable {Γ : Type w} [Monoid Γ]
  (σ : Γ →* (K ≃+* K)) (hval : ∀ (g : Γ) (x : K), v (σ g x) = v x)

/-- The original logarithm intertwines the two actual automorphism actions. -/
def principalUnitLogIntertwinerOfMixedChar :
    @Representation.IntertwiningMap ℤ_[p] Γ
      (Additive (CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1)) K
      _ _ _ _ (principalUnitPadicModuleOfMixedChar v p) (padicIntToFieldOfMixedChar v p).toModule
      (principalUnitRepresentationOfMixedChar v p σ hval)
      (fieldRepresentationOfMixedChar v p σ hval) :=
  @Representation.IntertwiningMap.mk ℤ_[p] Γ
    (Additive (CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1)) K
    _ _ _ _ (principalUnitPadicModuleOfMixedChar v p) (padicIntToFieldOfMixedChar v p).toModule
    (principalUnitRepresentationOfMixedChar v p σ hval)
    (fieldRepresentationOfMixedChar v p σ hval)
    (principalUnitLogLinearMapOfMixedChar v p) (fun g => by
      apply DFunLike.ext
      intro x
      exact principalUnitLogOfMixedChar_equivOfPreserves v p (σ g) (hval g)
        (Additive.toMul x))

/-- The intertwining map has the same values as the original logarithm. -/
@[simp] theorem principalUnitLogIntertwinerOfMixedChar_apply
    (x : Additive (CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1)) :
    principalUnitLogIntertwinerOfMixedChar v p σ hval x =
      (principalUnitLogOfMixedChar v p (Additive.toMul x)).toAdd := rfl

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
