/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPrincipalUnitPadicEquivariance
import Nyll.ValuedFieldTheory.LocalField.Analytic.MixedCharPadicIntMapEquivariance
import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.Module.RingHom

/-!
# The actual p-adic representations of valuation-preserving automorphisms

The concrete field action restricts to principal units. Its compatibility
with the constructed p-adic scalars supplies the linear representation laws.
-/

namespace LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation

universe u w

variable {K : Type u} [Field K] {Δ : Type w} [Monoid Δ]
variable (v : _root_.Valuation K (WithZero (Multiplicative ℤ)))
variable [ValuationTheory.DiscreteValuationField.Valuation.IsCompleteDiscrete v]
variable (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField v.valuationSubring) p]
variable (σ : Δ →* (K ≃+* K)) (hval : ∀ (g : Δ) (x : K), v (σ g x) = v x)

open CompleteDVF.higherPrincipalUnitGroup

/-- The concrete automorphism action on principal units is p-adic linear. -/
noncomputable def principalUnitRepresentationOfMixedChar :
    @Representation ℤ_[p] Δ
      (Additive (CompleteDVF.higherPrincipalUnitGroup (completeDVFOfWithZeroValuation v) 1))
      inferInstance inferInstance inferInstance (principalUnitPadicModuleOfMixedChar v p) := by
  let F := completeDVFOfWithZeroValuation v
  let : Module ℤ_[p] (Additive (CompleteDVF.higherPrincipalUnitGroup F 1)) :=
    principalUnitPadicModuleOfMixedChar v p
  let e (g : Δ) := equivOfPreserves F (σ g)
    (fun x => by change v x ≤ 1 ↔ v (σ g x) ≤ 1; rw [hval g x]) 1
  refine
    { toFun := fun g =>
        { toFun := (e g).toAdditive
          map_add' := (e g).toAdditive.map_add
          map_smul' := ?_ }
      map_one' := ?_
      map_mul' := ?_ }
  · intro a x
    apply Additive.toMul.injective
    exact principalUnitPadicPowOfMixedChar_equivOfPreserves v p (σ g) (hval g)
      a (Additive.toMul x)
  · apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    apply Subtype.ext
    change (((e 1 (Additive.toMul x) : F.valuationSubringˣ) : F.valuationSubring) : K) =
      ((((Additive.toMul x : CompleteDVF.higherPrincipalUnitGroup F 1) :
        F.valuationSubringˣ) : F.valuationSubring) : K)
    rw [equivOfPreserves_apply_coe, σ.map_one, RingAut.one_apply]
  · intro g h
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Subtype.ext
    apply Units.ext
    apply Subtype.ext
    change (((e (g * h) (Additive.toMul x) : F.valuationSubringˣ) : F.valuationSubring) : K) =
      (((e g (e h (Additive.toMul x)) : F.valuationSubringˣ) : F.valuationSubring) : K)
    simp only [e, equivOfPreserves_apply_coe, σ.map_mul, RingAut.mul_apply]

/-- The original field action is linear over the actual p-adic integer map. -/
noncomputable def fieldRepresentationOfMixedChar :
    @Representation ℤ_[p] Δ K inferInstance inferInstance inferInstance
      (padicIntToFieldOfMixedChar v p).toModule := by
  let : Module ℤ_[p] K := (padicIntToFieldOfMixedChar v p).toModule
  refine
    { toFun := fun g =>
        { toFun := σ g
          map_add' := (σ g).map_add
          map_smul' := ?_ }
      map_one' := ?_
      map_mul' := ?_ }
  · intro a x
    exact ringEquiv_padicIntToFieldOfMixedChar_mul v p (σ g) (hval g) a x
  · apply LinearMap.ext
    intro x
    change σ 1 x = x
    rw [σ.map_one, RingAut.one_apply]
  · intro g h
    apply LinearMap.ext
    intro x
    change σ (g * h) x = σ g (σ h x)
    rw [σ.map_mul, RingAut.mul_apply]

end LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation
