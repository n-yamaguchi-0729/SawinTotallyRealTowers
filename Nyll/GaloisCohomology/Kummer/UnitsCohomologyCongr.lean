/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.LiftedUnitsCohomology
public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-!
# Unit cohomology under a field isomorphism

Conjugation identifies the automorphism groups, while the same field
isomorphism identifies their actual unit representations.
-/

@[expose] public section

open CategoryTheory

universe u v w

namespace ClassFieldTower.Cohomology

/-- The unit map of the same algebra equivalence intertwines the actual
Galois actions through conjugation. -/
theorem unitsMapEquiv_action
    (K : Type v) (L : Type u) (M : Type w)
    [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) (σ : Gal(L/K)) (x : Additive Lˣ) :
    (Units.mapEquiv e.toMulEquiv).toAdditive
        ((Rep.ofAlgebraAutOnUnits K L).ρ σ x) =
      (Rep.ofAlgebraAutOnUnits K M).ρ (AlgEquiv.autCongr e σ)
        ((Units.mapEquiv e.toMulEquiv).toAdditive x) := by
  apply Additive.toMul.injective
  apply Units.ext
  change e (σ (x.toMul : L)) = e (σ (e.symm (e (x.toMul : L))))
  rw [e.symm_apply_apply]

/-- An actual algebra equivalence transports field-unit cohomology in every degree. -/
noncomputable def unitsCohomologyCongrTop
    (K : Type v) (L M : Type) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) (n : ℕ) :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) n ≅
      groupCohomology (Rep.ofAlgebraAutOnUnits K M) n :=
  groupCohomology.mapIso (AlgEquiv.autCongr e)
    (Units.mapEquiv e.toMulEquiv).toAdditive.toIntLinearEquiv (by
      intro σ
      apply LinearMap.ext
      intro x
      exact unitsMapEquiv_action K L M e σ x) n

/-- Pulling back a concrete unit-valued degree-one cochain through an
algebra equivalence commutes with its pointwise coboundary. Both the
automorphism and coefficient maps are the actual maps of that equivalence. -/
theorem unitsCochain_d₁₂_congr
    (K : Type v) (L M : Type) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) (a : Gal(M/K) → Additive Mˣ) (σ τ : Gal(L/K)) :
    groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits K L)
        (fun γ => Additive.ofMul
          (Units.map e.symm.toMonoidHom (a (AlgEquiv.autCongr e γ)).toMul)) (σ, τ) =
      Additive.ofMul (Units.map e.symm.toMonoidHom
        ((groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits K M) a)
          (AlgEquiv.autCongr e σ, AlgEquiv.autCongr e τ)).toMul) := by
  let UL : (Rep.ofAlgebraAutOnUnits K L) ≃+ Additive Lˣ := Rep.toAdditive
  let UM : (Rep.ofAlgebraAutOnUnits K M) ≃+ Additive Mˣ := Rep.toAdditive
  let U : (Rep.ofAlgebraAutOnUnits K L) ≃+ (Rep.ofAlgebraAutOnUnits K M) :=
    UL.trans ((Units.mapEquiv e.toMulEquiv).toAdditive.trans UM.symm)
  let aM : Gal(M/K) → (Rep.ofAlgebraAutOnUnits K M) := fun γ => UM.symm (a γ)
  have hforward (γ : Gal(L/K)) (x : Rep.ofAlgebraAutOnUnits K L) :
      U ((Rep.ofAlgebraAutOnUnits K L).ρ γ x) =
        (Rep.ofAlgebraAutOnUnits K M).ρ (AlgEquiv.autCongr e γ) (U x) := by
    exact unitsMapEquiv_action K L M e γ (UL x)
  have haction (γ : Gal(L/K)) (x : Rep.ofAlgebraAutOnUnits K M) :
      (Rep.ofAlgebraAutOnUnits K L).ρ γ (U.symm x) =
        U.symm ((Rep.ofAlgebraAutOnUnits K M).ρ (AlgEquiv.autCongr e γ) x) := by
    apply U.injective
    rw [hforward, U.apply_symm_apply, U.apply_symm_apply]
  change groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits K L)
      (fun γ => U.symm (aM (AlgEquiv.autCongr e γ))) (σ, τ) =
    U.symm ((groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits K M) aM)
      (AlgEquiv.autCongr e σ, AlgEquiv.autCongr e τ))
  change (Rep.ofAlgebraAutOnUnits K L).ρ σ (U.symm (aM (AlgEquiv.autCongr e τ))) -
      U.symm (aM (AlgEquiv.autCongr e (σ * τ))) +
        U.symm (aM (AlgEquiv.autCongr e σ)) =
    U.symm ((Rep.ofAlgebraAutOnUnits K M).ρ (AlgEquiv.autCongr e σ)
      (aM (AlgEquiv.autCongr e τ)) -
        aM (AlgEquiv.autCongr e σ * AlgEquiv.autCongr e τ) +
          aM (AlgEquiv.autCongr e σ))
  rw [map_add, map_sub, haction, map_mul]

/-- Pullback of actual unit cochains through a field equivalence commutes
with the native lifted-integer differential. The coefficient function is
the same unit map as in the original integer-coefficient statement. -/
theorem unitsCochain_d₁₂_congr_lifted
    (K : Type v) (L M : Type u) [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    (e : L ≃ₐ[K] M) (a : Gal(M/K) → Additive Mˣ) (σ τ : Gal(L/K)) :
    groupCohomology.d₁₂ (liftedGaloisUnitsRep K L)
        (fun γ => Additive.ofMul
          (Units.map e.symm.toMonoidHom (a (AlgEquiv.autCongr e γ)).toMul)) (σ, τ) =
      Additive.ofMul (Units.map e.symm.toMonoidHom
        ((groupCohomology.d₁₂ (liftedGaloisUnitsRep K M) a)
          (AlgEquiv.autCongr e σ, AlgEquiv.autCongr e τ)).toMul) := by
  let UL : (liftedGaloisUnitsRep K L) ≃+ Additive Lˣ := AddEquiv.refl _
  let UM : (liftedGaloisUnitsRep K M) ≃+ Additive Mˣ := AddEquiv.refl _
  let U : (liftedGaloisUnitsRep K L) ≃+ (liftedGaloisUnitsRep K M) :=
    UL.trans ((Units.mapEquiv e.toMulEquiv).toAdditive.trans UM.symm)
  let aM : Gal(M/K) → (liftedGaloisUnitsRep K M) := fun γ => UM.symm (a γ)
  have hforward (γ : Gal(L/K)) (x : liftedGaloisUnitsRep K L) :
      U ((liftedGaloisUnitsRep K L).ρ γ x) =
        (liftedGaloisUnitsRep K M).ρ (AlgEquiv.autCongr e γ) (U x) := by
    exact unitsMapEquiv_action K L M e γ (UL x)
  have haction (γ : Gal(L/K)) (x : liftedGaloisUnitsRep K M) :
      (liftedGaloisUnitsRep K L).ρ γ (U.symm x) =
        U.symm ((liftedGaloisUnitsRep K M).ρ (AlgEquiv.autCongr e γ) x) := by
    apply U.injective
    rw [hforward, U.apply_symm_apply, U.apply_symm_apply]
  change groupCohomology.d₁₂ (liftedGaloisUnitsRep K L)
      (fun γ => U.symm (aM (AlgEquiv.autCongr e γ))) (σ, τ) =
    U.symm ((groupCohomology.d₁₂ (liftedGaloisUnitsRep K M) aM)
      (AlgEquiv.autCongr e σ, AlgEquiv.autCongr e τ))
  change (liftedGaloisUnitsRep K L).ρ σ (U.symm (aM (AlgEquiv.autCongr e τ))) -
      U.symm (aM (AlgEquiv.autCongr e (σ * τ))) +
        U.symm (aM (AlgEquiv.autCongr e σ)) =
    U.symm ((liftedGaloisUnitsRep K M).ρ (AlgEquiv.autCongr e σ)
      (aM (AlgEquiv.autCongr e τ)) -
        aM (AlgEquiv.autCongr e σ * AlgEquiv.autCongr e τ) +
          aM (AlgEquiv.autCongr e σ))
  rw [map_add, map_sub, haction, map_mul]

end ClassFieldTower.Cohomology
