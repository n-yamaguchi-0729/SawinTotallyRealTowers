/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.RelationRank.FinitePlaceMuPKummerTameUnramified
import ClassFieldTheory.KummerTheory.Concrete.SUnitPreparation.FiniteRadicalSupport

set_option autoImplicit false
/-!
# Finite ramification support for natural `mu_p` Kummer classes

A represented global power class can ramify only where its representative or
the exponent `p` fails to be a unit.  Both exceptional sets are finite.  This
packages the resulting finite-support statement for every natural-coefficient
Kummer class.
-/

open NumberField IsDedekindDomain
open scoped Classical NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open KummerTheory

variable (K : Type) [Field K] [NumberField K]
variable (p : ℕ) [Fact p.Prime]

/-- The field unit represented by the prime exponent `p`. -/
def finitePlaceKummerPrimeUnit : Kˣ :=
  Units.mk0 (p : K)
    (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

include p in
/-- A finite set containing every possible ramified finite place of the
Kummer class represented by `a`. -/
noncomputable def finitePlaceAbsoluteKummerMuPBadPlaces (a : Kˣ) :
    Finset (HeightOneSpectrum (𝓞 K)) :=
  chosenUnitFiniteSupport (K := K) a ∪
    chosenUnitFiniteSupport (K := K) (finitePlaceKummerPrimeUnit K p)

/-- Outside the finite bad-place set, the inertia component of a represented
natural-`mu_p` Kummer class vanishes. -/
theorem finitePlaceAbsoluteKummerMuPH1RamificationLinearMap_eq_zero_of_not_mem_badPlaces
    (hmu : (primitiveRoots p K).Nonempty) (a : Kˣ)
    (v : HeightOneSpectrum (𝓞 K))
    (hv : v ∉ finitePlaceAbsoluteKummerMuPBadPlaces K p a) :
    finitePlaceAbsoluteKummerMuPH1RamificationLinearMap K p v
        (Additive.ofMul
          (QuotientGroup.mk'
            (powMonoidHom p : Kˣ →* Kˣ).range a)) = 0 := by
  have hva : v ∉ chosenUnitFiniteSupport (K := K) a := by
    intro hva
    exact hv (Finset.mem_union_left _ hva)
  have hvp : v ∉
      chosenUnitFiniteSupport (K := K) (finitePlaceKummerPrimeUnit K p) := by
    intro hvp
    exact hv (Finset.mem_union_right _ hvp)
  let S := chosenUnitFiniteSupport (K := K) a
  let aS : SUnitGroup (K := K) S :=
    ⟨a, mem_sUnitGroup_chosenUnitFiniteSupport (K := K) a⟩
  have hpUnit :
      v.valuation K ((finitePlaceKummerPrimeUnit K p : Kˣ) : K) = 1 :=
    ((mem_SUnitGroup_iff
      (chosenUnitFiniteSupport (K := K) (finitePlaceKummerPrimeUnit K p))
      (finitePlaceKummerPrimeUnit K p)).mp
      (mem_sUnitGroup_chosenUnitFiniteSupport
        (K := K) (finitePlaceKummerPrimeUnit K p))) v hvp
  have hp : v.valuation K (p : K) = 1 := by
    change v.valuation K (p : K) = 1 at hpUnit
    exact hpUnit
  rw [finitePlaceAbsoluteKummerMuPH1RamificationLinearMap_mk]
  simpa only [S, aS] using
    finitePlaceAbsoluteKummerMuPInertiaH1Class_eq_zero_of_sUnit
      K p hmu S aS v hva hp

/-- Every natural-`mu_p` Kummer class has only finitely many possibly
nonzero inertia components. -/
theorem finitePlaceAbsoluteKummerMuPH1Ramification_exists_finset
    (hmu : (primitiveRoots p K).Nonempty)
    (x : absolutePowerClassModP K p) :
    ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ v, v ∉ S →
      finitePlaceAbsoluteKummerMuPH1RamificationLinearMap K p v x = 0 := by
  let q : (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) :=
    Additive.toMul x
  change ∃ S, ∀ v, v ∉ S →
    finitePlaceAbsoluteKummerMuPH1RamificationLinearMap K p v
      (Additive.ofMul q) = 0
  refine QuotientGroup.induction_on q ?_
  intro a
  exact
    ⟨finitePlaceAbsoluteKummerMuPBadPlaces K p a,
      fun v hv ↦
        finitePlaceAbsoluteKummerMuPH1RamificationLinearMap_eq_zero_of_not_mem_badPlaces
          K p hmu a v hv⟩

/-- The set of finite places where a natural-`mu_p` Kummer class has a
nonzero inertia component is finite. -/
theorem finitePlaceAbsoluteKummerMuPH1Ramification_support_finite
    (hmu : (primitiveRoots p K).Nonempty)
    (x : absolutePowerClassModP K p) :
    Set.Finite {v : HeightOneSpectrum (𝓞 K) |
      finitePlaceAbsoluteKummerMuPH1RamificationLinearMap K p v x ≠ 0} := by
  obtain ⟨S, hS⟩ :=
    finitePlaceAbsoluteKummerMuPH1Ramification_exists_finset K p hmu x
  apply S.finite_toSet.subset
  intro v hv
  change finitePlaceAbsoluteKummerMuPH1RamificationLinearMap K p v x ≠ 0 at hv
  by_contra hvS
  exact hv (hS v hvS)

end ClassFieldTower.Martinet.Shafarevich
