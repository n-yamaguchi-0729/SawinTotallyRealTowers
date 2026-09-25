/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Kummer.FiniteKummerCupCoefficientSquare
import GaloisCohomology.Kummer.Concrete.SimpleExtension
import ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction

set_option autoImplicit false
/-!
# Normalized generators for chosen simple Kummer extensions

For a nontrivial chosen simple Kummer extension, this file chooses a cyclic
generator whose Kummer root character is the inverse of the selected primitive
root.  It also records the coefficient morphism for a tower of intermediate
fields used by finite-stage descent.
-/

open CategoryTheory
open RamificationTheory
open KummerTheory

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

theorem nthRootsSubgroup_natCard_of_primitiveRoots
    (E : Type) [Field E] (p : ℕ+)
    (hmu : (primitiveRoots (p : ℕ) E).Nonempty) :
    Nat.card (nthRootsSubgroup E (p : ℕ)) = (p : ℕ) := by
  let zeta : E := hmu.choose
  have hzeta : IsPrimitiveRoot zeta (p : ℕ) :=
    (mem_primitiveRoots p.pos).mp hmu.choose_spec
  calc
    Nat.card (nthRootsSubgroup E (p : ℕ)) =
        Nat.card (rootsOfUnity (p : ℕ) E) :=
      Nat.card_congr (nthRootsSubgroupEquivRootsOfUnity E (p : ℕ)).toEquiv
    _ = (p : ℕ) := hzeta.card_rootsOfUnity

theorem chosenSimpleKummerRootCharacter_surjective_of_nontrivial
    (K : Type) [Field K] (p : ℕ+) [Fact ((p : ℕ).Prime)]
    (hnK : ((p : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) (b : Kˣ)
    (hNT : Nontrivial
      Gal((chosenSimpleKummerExtension K p hnK b) / K)) :
    Function.Surjective
      (chosenSimpleKummerRootCharacter K p hnK hmu b) := by
  let E := chosenSimpleKummerExtension K p hnK b
  let chi := chosenSimpleKummerRootCharacter K p hnK hmu b
  let : Nontrivial Gal(E / K) := hNT
  have hmuE : (primitiveRoots (p : ℕ) E).Nonempty := by
    let zeta : K := hmu.choose
    have hzeta : IsPrimitiveRoot zeta (p : ℕ) :=
      (mem_primitiveRoots p.pos).mp hmu.choose_spec
    exact ⟨algebraMap K E zeta,
      (mem_primitiveRoots p.pos).mpr
        (hzeta.map_of_injective (algebraMap K E).injective)⟩
  have hcard : Nat.card (nthRootsSubgroup E (p : ℕ)) = (p : ℕ) :=
    nthRootsSubgroup_natCard_of_primitiveRoots E p hmuE
  have hcardPrime : (Nat.card (nthRootsSubgroup E (p : ℕ))).Prime := by
    rw [hcard]
    exact Fact.out
  let : Fact (Nat.card (nthRootsSubgroup E (p : ℕ))).Prime :=
    ⟨hcardPrime⟩
  apply MonoidHom.range_eq_top.mp
  rcases chi.range.eq_bot_or_eq_top_of_prime_card with hbot | htop
  · exfalso
    obtain ⟨sigma, hsigma⟩ := exists_ne (1 : Gal(E / K))
    apply hsigma
    apply chosenSimpleKummerRootCharacter_injective K p hnK hmu b
    have hsigma_mem : chi sigma ∈ chi.range := ⟨sigma, rfl⟩
    rw [hbot] at hsigma_mem
    have hchi : chi sigma = 1 := Subgroup.mem_bot.mp hsigma_mem
    simpa only [chi, map_one] using hchi
  · exact htop

theorem exists_chosenSimpleKummerGenerator_rootCharacter_eq
    (K : Type) [Field K] (p : ℕ+) [Fact ((p : ℕ).Prime)]
    (hnK : ((p : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) (b : Kˣ)
    (hNT : Nontrivial
      Gal((chosenSimpleKummerExtension K p hnK b) / K)) :
    let E := chosenSimpleKummerExtension K p hnK b
    let zetaUnit := finiteKummerCoefficientRootUnit K E p hmu
    let zeta : nthRootsSubgroup E (p : ℕ) :=
      ⟨zetaUnit,
        (finiteKummerCoefficientRootUnit_isPrimitiveRoot K E p hmu).pow_eq_one⟩
    ∃ g : Gal(E / K),
      (∀ sigma : Gal(E / K), sigma ∈ Subgroup.zpowers g) ∧
      chosenSimpleKummerRootCharacter K p hnK hmu b g = zeta := by
  dsimp only
  let E := chosenSimpleKummerExtension K p hnK b
  let chi := chosenSimpleKummerRootCharacter K p hnK hmu b
  let zetaUnit := finiteKummerCoefficientRootUnit K E p hmu
  have hzetaUnit : IsPrimitiveRoot zetaUnit (p : ℕ) :=
    finiteKummerCoefficientRootUnit_isPrimitiveRoot K E p hmu
  let zeta : nthRootsSubgroup E (p : ℕ) :=
    ⟨zetaUnit, hzetaUnit.pow_eq_one⟩
  obtain ⟨g, hg⟩ :=
    chosenSimpleKummerRootCharacter_surjective_of_nontrivial
      K p hnK hmu b hNT zeta
  refine ⟨g, ?_, hg⟩
  intro sigma
  have hcard : Nat.card (nthRootsSubgroup E (p : ℕ)) = (p : ℕ) := by
    let zetaE : E := algebraMap K E hmu.choose
    have hzetaE : IsPrimitiveRoot zetaE (p : ℕ) :=
      ((mem_primitiveRoots p.pos).mp hmu.choose_spec).map_of_injective
        (algebraMap K E).injective
    apply nthRootsSubgroup_natCard_of_primitiveRoots E p
    exact ⟨zetaE, (mem_primitiveRoots p.pos).mpr hzetaE⟩
  have hzeta : zeta ≠ 1 := by
    intro h
    apply hzetaUnit.ne_one (Fact.out : (p : ℕ).Prime).one_lt
    exact congrArg Subtype.val h
  have hmem : chi sigma ∈ Subgroup.zpowers zeta :=
    mem_zpowers_of_prime_card hcard hzeta
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hmem
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨i, ?_⟩
  apply chosenSimpleKummerRootCharacter_injective K p hnK hmu b
  rw [map_zpow, hg, hi]

theorem exists_chosenSimpleKummerGenerator_rootCharacter_eq_inv
    (K : Type) [Field K] (p : ℕ+) [Fact ((p : ℕ).Prime)]
    (hnK : ((p : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) (b : Kˣ)
    (hNT : Nontrivial
      Gal((chosenSimpleKummerExtension K p hnK b) / K)) :
    let E := chosenSimpleKummerExtension K p hnK b
    let zetaUnit := finiteKummerCoefficientRootUnit K E p hmu
    let zeta : nthRootsSubgroup E (p : ℕ) :=
      ⟨zetaUnit,
        (finiteKummerCoefficientRootUnit_isPrimitiveRoot K E p hmu).pow_eq_one⟩
    ∃ g : Gal(E / K),
      (∀ sigma : Gal(E / K), sigma ∈ Subgroup.zpowers g) ∧
      chosenSimpleKummerRootCharacter K p hnK hmu b g = zeta⁻¹ := by
  dsimp only
  obtain ⟨g, hg, hchi⟩ :=
    exists_chosenSimpleKummerGenerator_rootCharacter_eq
      K p hnK hmu b hNT
  refine ⟨g⁻¹, ?_, ?_⟩
  · intro sigma
    rw [Subgroup.zpowers_inv]
    exact hg sigma
  · rw [map_inv, hchi]

universe u

variable {K Ω : Type u} [Field K] [Field Ω] [Algebra K Ω]

/-- The natural unit-coefficient morphism associated to a tower of normal
intermediate fields. -/
noncomputable def intermediateFieldUnitsRepHom
    (E F : IntermediateField K Ω) (hEF : E ≤ F)
    [Normal K E] :
    Rep.res (intermediateFieldRestrictNormalHom E F hEF)
        (Rep.ofAlgebraAutOnUnits K E) ⟶
      Rep.ofAlgebraAutOnUnits K F := by
  let inc : E →+* F := (IntermediateField.inclusion hEF).toRingHom
  let m : Additive Eˣ →+ Additive Fˣ :=
    (Units.map inc.toMonoidHom).toAdditive
  apply Rep.ofHom
  refine ⟨m.toIntLinearMap, ?_⟩
  intro sigma
  apply LinearMap.ext
  intro x
  apply Additive.toMul.injective
  apply Units.ext
  apply F.val.injective
  change F.val
      (IntermediateField.inclusion hEF
        ((intermediateFieldRestrictNormalHom E F hEF sigma)
          (Additive.toMul x : Eˣ))) =
    F.val
      (sigma
        (IntermediateField.inclusion hEF (Additive.toMul x : Eˣ)))
  exact intermediateFieldRestrictNormalHom_apply_val E F hEF sigma
    (Additive.toMul x : Eˣ)

end ClassFieldTower.Martinet.Shafarevich
