/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.FiniteKummerCoefficientH2
public import Nyll.GaloisCohomology.Kummer.Concrete.FiniteDualSeparation
public import Nyll.GaloisCohomology.Kummer.Concrete.PrimitiveRootCoordinates
public import Nyll.GaloisCohomology.Kummer.Concrete.SimpleExtension
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCharacterCoordinates
public import Nyll.ValuedFieldTheory.Ramification.GaloisValuation.IntermediateFieldRestriction
public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Subgroup.Map
public import Mathlib.FieldTheory.Fixed
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Normalized generators for chosen simple Kummer extensions

The actual root character of a chosen simple Kummer extension has a negative
coordinate with respect to the selected primitive root. Its image index gives
a normalized cyclic generator even when the extension degree is smaller than
the coefficient exponent, including the trivial extension. At prime exponent,
the existing nontrivial case specializes to the inverse primitive root.

The file also records the coefficient morphism for a tower of intermediate
fields used by finite-stage descent.
-/

@[expose] public section

open CategoryTheory
open RamificationTheory
open KummerTheory

universe u

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

theorem nthRootsSubgroup_natCard_of_primitiveRoots
    (E : Type u) [Field E] (p : ℕ+)
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
    (K : Type u) [Field K] (p : ℕ+) [Fact ((p : ℕ).Prime)]
    (hnK : ((p : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) (b : Kˣ)
    (hNT : Nontrivial
      Gal((chosenSimpleKummerExtension K p hnK b)/K)) :
    Function.Surjective
      (chosenSimpleKummerRootCharacter K p hnK hmu b) := by
  let E := chosenSimpleKummerExtension K p hnK b
  let chi := chosenSimpleKummerRootCharacter K p hnK hmu b
  let : Nontrivial Gal(E/K) := hNT
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
    obtain ⟨sigma, hsigma⟩ := exists_ne (1 : Gal(E/K))
    apply hsigma
    apply chosenSimpleKummerRootCharacter_injective K p hnK hmu b
    have hsigma_mem : chi sigma ∈ chi.range := ⟨sigma, rfl⟩
    rw [hbot] at hsigma_mem
    have hchi : chi sigma = 1 := Subgroup.mem_bot.mp hsigma_mem
    simpa only [chi, map_one] using hchi
  · exact htop

theorem exists_chosenSimpleKummerGenerator_rootCharacter_eq
    (K : Type u) [Field K] (p : ℕ+) [Fact ((p : ℕ).Prime)]
    (hnK : ((p : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) (b : Kˣ)
    (hNT : Nontrivial
      Gal((chosenSimpleKummerExtension K p hnK b)/K)) :
    let E := chosenSimpleKummerExtension K p hnK b
    let zetaUnit := finiteKummerCoefficientRootUnit K E p hmu
    let zeta : nthRootsSubgroup E (p : ℕ) :=
      ⟨zetaUnit,
        (finiteKummerCoefficientRootUnit_isPrimitiveRoot K E p hmu).pow_eq_one⟩
    ∃ g : Gal(E/K),
      (∀ sigma : Gal(E/K), sigma ∈ Subgroup.zpowers g) ∧
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
    (K : Type u) [Field K] (p : ℕ+) [Fact ((p : ℕ).Prime)]
    (hnK : ((p : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) (b : Kˣ)
    (hNT : Nontrivial
      Gal((chosenSimpleKummerExtension K p hnK b)/K)) :
    let E := chosenSimpleKummerExtension K p hnK b
    let zetaUnit := finiteKummerCoefficientRootUnit K E p hmu
    let zeta : nthRootsSubgroup E (p : ℕ) :=
      ⟨zetaUnit,
        (finiteKummerCoefficientRootUnit_isPrimitiveRoot K E p hmu).pow_eq_one⟩
    ∃ g : Gal(E/K),
      (∀ sigma : Gal(E/K), sigma ∈ Subgroup.zpowers g) ∧
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

/-- The negative coordinate of the actual Kummer root quotient with
respect to the supplied primitive root in its simple extension. -/
noncomputable def chosenSimpleKummerNegativeRootCharacterOfRoot
    (K : Type u) [Field K] (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ)
    (ζ : (chosenSimpleKummerExtension K n hnK b)ˣ)
    (hζ : IsPrimitiveRoot ζ (n : ℕ)) :
    Gal((chosenSimpleKummerExtension K n hnK b)/K) →*
      Multiplicative (ZMod (n : ℕ)) := by
  let E := chosenSimpleKummerExtension K n hnK b
  let e := (nthRootsSubgroupEquivRootsOfUnity E (n : ℕ)).trans
    ((MulEquiv.subgroupCongr hζ.zpowers_eq.symm).trans
      hζ.zmodEquivZPowers.symm.toMultiplicativeRight)
  exact e.toMonoidHom.comp (chosenSimpleKummerRootCharacter K n hnK hmu b)⁻¹

/-- Decoding with the supplied primitive root recovers the inverse of
the actual Galois root quotient. -/
theorem chosenSimpleKummerNegativeRootCharacterOfRoot_coefficient
    (K : Type u) [Field K] (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ)
    (ζ : (chosenSimpleKummerExtension K n hnK b)ˣ)
    (hζ : IsPrimitiveRoot ζ (n : ℕ))
    (sigma : Gal((chosenSimpleKummerExtension K n hnK b)/K)) :
    primitiveRootCoordinate hζ (Multiplicative.toAdd
      (chosenSimpleKummerNegativeRootCharacterOfRoot K n hnK hmu b ζ hζ sigma)) =
      (chosenSimpleKummerRootCharacter K n hnK hmu b sigma :
        (chosenSimpleKummerExtension K n hnK b)ˣ)⁻¹ := by
  let E := chosenSimpleKummerExtension K n hnK b
  let χ := chosenSimpleKummerRootCharacter K n hnK hmu b
  let z : Subgroup.zpowers ζ :=
    (MulEquiv.subgroupCongr hζ.zpowers_eq.symm)
      (nthRootsSubgroupEquivRootsOfUnity E (n : ℕ) ((χ sigma)⁻¹))
  change (hζ.zmodEquivZPowers
      (hζ.zmodEquivZPowers.symm (Additive.ofMul z))).toMul.1 =
    (χ sigma : Eˣ)⁻¹
  rw [hζ.zmodEquivZPowers.apply_symm_apply]
  rfl

/-- Negative coordinates still separate all automorphisms because the chosen
radical generates the simple extension. -/
theorem chosenSimpleKummerNegativeRootCharacterOfRoot_injective
    (K : Type u) [Field K] (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ)
    (ζ : (chosenSimpleKummerExtension K n hnK b)ˣ)
    (hζ : IsPrimitiveRoot ζ (n : ℕ)) :
    Function.Injective
      (chosenSimpleKummerNegativeRootCharacterOfRoot K n hnK hmu b ζ hζ) := by
  intro sigma tau h
  apply chosenSimpleKummerRootCharacter_injective K n hnK hmu b
  apply Subtype.ext
  apply inv_injective
  rw [← chosenSimpleKummerNegativeRootCharacterOfRoot_coefficient K n hnK hmu b ζ hζ sigma,
    ← chosenSimpleKummerNegativeRootCharacterOfRoot_coefficient K n hnK hmu b ζ hζ tau, h]

/-- The image index of the negative Kummer character supplies an actual
generator with root quotient `ζ⁻ᵏ` and standard coordinates scaled by `k`.
The extension degree is allowed to be any divisor of the coefficient exponent. -/
theorem exists_chosenSimpleKummerGenerator_scaled_negativeRootCharacterOfRoot
    (K : Type u) [Field K] (n : ℕ+)
    (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ)
    (ζ : (chosenSimpleKummerExtension K n hnK b)ˣ)
    (hζ : IsPrimitiveRoot ζ (n : ℕ)) :
    let E := chosenSimpleKummerExtension K n hnK b
    let _ : FiniteDimensional K E :=
      chosenSimpleKummerExtension_finiteDimensional K n hnK b
    ∃ k : ℕ, 0 < k ∧ (n : ℕ) = k * Nat.card Gal(E/K) ∧
      ∃ (g : Gal(E/K)) (hg : ∀ sigma : Gal(E/K), sigma ∈ Subgroup.zpowers g),
        (chosenSimpleKummerRootCharacter K n hnK hmu b g : Eˣ) = ζ ^ (-(k : ℤ)) ∧
        ∀ sigma : Gal(E/K),
          (Multiplicative.toAdd
            (chosenSimpleKummerNegativeRootCharacterOfRoot K n hnK hmu b ζ hζ sigma)).val =
            k * (Cohomology.finiteCyclicGeneratorCoordinate g hg sigma).val := by
  intro E hfinite
  obtain ⟨k, hk, hcard, g, hg, hgχ, hcoordinate⟩ :=
    Cohomology.exists_generator_scaled_character
      (chosenSimpleKummerNegativeRootCharacterOfRoot K n hnK hmu b ζ hζ)
      (chosenSimpleKummerNegativeRootCharacterOfRoot_injective K n hnK hmu b ζ hζ)
  refine ⟨k, hk, hcard, g, hg, ?_, hcoordinate⟩
  have hroot := chosenSimpleKummerNegativeRootCharacterOfRoot_coefficient
    K n hnK hmu b ζ hζ g
  rw [hgχ, toAdd_ofAdd, primitiveRootCoordinate_natCast] at hroot
  rw [zpow_neg, zpow_natCast]
  exact inv_eq_iff_eq_inv.mp hroot.symm

/-- The negative root coordinate for the selected finite Kummer coefficient
root is the corresponding specialization of supplied-root coordinates. -/
noncomputable def chosenSimpleKummerNegativeRootCharacter
    (K : Type u) [Field K] (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    Gal((chosenSimpleKummerExtension K n hnK b)/K) →* Multiplicative (ZMod (n : ℕ)) :=
  chosenSimpleKummerNegativeRootCharacterOfRoot K n hnK hmu b
    (finiteKummerCoefficientRootUnit K (chosenSimpleKummerExtension K n hnK b) n hmu)
    (finiteKummerCoefficientRootUnit_isPrimitiveRoot K
      (chosenSimpleKummerExtension K n hnK b) n hmu)

/-- The original chosen-root coefficient map decodes its specialized
negative character to the inverse root quotient. -/
theorem chosenSimpleKummerNegativeRootCharacter_coefficient
    (K : Type u) [Field K] (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ)
    (sigma : Gal((chosenSimpleKummerExtension K n hnK b)/K)) :
    (finiteKummerCoefficientAddHom K (chosenSimpleKummerExtension K n hnK b)
      n hmu (ULift.up (Multiplicative.toAdd
        (chosenSimpleKummerNegativeRootCharacter K n hnK hmu b sigma)))).toMul =
      (chosenSimpleKummerRootCharacter K n hnK hmu b sigma :
        (chosenSimpleKummerExtension K n hnK b)ˣ)⁻¹ :=
  chosenSimpleKummerNegativeRootCharacterOfRoot_coefficient K n hnK hmu b
    (finiteKummerCoefficientRootUnit K (chosenSimpleKummerExtension K n hnK b) n hmu)
    (finiteKummerCoefficientRootUnit_isPrimitiveRoot K
      (chosenSimpleKummerExtension K n hnK b) n hmu) sigma

theorem chosenSimpleKummerNegativeRootCharacter_injective
    (K : Type u) [Field K] (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    Function.Injective (chosenSimpleKummerNegativeRootCharacter K n hnK hmu b) :=
  chosenSimpleKummerNegativeRootCharacterOfRoot_injective K n hnK hmu b
    (finiteKummerCoefficientRootUnit K (chosenSimpleKummerExtension K n hnK b) n hmu)
    (finiteKummerCoefficientRootUnit_isPrimitiveRoot K
      (chosenSimpleKummerExtension K n hnK b) n hmu)

/-- The previous selected-root normalization is recovered from the
supplied-root theorem without repeating the cyclic construction. -/
theorem exists_chosenSimpleKummerGenerator_scaled_negativeRootCharacter
    (K : Type u) [Field K] (n : ℕ+) (hnK : ((n : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (n : ℕ) K).Nonempty) (b : Kˣ) :
    let E := chosenSimpleKummerExtension K n hnK b
    let _ : FiniteDimensional K E :=
      chosenSimpleKummerExtension_finiteDimensional K n hnK b
    let ζUnit := finiteKummerCoefficientRootUnit K E n hmu
    let ζ : nthRootsSubgroup E (n : ℕ) :=
      ⟨ζUnit, (finiteKummerCoefficientRootUnit_isPrimitiveRoot K E n hmu).pow_eq_one⟩
    ∃ k : ℕ, 0 < k ∧ (n : ℕ) = k * Nat.card Gal(E/K) ∧
      ∃ (g : Gal(E/K)) (hg : ∀ sigma : Gal(E/K), sigma ∈ Subgroup.zpowers g),
        chosenSimpleKummerRootCharacter K n hnK hmu b g = ζ ^ (-(k : ℤ)) ∧
        ∀ sigma : Gal(E/K),
          (Multiplicative.toAdd
            (chosenSimpleKummerNegativeRootCharacter K n hnK hmu b sigma)).val =
            k * (Cohomology.finiteCyclicGeneratorCoordinate g hg sigma).val := by
  intro E hfinite ζUnit ζ
  obtain ⟨k, hk, hcard, g, hg, hroot, hcoordinate⟩ :=
    exists_chosenSimpleKummerGenerator_scaled_negativeRootCharacterOfRoot
      K n hnK hmu b ζUnit (finiteKummerCoefficientRootUnit_isPrimitiveRoot K E n hmu)
  exact ⟨k, hk, hcard, g, hg, Subtype.ext hroot, hcoordinate⟩

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
