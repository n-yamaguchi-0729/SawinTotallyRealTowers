/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.FiniteCyclicCarryCocycle
import GaloisCohomology.Kummer.Concrete.FiniteKummerNormalizedGenerator

set_option autoImplicit false
/-!
# Coordinates for normalized simple Kummer generators

For the normalized generator of a nontrivial simple Kummer extension, the
Galois generator coordinate is the negative of the chosen-root coordinate of
the Kummer character.  The final section records the corresponding
simplifications when the cyclic group is trivial.
-/

open CategoryTheory
open KummerTheory

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology

/-- The selected primitive root generates the full group of `p`-th roots of
unity. -/
theorem finiteKummerCoefficientRoot_generates_nthRootsSubgroup
    (K L : Type) [Field K] [Field L] [Algebra K L]
    (p : ℕ+) [Fact ((p : ℕ).Prime)]
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) :
    let zetaUnit := finiteKummerCoefficientRootUnit K L p hmu
    let zeta : nthRootsSubgroup L (p : ℕ) :=
      ⟨zetaUnit,
        (finiteKummerCoefficientRootUnit_isPrimitiveRoot K L p hmu).pow_eq_one⟩
    ∀ x : nthRootsSubgroup L (p : ℕ), x ∈ Subgroup.zpowers zeta := by
  dsimp only
  let zetaUnit := finiteKummerCoefficientRootUnit K L p hmu
  have hzetaUnit : IsPrimitiveRoot zetaUnit (p : ℕ) :=
    finiteKummerCoefficientRootUnit_isPrimitiveRoot K L p hmu
  let zeta : nthRootsSubgroup L (p : ℕ) :=
    ⟨zetaUnit, hzetaUnit.pow_eq_one⟩
  intro x
  have hcard : Nat.card (nthRootsSubgroup L (p : ℕ)) = (p : ℕ) := by
    apply nthRootsSubgroup_natCard_of_primitiveRoots
    exact ⟨algebraMap K L hmu.choose,
      (mem_primitiveRoots p.pos).mpr
        (((mem_primitiveRoots p.pos).mp hmu.choose_spec).map_of_injective
          (algebraMap K L).injective)⟩
  have hcardPrime : (Nat.card (nthRootsSubgroup L (p : ℕ))).Prime := by
    rw [hcard]
    exact Fact.out
  let : Fact (Nat.card (nthRootsSubgroup L (p : ℕ))).Prime :=
    ⟨hcardPrime⟩
  apply mem_zpowers_of_prime_card hcard
  intro h
  apply hzetaUnit.ne_one (Fact.out : (p : ℕ).Prime).one_lt
  exact congrArg Subtype.val h

/-- A character taking the chosen generator to the inverse target generator
negates the two generator coordinates. -/
theorem finiteCyclicGeneratorCoordinate_eq_neg_characterCoordinate
    {G M : Type} [Group G] [Fintype G] [Group M] [Fintype M]
    (chi : G →* M) (g : G)
    (hg : ∀ sigma : G, sigma ∈ Subgroup.zpowers g)
    (zeta : M) (hzeta : ∀ x : M, x ∈ Subgroup.zpowers zeta)
    (hcard : Nat.card M = Nat.card G) (hchi : chi g = zeta⁻¹)
    (sigma : G) :
    finiteCyclicGeneratorCoordinate g hg sigma =
      -Multiplicative.toAdd
        ((zmodMulEquivOfGenerator hzeta hcard).symm (chi sigma)) := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg sigma)
  rw [finiteCyclicGeneratorCoordinate_zpow, map_zpow, hchi]
  simp only [inv_zpow]
  rw [← zpow_neg]
  simp

/-- The generator coordinate on a chosen simple Kummer extension.  The
canonical finite-dimensional structure is kept local to this definition. -/
noncomputable def chosenSimpleKummerGeneratorCoordinate
    (K : Type) [Field K] (p : ℕ+)
    (hnK : ((p : ℕ) : K) ≠ 0) (b : Kˣ)
    (g : Gal((chosenSimpleKummerExtension K p hnK b) / K))
    (hg : ∀ sigma : Gal((chosenSimpleKummerExtension K p hnK b) / K),
      sigma ∈ Subgroup.zpowers g)
    (sigma : Gal((chosenSimpleKummerExtension K p hnK b) / K)) :
    ZMod (Nat.card Gal((chosenSimpleKummerExtension K p hnK b) / K)) := by
  let : FiniteDimensional K
      (chosenSimpleKummerExtension K p hnK b) :=
    chosenSimpleKummerExtension_finiteDimensional K p hnK b
  exact finiteCyclicGeneratorCoordinate g hg sigma

/-- The Kummer root character, expressed in the chosen primitive-root
coordinate and transported to the cardinality of its Galois group. -/
noncomputable def chosenSimpleKummerRootCharacterCoordinate
    (K : Type) [Field K] (p : ℕ+) [Fact ((p : ℕ).Prime)]
    (hnK : ((p : ℕ) : K) ≠ 0)
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty) (b : Kˣ)
    (hcardG : Nat.card
      Gal((chosenSimpleKummerExtension K p hnK b) / K) = (p : ℕ))
    (sigma : Gal((chosenSimpleKummerExtension K p hnK b) / K)) :
    ZMod (Nat.card Gal((chosenSimpleKummerExtension K p hnK b) / K)) :=
  let E := chosenSimpleKummerExtension K p hnK b
  let hrootCard : Nat.card (nthRootsSubgroup E (p : ℕ)) = (p : ℕ) :=
    nthRootsSubgroup_natCard_of_primitiveRoots E p
      ⟨algebraMap K E hmu.choose,
        (mem_primitiveRoots p.pos).mpr
          (((mem_primitiveRoots p.pos).mp hmu.choose_spec).map_of_injective
            (algebraMap K E).injective)⟩
  Multiplicative.toAdd
    ((zmodMulEquivOfGenerator
      (finiteKummerCoefficientRoot_generates_nthRootsSubgroup K E p hmu)
      (hrootCard.trans hcardG.symm)).symm
      (chosenSimpleKummerRootCharacter K p hnK hmu b sigma))

/-- A nontrivial chosen simple Kummer extension has a normalized generator;
its order is `p`, and its generator coordinate is the negative Kummer
character coordinate. -/
theorem exists_chosenSimpleKummerNormalizedGeneratorCoordinate
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
    ∃ (g : Gal(E / K))
        (hg : ∀ sigma : Gal(E / K), sigma ∈ Subgroup.zpowers g)
        (hcardG : Nat.card Gal(E / K) = (p : ℕ)),
      chosenSimpleKummerRootCharacter K p hnK hmu b g = zeta⁻¹ ∧
      ∀ sigma : Gal(E / K),
        chosenSimpleKummerGeneratorCoordinate K p hnK b g hg sigma =
          -chosenSimpleKummerRootCharacterCoordinate
            K p hnK hmu b hcardG sigma := by
  dsimp only
  let E := chosenSimpleKummerExtension K p hnK b
  let chi := chosenSimpleKummerRootCharacter K p hnK hmu b
  let zetaUnit := finiteKummerCoefficientRootUnit K E p hmu
  let zeta : nthRootsSubgroup E (p : ℕ) :=
    ⟨zetaUnit,
      (finiteKummerCoefficientRootUnit_isPrimitiveRoot K E p hmu).pow_eq_one⟩
  obtain ⟨g, hg, hchiG⟩ :=
    exists_chosenSimpleKummerGenerator_rootCharacter_eq_inv
      K p hnK hmu b hNT
  have hmuE : (primitiveRoots (p : ℕ) E).Nonempty :=
    ⟨algebraMap K E hmu.choose,
      (mem_primitiveRoots p.pos).mpr
        (((mem_primitiveRoots p.pos).mp hmu.choose_spec).map_of_injective
          (algebraMap K E).injective)⟩
  have hrootCard : Nat.card (nthRootsSubgroup E (p : ℕ)) = (p : ℕ) :=
    nthRootsSubgroup_natCard_of_primitiveRoots E p hmuE
  have hcardG : Nat.card Gal(E / K) = (p : ℕ) := by
    calc
      Nat.card Gal(E / K) = Nat.card (nthRootsSubgroup E (p : ℕ)) := by
        apply Nat.card_congr
        exact Equiv.ofBijective chi ⟨
          chosenSimpleKummerRootCharacter_injective K p hnK hmu b,
          chosenSimpleKummerRootCharacter_surjective_of_nontrivial
            K p hnK hmu b hNT⟩
      _ = (p : ℕ) := hrootCard
  refine ⟨g, hg, hcardG, hchiG, ?_⟩
  intro sigma
  let : FiniteDimensional K E :=
    chosenSimpleKummerExtension_finiteDimensional K p hnK b
  change finiteCyclicGeneratorCoordinate g hg sigma = _
  exact finiteCyclicGeneratorCoordinate_eq_neg_characterCoordinate
    chi g hg zeta
    (finiteKummerCoefficientRoot_generates_nthRootsSubgroup K E p hmu)
    (hrootCard.trans hcardG.symm) hchiG sigma

section Trivial

open CategoryTheory Representation

/-- In a trivial group, `1` is a generator. -/
theorem finiteCyclic_one_generates_of_subsingleton
    {G : Type} [Group G] [Subsingleton G] (x : G) :
    x ∈ Subgroup.zpowers (1 : G) := by
  rw [Subsingleton.elim x 1]
  exact Subgroup.one_mem _

@[simp]
theorem finiteCyclicGeneratorCoordinate_eq_zero_of_subsingleton
    {G : Type} [Group G] [Fintype G] [Subsingleton G] (x : G) :
    finiteCyclicGeneratorCoordinate 1
      finiteCyclic_one_generates_of_subsingleton x = 0 := by
  rw [Subsingleton.elim x 1]
  exact finiteCyclicGeneratorCoordinate_one 1 _

/-- The normalized carry cocycle vanishes on a trivial cyclic group. -/
theorem finiteCyclicCarryTwoCocycle_eq_zero_of_subsingleton
    {R G : Type} [CommRing R] [CommGroup G] [Fintype G] [Subsingleton G]
    (A : Rep R G)
    (a : LinearMap.ker
      (Rep.applyAsHom A (1 : G) - 𝟙 A).hom.toLinearMap)
    (x : G × G) :
    finiteCyclicCarryTwoCocycle A 1
      finiteCyclic_one_generates_of_subsingleton a x = 0 := by
  rcases x with ⟨sigma, tau⟩
  rw [Subsingleton.elim sigma 1, Subsingleton.elim tau 1]
  exact finiteCyclicCarryTwoCocycle_one_left A 1 _ a 1

end Trivial

end ClassFieldTower.Martinet.Shafarevich
