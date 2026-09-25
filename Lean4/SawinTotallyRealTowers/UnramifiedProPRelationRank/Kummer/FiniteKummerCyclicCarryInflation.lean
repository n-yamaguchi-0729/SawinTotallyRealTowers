/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Kummer.FiniteKummerCyclicFactorSet
import GaloisCohomology.Kummer.Concrete.FiniteKummerNormalizedGenerator

set_option autoImplicit false
open CategoryTheory
open RamificationTheory

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology

universe u

/-- Coefficients fixed by the selected generator, packaged in the exact
module structure carried by a representation. -/
abbrev FiniteCyclicCarryCoefficient
    {R G : Type u} [CommRing R] [CommGroup G]
    (A : Rep R G) (g : G) :=
  LinearMap.ker (Rep.applyAsHom A g - 𝟙 A).hom.toLinearMap

/-- The positive cyclic carry cocycle pulled back along a group homomorphism,
with coefficients in an arbitrary target representation. -/
noncomputable def inflatedFiniteCyclicCarryTwoCocycleOfRep
    {R G Q : Type u} [CommRing R] [CommGroup G] [Fintype G] [Group Q]
    (B : Rep R Q) (q : Q →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (b : B) (hb : ∀ x : Q, B.ρ x b = b) :
    groupCohomology.cocycles₂ B := by
  refine ⟨fun xy ↦ finiteCyclicCarry g hg (q xy.1) (q xy.2) • b, ?_⟩
  rw [groupCohomology.mem_cocycles₂_iff]
  intro x y z
  change
    finiteCyclicCarry g hg (q (x * y)) (q z) • b +
        finiteCyclicCarry g hg (q x) (q y) • b =
      B.ρ x (finiteCyclicCarry g hg (q y) (q z) • b) +
        finiteCyclicCarry g hg (q x) (q (y * z)) • b
  rw [map_nsmul, hb x, ← add_nsmul, ← add_nsmul, map_mul, map_mul]
  exact congrArg (· • b) (finiteCyclicCarry_cocycle g hg (q x) (q y) (q z))

@[simp]
theorem inflatedFiniteCyclicCarryTwoCocycleOfRep_apply
    {R G Q : Type u} [CommRing R] [CommGroup G] [Fintype G] [Group Q]
    (B : Rep R Q) (q : Q →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (b : B) (hb : ∀ x : Q, B.ρ x b = b)
    (x y : Q) :
    inflatedFiniteCyclicCarryTwoCocycleOfRep B q g hg b hb (x, y) =
      finiteCyclicCarry g hg (q x) (q y) • b := by
  simp only [inflatedFiniteCyclicCarryTwoCocycleOfRep]
  rfl

/-- Mapping a cyclic carry cocycle maps its fixed coefficient and otherwise
leaves the pulled-back positive carry factor set unchanged. -/
theorem mapCocycles₂_finiteCyclicCarryTwoCocycle
    {R G Q : Type u} [CommRing R] [CommGroup G] [Fintype G] [Group Q]
    (A : Rep R G) (B : Rep R Q) (q : Q →* G)
    (f : Rep.res q A ⟶ B)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : FiniteCyclicCarryCoefficient A g)
    (b : B) (hb : ∀ x : Q, B.ρ x b = b)
    (hab : f.hom a.1 = b) :
    groupCohomology.mapCocycles₂ q f
        (finiteCyclicCarryTwoCocycle A g hg a) =
      inflatedFiniteCyclicCarryTwoCocycleOfRep B q g hg b hb := by
  apply Subtype.ext
  funext xy
  rcases xy with ⟨x, y⟩
  change
    f.hom (finiteCyclicCarry g hg (q x) (q y) • a.1) =
      finiteCyclicCarry g hg (q x) (q y) • b
  rw [map_nsmul, hab]

/-- The image of a generator-fixed coefficient is fixed after restriction
along the cyclic quotient. -/
theorem finiteCyclicCarryCoefficient_map_fixed
    {R G Q : Type u} [CommRing R] [CommGroup G] [Fintype G] [Group Q]
    (A : Rep R G) (B : Rep R Q) (q : Q →* G)
    (f : Rep.res q A ⟶ B)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : FiniteCyclicCarryCoefficient A g)
    (x : Q) :
    B.ρ x (f.hom a.1) = f.hom a.1 := by
  have hagzero := a.2
  change A.ρ g a.1 - a.1 = 0 at hagzero
  have hag : A.ρ g a.1 = a.1 := sub_eq_zero.mp hagzero
  have ha : a.1 ∈ A.ρ.invariants :=
    (Representation.mem_invariants_iff_of_forall_mem_zpowers
      A.ρ g hg a.1).2 hag
  rw [← Rep.hom_comm_apply f x]
  exact congrArg f.hom (ha (q x))

/-- Degree-two naturality for a cyclic carry factor set. -/
theorem map_H2pi_finiteCyclicCarryTwoCocycle
    {R G Q : Type u} [CommRing R] [CommGroup G] [Fintype G] [Group Q]
    (A : Rep R G) (B : Rep R Q) (q : Q →* G)
    (f : Rep.res q A ⟶ B)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : FiniteCyclicCarryCoefficient A g)
    (b : B) (hb : ∀ x : Q, B.ρ x b = b)
    (hab : f.hom a.1 = b) :
    groupCohomology.map q f 2
        (groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A g hg a)) =
      groupCohomology.H2π B
        (inflatedFiniteCyclicCarryTwoCocycleOfRep B q g hg b hb) := by
  change
    (groupCohomology.H2π A ≫ groupCohomology.map q f 2)
        (finiteCyclicCarryTwoCocycle A g hg a) = _
  rw [groupCohomology.H2π_comp_map]
  change
    groupCohomology.H2π B
        (groupCohomology.mapCocycles₂ q f
          (finiteCyclicCarryTwoCocycle A g hg a)) = _
  rw [mapCocycles₂_finiteCyclicCarryTwoCocycle A B q f g hg a b hb hab]

/-- The arbitrary-representation pullback specializes definitionally to the
unit-representation carry cocycle used by the Kummer factor-set bridge. -/
theorem inflatedFiniteCyclicCarryTwoCocycleOfRep_units_eq
    (K M : Type) [Field K] [Field M] [Algebra K M]
    {G : Type} [CommGroup G] [Fintype G]
    (q : Gal(M / K) →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (b : Rep.ofAlgebraAutOnUnits K M)
    (hb : ∀ x : Gal(M / K),
      (Rep.ofAlgebraAutOnUnits K M).ρ x b = b) :
    inflatedFiniteCyclicCarryTwoCocycleOfRep
        (Rep.ofAlgebraAutOnUnits K M) q g hg b hb =
      inflatedFiniteCyclicCarryTwoCocycle K M q g hg b hb := by
  apply Subtype.ext
  funext xy
  rcases xy with ⟨x, y⟩
  change
    inflatedFiniteCyclicCarryTwoCocycleOfRep
        (Rep.ofAlgebraAutOnUnits K M) q g hg b hb (x, y) =
      inflatedFiniteCyclicCarryTwoCocycle K M q g hg b hb (x, y)
  rw [inflatedFiniteCyclicCarryTwoCocycleOfRep_apply,
    inflatedFiniteCyclicCarryTwoCocycle_apply]

/-- Unit-coefficient specialization of cyclic carry naturality. -/
theorem map_H2pi_finiteCyclicCarryTwoCocycle_units
    (K M : Type) [Field K] [Field M] [Algebra K M]
    {G : Type} [CommGroup G] [Fintype G]
    (A : Rep ℤ G) (q : Gal(M / K) →* G)
    (f : Rep.res q A ⟶ Rep.ofAlgebraAutOnUnits K M)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : FiniteCyclicCarryCoefficient A g)
    (b : Rep.ofAlgebraAutOnUnits K M)
    (hb : ∀ x : Gal(M / K),
      (Rep.ofAlgebraAutOnUnits K M).ρ x b = b)
    (hab : f.hom a.1 = b) :
    groupCohomology.map q f 2
        (groupCohomology.H2π A (finiteCyclicCarryTwoCocycle A g hg a)) =
      groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K M)
        (inflatedFiniteCyclicCarryTwoCocycle K M q g hg b hb) := by
  rw [← inflatedFiniteCyclicCarryTwoCocycleOfRep_units_eq
    K M q g hg b hb]
  exact map_H2pi_finiteCyclicCarryTwoCocycle A
    (Rep.ofAlgebraAutOnUnits K M) q f g hg a b hb hab

section IntermediateFields

variable {K Omega : Type u} [Field K] [Field Omega] [Algebra K Omega]

@[simp]
theorem intermediateFieldUnitsRepHom_apply
    (E F : IntermediateField K Omega) (hEF : E ≤ F)
    [Normal K E] (x : Additive Eˣ) :
    (intermediateFieldUnitsRepHom E F hEF).hom x =
      Additive.ofMul
        (Units.map (IntermediateField.inclusion hEF).toRingHom.toMonoidHom
          (Additive.toMul x)) := by
  rfl

/-- Intermediate-field unit inclusion carries a base-field unit to the same
base-field unit in the larger intermediate field. -/
theorem intermediateFieldUnitsRepHom_baseUnit
    (E F : IntermediateField K Omega) (hEF : E ≤ F)
    [Normal K E] (a : Kˣ) :
    (intermediateFieldUnitsRepHom E F hEF).hom
        (Additive.ofMul (Units.map (algebraMap K E).toMonoidHom a)) =
      Additive.ofMul (Units.map (algebraMap K F).toMonoidHom a) := by
  apply Additive.toMul.injective
  apply Units.ext
  change (IntermediateField.inclusion hEF)
      (algebraMap K E (a : K)) = algebraMap K F (a : K)
  exact (IntermediateField.inclusion hEF).commutes (a : K)

end IntermediateFields

end ClassFieldTower.Martinet.Shafarevich
