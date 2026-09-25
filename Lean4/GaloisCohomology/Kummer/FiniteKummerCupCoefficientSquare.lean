/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.DiscreteH2Comparison
import GaloisCohomology.Kummer.FiniteKummerCoefficientH2
import Mathlib.FieldTheory.KrullTopology

set_option autoImplicit false
/-!
# The finite Kummer cup-product coefficient square

For a finite Galois extension, changing the coefficients of the ordinary
degree-two character cup class by a chosen primitive root is represented by
applying the chosen-root homomorphism pointwise to its two-cocycle.  Combining
this square with the discrete continuous/ordinary comparison gives the same
description for the continuous character cup.

This is only a coefficient-change statement.  It neither assumes the Galois
group is cyclic nor identifies the resulting class with a norm or Hilbert
symbol.
-/

open CategoryTheory
open ClassFieldTower.ProP

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable (p : ℕ+)

/-- The ordinary character cup cocycle after applying the chosen-root
coefficient homomorphism pointwise. -/
noncomputable def finiteKummerCupCoefficientTwoCocycle
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(L / K))) :
    groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K L) :=
  groupCohomology.mapCocycles₂ (MonoidHom.id (Gal(L / K)))
    (finiteKummerCoefficientRepHom K L p hmu)
    (Cohomology.ordinaryH1CupTwoCocycle chi psi)

@[simp]
theorem finiteKummerCupCoefficientTwoCocycle_apply
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(L / K)))
    (sigma tau : Gal(L / K)) :
    finiteKummerCupCoefficientTwoCocycle K L p hmu chi psi (sigma, tau) =
      finiteKummerCoefficientAddHom K L p hmu
        (ULift.up
          (chi (Additive.ofMul sigma) * psi (Additive.ofMul tau))) := by
  rfl

/-- The same coefficient-changed cup cocycle in the general `Fin 2`
inhomogeneous-cochain model. -/
noncomputable def finiteKummerCupCoefficientCocycle
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(L / K))) :
    groupCohomology.cocycles (Rep.ofAlgebraAutOnUnits K L) 2 :=
  groupCohomology.cocyclesMap (MonoidHom.id (Gal(L / K)))
    (finiteKummerCoefficientRepHom K L p hmu) 2
    ((groupCohomology.isoCocycles₂
      (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ))))).inv
      (Cohomology.ordinaryH1CupTwoCocycle chi psi))

/-- In the general inhomogeneous-cochain model, the coefficient-changed cup
cocycle is obtained by applying the chosen-root map pointwise. -/
theorem finiteKummerCupCoefficientCocycle_apply
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(L / K)))
    (x : Fin 2 → Gal(L / K)) :
    groupCohomology.iCocycles (Rep.ofAlgebraAutOnUnits K L) 2
        (finiteKummerCupCoefficientCocycle K L p hmu chi psi) x =
      finiteKummerCoefficientAddHom K L p hmu
        (groupCohomology.iCocycles
          (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ)))) 2
          ((groupCohomology.isoCocycles₂
            (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ))))).inv
            (Cohomology.ordinaryH1CupTwoCocycle chi psi)) x) := by
  exact finiteKummerCoefficientCocyclesMap_apply K L p hmu _ x

/-- The general and pair-shaped presentations of the coefficient-changed cup
cocycle agree. -/
theorem finiteKummerCupCoefficientCocycle_isoCocycles₂_hom
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(L / K))) :
    (groupCohomology.isoCocycles₂ (Rep.ofAlgebraAutOnUnits K L)).hom
        (finiteKummerCupCoefficientCocycle K L p hmu chi psi) =
      finiteKummerCupCoefficientTwoCocycle K L p hmu chi psi := by
  simp only [finiteKummerCupCoefficientCocycle,
    finiteKummerCupCoefficientTwoCocycle,
    groupCohomology.cocyclesMap_comp_isoCocycles₂_hom_apply,
    Iso.inv_hom_id_apply]

/-- Naturality of `H²π` for the chosen-root coefficient morphism. -/
theorem finiteKummerCoefficientH2Map_H2π
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (z : groupCohomology.cocycles₂
      (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ))))) :
    finiteKummerCoefficientH2Map K L p hmu
        (groupCohomology.H2π
          (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ)))) z) =
      groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
        (groupCohomology.mapCocycles₂ (MonoidHom.id (Gal(L / K)))
          (finiteKummerCoefficientRepHom K L p hmu) z) := by
  change
    (groupCohomology.H2π
        (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ)))) ≫
      groupCohomology.map (MonoidHom.id (Gal(L / K)))
        (finiteKummerCoefficientRepHom K L p hmu) 2) z =
      (groupCohomology.mapCocycles₂ (MonoidHom.id (Gal(L / K)))
          (finiteKummerCoefficientRepHom K L p hmu) ≫
        groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)) z
  rw [groupCohomology.H2π_comp_map]

/-- The quotient-model version of the ordinary coefficient square. -/
theorem finiteKummerCoefficientH2Map_ordinaryH1CupClass_quotient
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(L / K))) :
    finiteKummerCoefficientH2Map K L p hmu
        (Cohomology.ordinaryH1CupClass chi psi) =
      groupCohomology.π (Rep.ofAlgebraAutOnUnits K L) 2
        (finiteKummerCupCoefficientCocycle K L p hmu chi psi) := by
  change
    finiteKummerCoefficientH2Map K L p hmu
        (groupCohomology.π
          (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ)))) 2
          ((groupCohomology.isoCocycles₂
            (Rep.trivial ℤ (Gal(L / K)) (ULift (ZMod (p : ℕ))))).inv
            (Cohomology.ordinaryH1CupTwoCocycle chi psi))) = _
  exact finiteKummerCoefficientH2Map_quotient K L p hmu _

/-- The chosen-root coefficient map sends the ordinary character cup class
to the class of the pointwise chosen-root cup cocycle. -/
theorem finiteKummerCoefficientH2Map_ordinaryH1CupClass
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(L / K))) :
    finiteKummerCoefficientH2Map K L p hmu
        (Cohomology.ordinaryH1CupClass chi psi) =
      groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
        (finiteKummerCupCoefficientTwoCocycle K L p hmu chi psi) := by
  exact finiteKummerCoefficientH2Map_H2π K L p hmu
    (Cohomology.ordinaryH1CupTwoCocycle chi psi)

section FiniteGalois

variable [FiniteDimensional K L]

/-- For a finite Galois extension, the discrete comparison followed by the
chosen-root coefficient map sends the continuous character cup to the class
of the pointwise chosen-root ordinary cup cocycle. -/
theorem finiteKummerCoefficientH2Map_discreteContinuousH1Cup
    [IsGalois K L]
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(L / K))) :
    finiteKummerCoefficientH2Map K L p hmu
        (Cohomology.discreteContinuousH2AddEquiv
          (Cohomology.continuousH1CupProductLifted chi psi)) =
      groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
        (finiteKummerCupCoefficientTwoCocycle K L p hmu chi psi) := by
  rw [Cohomology.discreteContinuousH2AddEquiv_continuousH1Cup]
  exact finiteKummerCoefficientH2Map_ordinaryH1CupClass K L p hmu chi psi

end FiniteGalois

end ClassFieldTower.Martinet.Shafarevich
