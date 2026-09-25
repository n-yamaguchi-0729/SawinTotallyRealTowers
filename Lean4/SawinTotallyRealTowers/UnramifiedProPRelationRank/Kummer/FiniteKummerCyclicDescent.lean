/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.FiniteKummerCyclicCarryInflation

set_option autoImplicit false
/-!
# Finite Kummer cup descent to a cyclic carry class

This file composes the Kummer factor-set calculation with degree-two
naturality.  Thus the coefficient-changed cup class on an arbitrary common
finite Galois stage is the image of the normalized carry class on its cyclic
Kummer quotient.
-/

open CategoryTheory
open ClassFieldTower.ProP

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology

/-- Arbitrary-pair cyclic descent: once the common Kummer stage acts on a
chosen root by `chi`, and its cyclic quotient coordinate is `-psi`, the
coefficient-changed cup class is the pullback of the quotient's positive
carry class. -/
theorem finiteKummerCup_H2pi_eq_map_finiteCyclicCarry
    (K M : Type) [Field K] [Field M] [Algebra K M]
    (p : ℕ+)
    {G : Type} [CommGroup G] [Fintype G]
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod
      (p := (p : ℕ)) (G := Gal(M / K)))
    (q : Gal(M / K) →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : Nat.card G = (p : ℕ))
    (hcoord : ∀ sigma : Gal(M / K),
      (finiteCyclicGeneratorCoordinate g hg (q sigma)).val =
        (-psi (Additive.ofMul sigma)).val)
    (A : Rep ℤ G)
    (f : Rep.res q A ⟶ Rep.ofAlgebraAutOnUnits K M)
    (c : FiniteCyclicCarryCoefficient A g)
    (alpha a : Rep.ofAlgebraAutOnUnits K M)
    (halpha : ∀ sigma : Gal(M / K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma alpha =
        (finiteKummerCoefficientRepHom K M p hmu).hom
          (ULift.up (chi (Additive.ofMul sigma))) + alpha)
    (hpow : (p : ℕ) • alpha = a)
    (ha : ∀ sigma : Gal(M / K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma a = a)
    (hca : f.hom c.1 = a) :
    groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K M)
        (finiteKummerCupCoefficientTwoCocycle K M p hmu chi psi) =
      groupCohomology.map q f 2
        (groupCohomology.H2π A
          (finiteCyclicCarryTwoCocycle A g hg c)) := by
  rw [map_H2pi_finiteCyclicCarryTwoCocycle_units
    K M A q f g hg c a ha hca]
  exact finiteKummerCup_H2pi_eq_inflatedFiniteCyclicCarry
    K M p hmu chi psi q g hg hcard hcoord alpha a halpha hpow ha

end ClassFieldTower.Martinet.Shafarevich
