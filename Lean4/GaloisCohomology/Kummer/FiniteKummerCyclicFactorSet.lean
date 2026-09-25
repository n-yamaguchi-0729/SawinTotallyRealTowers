/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Kummer.FiniteKummerCupCoefficientSquare
import GaloisCohomology.ProP.FiniteCyclicCarryCocycle

set_option autoImplicit false
open CategoryTheory
open ClassFieldTower.ProP

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open Cohomology

variable (K M : Type) [Field K] [Field M] [Algebra K M]
variable (p : ℕ+)

/-- The positive carry cocycle associated to the standard representatives of
the negative of a Kummer character. -/
noncomputable def negativeCharacterCarryTwoCocycle
    (psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(M / K)))
    (a : Rep.ofAlgebraAutOnUnits K M)
    (ha : ∀ sigma : Gal(M / K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma a = a) :
    groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K M) := by
  let : NeZero (p : ℕ) := ⟨p.ne_zero⟩
  refine ⟨fun xy ↦
    Cohomology.zmodCarry
      (-psi (Additive.ofMul xy.1))
      (-psi (Additive.ofMul xy.2)) • a, ?_⟩
  rw [groupCohomology.mem_cocycles₂_iff]
  intro x y z
  change
    Cohomology.zmodCarry
          (-psi (Additive.ofMul (x * y))) (-psi (Additive.ofMul z)) • a +
        Cohomology.zmodCarry
          (-psi (Additive.ofMul x)) (-psi (Additive.ofMul y)) • a =
      (Rep.ofAlgebraAutOnUnits K M).ρ x
          (Cohomology.zmodCarry
            (-psi (Additive.ofMul y)) (-psi (Additive.ofMul z)) • a) +
        Cohomology.zmodCarry
          (-psi (Additive.ofMul x)) (-psi (Additive.ofMul (y * z))) • a
  rw [map_nsmul, ha x, ← add_nsmul, ← add_nsmul]
  have hxy : psi (Additive.ofMul (x * y)) =
      psi (Additive.ofMul x) + psi (Additive.ofMul y) := by
    exact psi.map_add (Additive.ofMul x) (Additive.ofMul y)
  have hyz : psi (Additive.ofMul (y * z)) =
      psi (Additive.ofMul y) + psi (Additive.ofMul z) := by
    exact psi.map_add (Additive.ofMul y) (Additive.ofMul z)
  rw [hxy, hyz, neg_add_rev]
  rw [add_comm (-psi (Additive.ofMul y)) (-psi (Additive.ofMul x)),
    neg_add_rev]
  rw [add_comm (-psi (Additive.ofMul z)) (-psi (Additive.ofMul y))]
  exact congrArg (· • a)
    (Cohomology.zmodCarry_cocycle
      (-psi (Additive.ofMul x))
      (-psi (Additive.ofMul y))
      (-psi (Additive.ofMul z)))

@[simp]
theorem negativeCharacterCarryTwoCocycle_apply
    (psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(M / K)))
    (a : Rep.ofAlgebraAutOnUnits K M)
    (ha : ∀ sigma : Gal(M / K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma a = a)
    (sigma tau : Gal(M / K)) :
    negativeCharacterCarryTwoCocycle K M p psi a ha (sigma, tau) =
      Cohomology.zmodCarry
        (-psi (Additive.ofMul sigma))
        (-psi (Additive.ofMul tau)) • a :=
  by
    simp only [negativeCharacterCarryTwoCocycle]
    rfl

/-- The positive cyclic carry cocycle pulled back along a finite quotient. -/
noncomputable def inflatedFiniteCyclicCarryTwoCocycle
    {G : Type} [CommGroup G] [Fintype G]
    (q : Gal(M / K) →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : Rep.ofAlgebraAutOnUnits K M)
    (ha : ∀ sigma : Gal(M / K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma a = a) :
    groupCohomology.cocycles₂ (Rep.ofAlgebraAutOnUnits K M) := by
  refine ⟨fun xy ↦ Cohomology.finiteCyclicCarry g hg (q xy.1) (q xy.2) • a, ?_⟩
  rw [groupCohomology.mem_cocycles₂_iff]
  intro x y z
  change
    Cohomology.finiteCyclicCarry g hg (q (x * y)) (q z) • a +
        Cohomology.finiteCyclicCarry g hg (q x) (q y) • a =
      (Rep.ofAlgebraAutOnUnits K M).ρ x
          (Cohomology.finiteCyclicCarry g hg (q y) (q z) • a) +
        Cohomology.finiteCyclicCarry g hg (q x) (q (y * z)) • a
  rw [map_nsmul, ha x, ← add_nsmul, ← add_nsmul, map_mul, map_mul]
  exact congrArg (· • a)
    (Cohomology.finiteCyclicCarry_cocycle g hg (q x) (q y) (q z))

@[simp]
theorem inflatedFiniteCyclicCarryTwoCocycle_apply
    {G : Type} [CommGroup G] [Fintype G]
    (q : Gal(M / K) →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : Rep.ofAlgebraAutOnUnits K M)
    (ha : ∀ sigma : Gal(M / K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma a = a)
    (sigma tau : Gal(M / K)) :
    inflatedFiniteCyclicCarryTwoCocycle K M q g hg a ha (sigma, tau) =
      Cohomology.finiteCyclicCarry g hg (q sigma) (q tau) • a := by
  simp only [inflatedFiniteCyclicCarryTwoCocycle]
  rfl

/-- A quotient whose generator coordinate is the negative Kummer character
has the same pulled-back carry cocycle.  The value-coordinate formulation
avoids any transport between definitionally different `ZMod` moduli. -/
theorem negativeCharacterCarryTwoCocycle_eq_inflated
    {G : Type} [CommGroup G] [Fintype G]
    (psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(M / K)))
    (q : Gal(M / K) →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : Nat.card G = (p : ℕ))
    (hcoord : ∀ sigma : Gal(M / K),
      (Cohomology.finiteCyclicGeneratorCoordinate g hg (q sigma)).val =
        (-psi (Additive.ofMul sigma)).val)
    (a : Rep.ofAlgebraAutOnUnits K M)
    (ha : ∀ sigma : Gal(M / K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma a = a) :
    negativeCharacterCarryTwoCocycle K M p psi a ha =
      inflatedFiniteCyclicCarryTwoCocycle K M q g hg a ha := by
  apply Subtype.ext
  funext xy
  rcases xy with ⟨sigma, tau⟩
  change
    negativeCharacterCarryTwoCocycle K M p psi a ha (sigma, tau) =
      inflatedFiniteCyclicCarryTwoCocycle K M q g hg a ha (sigma, tau)
  rw [negativeCharacterCarryTwoCocycle_apply,
    inflatedFiniteCyclicCarryTwoCocycle_apply]
  congr 1
  simp only [Cohomology.finiteCyclicCarry, Cohomology.zmodCarry]
  simp only [hcard, hcoord sigma, hcoord tau]

/-- The chosen-root coefficient as an element of the representation's exact
underlying type. -/
noncomputable def finiteKummerCoefficientElement
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (z : ULift (ZMod (p : ℕ))) : Rep.ofAlgebraAutOnUnits K M :=
  (finiteKummerCoefficientRepHom K M p hmu).hom z

@[simp]
theorem finiteKummerCoefficientElement_apply
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (z : ULift (ZMod (p : ℕ))) :
    finiteKummerCoefficientElement K M p hmu z =
      finiteKummerCoefficientAddHom K M p hmu z :=
  rfl

private theorem coefficient_cup_eq_neg_coordinate_smul
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (x y : ZMod (p : ℕ)) :
    finiteKummerCoefficientElement K M p hmu (ULift.up (x * y)) =
      -((-y).val •
        finiteKummerCoefficientElement K M p hmu (ULift.up x)) := by
  let : NeZero (p : ℕ) := ⟨p.ne_zero⟩
  change
    (finiteKummerCoefficientRepHom K M p hmu).hom
        (ULift.up (x * y)) =
      -((-y).val •
        (finiteKummerCoefficientRepHom K M p hmu).hom (ULift.up x))
  rw [← map_nsmul, ← map_neg]
  apply congrArg (finiteKummerCoefficientRepHom K M p hmu).hom
  apply ULift.ext
  change x * y = -((-y).val • x)
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  ring

/-- The coefficient-changed cup factor set equals the positive carry factor
set in `H²`.  The explicit cobounding cochain is
`sigma ↦ -(-psi sigma).val • alpha`.

The action hypothesis is the Kummer equation
`sigma(alpha) = zeta^(chi sigma) * alpha`, written additively; the power
hypothesis is `alpha^p = a`. -/
theorem finiteKummerCup_H2pi_eq_negativeCharacterCarry
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(M / K)))
    (alpha a : Rep.ofAlgebraAutOnUnits K M)
    (halpha : ∀ sigma : Gal(M / K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma alpha =
        (finiteKummerCoefficientRepHom K M p hmu).hom
          (ULift.up (chi (Additive.ofMul sigma))) + alpha)
    (hpow : (p : ℕ) • alpha = a)
    (ha : ∀ sigma : Gal(M / K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma a = a) :
    groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K M)
        (finiteKummerCupCoefficientTwoCocycle K M p hmu chi psi) =
      groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K M)
        (negativeCharacterCarryTwoCocycle K M p psi a ha) := by
  rw [groupCohomology.H2π_eq_iff]
  refine ⟨fun sigma ↦
    -((-psi (Additive.ofMul sigma)).val • alpha), ?_⟩
  funext xy
  rcases xy with ⟨sigma, tau⟩
  change
    (Rep.ofAlgebraAutOnUnits K M).ρ sigma
          (-((-psi (Additive.ofMul tau)).val • alpha)) -
        (-((-psi (Additive.ofMul (sigma * tau))).val • alpha)) +
          -((-psi (Additive.ofMul sigma)).val • alpha) =
      finiteKummerCoefficientElement K M p hmu
          (ULift.up
            (chi (Additive.ofMul sigma) * psi (Additive.ofMul tau))) -
        Cohomology.zmodCarry
          (-psi (Additive.ofMul sigma))
          (-psi (Additive.ofMul tau)) • a
  rw [coefficient_cup_eq_neg_coordinate_smul K M p hmu,
    map_neg, map_nsmul, halpha, nsmul_add]
  let x := -psi (Additive.ofMul sigma)
  let y := -psi (Additive.ofMul tau)
  have hxy : -psi (Additive.ofMul (sigma * tau)) = x + y := by
    simp [x, y, add_comm]
  rw [hxy]
  have hxdef : -psi (Additive.ofMul sigma) = x := rfl
  have hydef : -psi (Additive.ofMul tau) = y := rfl
  rw [hxdef, hydef]
  change
    -(y.val • finiteKummerCoefficientElement K M p hmu
            (ULift.up (chi (Additive.ofMul sigma))) +
          y.val • alpha) -
        (-((x + y).val • alpha)) + -(x.val • alpha) =
      -(y.val • finiteKummerCoefficientElement K M p hmu
          (ULift.up (chi (Additive.ofMul sigma)))) -
        Cohomology.zmodCarry x y • a
  by_cases hcarry : (p : ℕ) ≤ x.val + y.val
  · rw [(Cohomology.zmodCarry_eq_one_iff x y).2 hcarry,
      one_nsmul, ZMod.val_add_of_le hcarry]
    rw [← hpow]
    have hsmul :
        x.val • alpha + y.val • alpha =
          (x.val + y.val - (p : ℕ)) • alpha + (p : ℕ) • alpha := by
      rw [← add_nsmul, ← add_nsmul, Nat.sub_add_cancel hcarry]
    calc
      _ = -(y.val • finiteKummerCoefficientElement K M p hmu
              (ULift.up (chi (Additive.ofMul sigma)))) +
            (-(x.val • alpha + y.val • alpha) +
              (x.val + y.val - (p : ℕ)) • alpha) := by abel
      _ = -(y.val • finiteKummerCoefficientElement K M p hmu
              (ULift.up (chi (Additive.ofMul sigma)))) +
            (-((x.val + y.val - (p : ℕ)) • alpha +
                (p : ℕ) • alpha) +
              (x.val + y.val - (p : ℕ)) • alpha) := by rw [hsmul]
      _ = _ := by abel
  · have hlt : x.val + y.val < (p : ℕ) := Nat.lt_of_not_ge hcarry
    rw [(Cohomology.zmodCarry_eq_zero_iff x y).2 hlt,
      zero_nsmul, sub_zero, ZMod.val_add_of_lt hlt]
    module

/-- Factor-set descent along a cyclic quotient.  Its only quotient-specific
input is the pointwise identification of the normalized generator coordinate
with the negative Kummer character. -/
theorem finiteKummerCup_H2pi_eq_inflatedFiniteCyclicCarry
    {G : Type} [CommGroup G] [Fintype G]
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(M / K)))
    (q : Gal(M / K) →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : Nat.card G = (p : ℕ))
    (hcoord : ∀ sigma : Gal(M / K),
      (Cohomology.finiteCyclicGeneratorCoordinate g hg (q sigma)).val =
        (-psi (Additive.ofMul sigma)).val)
    (alpha a : Rep.ofAlgebraAutOnUnits K M)
    (halpha : ∀ sigma : Gal(M / K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma alpha =
        (finiteKummerCoefficientRepHom K M p hmu).hom
          (ULift.up (chi (Additive.ofMul sigma))) + alpha)
    (hpow : (p : ℕ) • alpha = a)
    (ha : ∀ sigma : Gal(M / K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma a = a) :
    groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K M)
        (finiteKummerCupCoefficientTwoCocycle K M p hmu chi psi) =
      groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K M)
        (inflatedFiniteCyclicCarryTwoCocycle K M q g hg a ha) := by
  rw [← negativeCharacterCarryTwoCocycle_eq_inflated
    K M p psi q g hg hcard hcoord a ha]
  exact finiteKummerCup_H2pi_eq_negativeCharacterCarry
    K M p hmu chi psi alpha a halpha hpow ha

end ClassFieldTower.Martinet.Shafarevich
