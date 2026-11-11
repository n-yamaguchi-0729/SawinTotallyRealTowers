/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Kummer.FiniteKummerCupCoefficientSquare
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryCocycle
public import Nyll.GaloisCohomology.ProP.FiniteCyclicCarryPrimitive
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingEquivalence

/-!
# Cyclic factor sets for finite Kummer cup products

Constructs carry cocycles from the negative Kummer character and compares them
with cup-product classes and factor sets inflated from cyclic quotients.
-/

@[expose] public section

open CategoryTheory
open ClassFieldTower.ProP

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open Cohomology

universe u v

private theorem coefficient_cup_eq_neg_coordinate_smul
    {A : Type v} [AddCommGroup A] (N : ℕ) [NeZero N]
    (ι : ULift.{v} (ZMod N) →+ A) (x y : ZMod N) :
    ι (ULift.up (x * y)) = -((-y).val • ι (ULift.up x)) := by
  rw [← map_nsmul, ← map_neg]
  apply congrArg ι
  apply ULift.ext
  change x * y = -((-y).val • x)
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
  ring

/-- The cup correction retains any specified coefficient map. Thus
the coherent primitive-root coordinates used on an étale curve can be
used directly, without replacing them by a separately chosen primitive
root. Only the displayed actual action and root equation are used. -/
theorem cyclicCoefficientCup_correction_coboundary
    {R H : Type u} [CommRing R] [Group H] (A : Rep.{v} R H) (N : ℕ) [NeZero N]
    (ι : ULift.{v} (ZMod N) →+ A)
    (chi psi : Additive H →+ ZMod N) (alpha a : A)
    (halpha : ∀ sigma : H,
      A.ρ sigma alpha = ι (ULift.up (chi (Additive.ofMul sigma))) + alpha)
    (hpow : N • alpha = a) :
    groupCohomology.d₁₂ A (fun sigma => -((-psi (Additive.ofMul sigma)).val • alpha)) =
      (fun xy : H × H =>
        ι (ULift.up (chi (Additive.ofMul xy.1) * psi (Additive.ofMul xy.2)))) -
        (fun xy : H × H => Cohomology.zmodCarry
          (-psi (Additive.ofMul xy.1)) (-psi (Additive.ofMul xy.2)) • a) := by
  funext xy
  rcases xy with ⟨sigma, tau⟩
  change A.ρ sigma (-((-psi (Additive.ofMul tau)).val • alpha)) -
      (-((-psi (Additive.ofMul (sigma * tau))).val • alpha)) +
      -((-psi (Additive.ofMul sigma)).val • alpha) =
    ι (ULift.up (chi (Additive.ofMul sigma) * psi (Additive.ofMul tau))) -
      Cohomology.zmodCarry (-psi (Additive.ofMul sigma)) (-psi (Additive.ofMul tau)) • a
  rw [coefficient_cup_eq_neg_coordinate_smul N ι,
    map_neg, map_nsmul, halpha, nsmul_add]
  let x := -psi (Additive.ofMul sigma)
  let y := -psi (Additive.ofMul tau)
  have hxy : -psi (Additive.ofMul (sigma * tau)) = x + y := by
    change -psi (Additive.ofMul sigma + Additive.ofMul tau) =
      -psi (Additive.ofMul sigma) + -psi (Additive.ofMul tau)
    rw [map_add, neg_add_rev, add_comm]
  rw [hxy]
  have hxdef : -psi (Additive.ofMul sigma) = x := rfl
  have hydef : -psi (Additive.ofMul tau) = y := rfl
  rw [hxdef, hydef]
  change -(y.val • ι (ULift.up (chi (Additive.ofMul sigma))) + y.val • alpha) -
      (-((x + y).val • alpha)) + -(x.val • alpha) =
    -(y.val • ι (ULift.up (chi (Additive.ofMul sigma)))) - Cohomology.zmodCarry x y • a
  by_cases hcarry : N ≤ x.val + y.val
  · rw [(Cohomology.zmodCarry_eq_one_iff x y).2 hcarry,
      one_nsmul, ZMod.val_add_of_le hcarry, ← hpow]
    have hsmul : x.val • alpha + y.val • alpha =
        (x.val + y.val - N) • alpha + N • alpha := by
      rw [← add_nsmul, ← add_nsmul, Nat.sub_add_cancel hcarry]
    calc
      _ = -(y.val • ι (ULift.up (chi (Additive.ofMul sigma)))) +
          (-(x.val • alpha + y.val • alpha) + (x.val + y.val - N) • alpha) := by abel
      _ = -(y.val • ι (ULift.up (chi (Additive.ofMul sigma)))) +
          (-((x.val + y.val - N) • alpha + N • alpha) +
            (x.val + y.val - N) • alpha) := by rw [hsmul]
      _ = _ := by abel
  · have hlt : x.val + y.val < N := Nat.lt_of_not_ge hcarry
    rw [(Cohomology.zmodCarry_eq_zero_iff x y).2 hlt,
      zero_nsmul, sub_zero, ZMod.val_add_of_lt hlt, add_nsmul]
    abel

/-- The same supplied coefficient map is retained by the explicit
norm primitive, including a cyclic quotient of proper divisor order. -/
theorem cyclicCoefficientCup_normPrimitive
    {R H G : Type u} [CommRing R] [Group H] [CommGroup G] [Fintype G]
    (A : Rep.{u} R H) (N : ℕ) [NeZero N]
    (ι : ULift.{u} (ZMod N) →+ A)
    (chi psi : Additive H →+ ZMod N)
    (q : H →* G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (k : ℕ) (hk : 0 < k) (hcard : N = k * Nat.card G)
    (hcoord : ∀ sigma : H, (-psi (Additive.ofMul sigma)).val =
      k * (Cohomology.finiteCyclicGeneratorCoordinate g hg (q sigma)).val)
    (B : Rep.{u} R G) (φ : Rep.res q B ⟶ A) (b : B) (alpha a : A)
    (halpha : ∀ sigma : H,
      A.ρ sigma alpha = ι (ULift.up (chi (Additive.ofMul sigma))) + alpha)
    (hpow : N • alpha = a) (hnorm : φ.hom (B.norm.asHom.hom b) = a) :
    groupCohomology.d₁₂ A
        (fun sigma => -((-psi (Additive.ofMul sigma)).val • alpha) +
          φ.hom (Cohomology.finiteCyclicNormPrefixCochain B g hg b (q sigma))) =
      (fun xy : H × H =>
        ι (ULift.up (chi (Additive.ofMul xy.1) * psi (Additive.ofMul xy.2)))) := by
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  have hprefix : groupCohomology.d₁₂ A
      (fun sigma => φ.hom (Cohomology.finiteCyclicNormPrefixCochain B g hg b (q sigma))) =
        (fun xy : H × H => Cohomology.zmodCarry
          (-psi (Additive.ofMul xy.1)) (-psi (Additive.ofMul xy.2)) • a) := by
    funext xy
    rcases xy with ⟨sigma, tau⟩
    rw [Cohomology.finiteCyclicNormPrefixCochain_pullback_d₁₂_apply, hnorm]
    apply congrArg (fun m : ℕ => m • a)
    exact (Cohomology.zmodCarry_eq_of_scaled_values k hk hcard
      (Cohomology.finiteCyclicGeneratorCoordinate g hg (q sigma))
      (Cohomology.finiteCyclicGeneratorCoordinate g hg (q tau))
      (-psi (Additive.ofMul sigma)) (-psi (Additive.ofMul tau))
      (hcoord sigma) (hcoord tau)).symm
  change groupCohomology.d₁₂ A
    ((fun sigma => -((-psi (Additive.ofMul sigma)).val • alpha)) +
      (fun sigma => φ.hom (Cohomology.finiteCyclicNormPrefixCochain B g hg b (q sigma)))) = _
  rw [map_add, cyclicCoefficientCup_correction_coboundary A N ι chi psi alpha a
    halpha hpow, hprefix, sub_add_cancel]

/-- The norm primitive in the actual lifted-integer cochain complex.
Its coefficient map and norm-prefix cochain remain the original ones;
coefficient transport changes only the scalar owner of the differential. -/
theorem cyclicCoefficientCup_normPrimitive_lifted
    {H G : Type u} [Group H] [CommGroup G] [Fintype G]
    (A : Rep.{u} ℤ H) (N : ℕ) [NeZero N]
    (ι : ULift.{u} (ZMod N) →+ A)
    (chi psi : Additive H →+ ZMod N)
    (q : H →* G) (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (k : ℕ) (hk : 0 < k) (hcard : N = k * Nat.card G)
    (hcoord : ∀ sigma : H, (-psi (Additive.ofMul sigma)).val =
      k * (Cohomology.finiteCyclicGeneratorCoordinate g hg (q sigma)).val)
    (B : Rep.{u} ℤ G) (φ : Rep.res q B ⟶ A) (b : B) (alpha a : A)
    (halpha : ∀ sigma : H,
      A.ρ sigma alpha = ι (ULift.up (chi (Additive.ofMul sigma))) + alpha)
    (hpow : N • alpha = a) (hnorm : φ.hom (B.norm.asHom.hom b) = a) :
    groupCohomology.d₁₂
        ((Rep.coefficientRingEquivalence
          (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) H).functor.obj A)
        (fun sigma => -((-psi (Additive.ofMul sigma)).val • alpha) +
          φ.hom (Cohomology.finiteCyclicNormPrefixCochain B g hg b (q sigma))) =
      (fun xy : H × H =>
        ι (ULift.up (chi (Additive.ofMul xy.1) * psi (Additive.ofMul xy.2)))) := by
  let A' : Rep.{u} (ULift.{u} ℤ) H :=
    (Rep.coefficientRingEquivalence
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) H).functor.obj A
  let B' : Rep.{u} (ULift.{u} ℤ) G :=
    (Rep.coefficientRingEquivalence
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) G).functor.obj B
  let φ' : Rep.res q B' ⟶ A' :=
    (Rep.coefficientRingEquivalence
      (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) H).functor.map φ
  have hnorm' : φ'.hom (B'.norm.asHom.hom b) = a := by
    change φ.hom (B'.norm.asHom.hom b) = a
    exact (congrArg (fun z : B => φ.hom z)
      (Rep.coefficientRingEquivalence_obj_norm_apply
        (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) G B b)).trans hnorm
  have hp (sigma : H) :
      φ'.hom (Cohomology.finiteCyclicNormPrefixCochain B' g hg b (q sigma)) =
        φ.hom (Cohomology.finiteCyclicNormPrefixCochain B g hg b (q sigma)) := by
    change φ.hom (Cohomology.finiteCyclicNormPrefixCochain
      ((Rep.coefficientRingEquivalence
        (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ) G).functor.obj B)
          g hg b (q sigma)) = _
    rw [Cohomology.finiteCyclicNormPrefixCochain_integerLift_apply]
  have h := cyclicCoefficientCup_normPrimitive A' N ι chi psi q g hg k hk hcard hcoord
    B' φ' b alpha a halpha hpow hnorm'
  simp only [hp] at h
  exact h

variable (K M : Type) [Field K] [Field M] [Algebra K M]
variable (p : ℕ+)

/-- The positive carry cocycle associated to the standard representatives of
the negative of a Kummer character. -/
noncomputable def negativeCharacterCarryTwoCocycle
    (psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(M/K)))
    (a : Rep.ofAlgebraAutOnUnits K M)
    (ha : ∀ sigma : Gal(M/K),
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
    (psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(M/K)))
    (a : Rep.ofAlgebraAutOnUnits K M)
    (ha : ∀ sigma : Gal(M/K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma a = a)
    (sigma tau : Gal(M/K)) :
    negativeCharacterCarryTwoCocycle K M p psi a ha (sigma, tau) =
      Cohomology.zmodCarry
        (-psi (Additive.ofMul sigma))
        (-psi (Additive.ofMul tau)) • a :=
  rfl

/-- The positive cyclic carry cocycle pulled back along a finite quotient. -/
noncomputable def inflatedFiniteCyclicCarryTwoCocycle
    {G : Type} [CommGroup G] [Fintype G]
    (q : Gal(M/K) →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : Rep.ofAlgebraAutOnUnits K M)
    (ha : ∀ sigma : Gal(M/K),
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
    (q : Gal(M/K) →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (a : Rep.ofAlgebraAutOnUnits K M)
    (ha : ∀ sigma : Gal(M/K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma a = a)
    (sigma tau : Gal(M/K)) :
    inflatedFiniteCyclicCarryTwoCocycle K M q g hg a ha (sigma, tau) =
      Cohomology.finiteCyclicCarry g hg (q sigma) (q tau) • a := by
  simp only [inflatedFiniteCyclicCarryTwoCocycle]
  rfl

/-- A quotient whose generator coordinate is the negative Kummer character
has the same pulled-back carry cocycle.  The value-coordinate formulation
avoids any transport between definitionally different `ZMod` moduli. -/
theorem negativeCharacterCarryTwoCocycle_eq_inflated
    {G : Type} [CommGroup G] [Fintype G]
    (psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(M/K)))
    (q : Gal(M/K) →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : Nat.card G = (p : ℕ))
    (hcoord : ∀ sigma : Gal(M/K),
      (Cohomology.finiteCyclicGeneratorCoordinate g hg (q sigma)).val =
        (-psi (Additive.ofMul sigma)).val)
    (a : Rep.ofAlgebraAutOnUnits K M)
    (ha : ∀ sigma : Gal(M/K),
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

/-- The same carry comparison for a character of smaller order. Its
standard coordinates and coefficient exponent are scaled by the same
positive index; no full-order character hypothesis is needed. -/
theorem negativeCharacterCarryTwoCocycle_eq_inflated_of_scaled_coordinate
    {G : Type} [CommGroup G] [Fintype G]
    (psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(M/K)))
    (q : Gal(M/K) →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (k : ℕ) (hk : 0 < k) (hcard : (p : ℕ) = k * Nat.card G)
    (hcoord : ∀ sigma : Gal(M/K),
      (-psi (Additive.ofMul sigma)).val =
        k * (Cohomology.finiteCyclicGeneratorCoordinate g hg (q sigma)).val)
    (a : Rep.ofAlgebraAutOnUnits K M)
    (ha : ∀ sigma : Gal(M/K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma a = a) :
    negativeCharacterCarryTwoCocycle K M p psi a ha =
      inflatedFiniteCyclicCarryTwoCocycle K M q g hg a ha := by
  have : NeZero (p : ℕ) := ⟨p.ne_zero⟩
  have : NeZero (Nat.card G) := ⟨Nat.card_pos.ne'⟩
  apply Subtype.ext
  funext xy
  rcases xy with ⟨sigma, tau⟩
  change negativeCharacterCarryTwoCocycle K M p psi a ha (sigma, tau) =
    inflatedFiniteCyclicCarryTwoCocycle K M q g hg a ha (sigma, tau)
  rw [negativeCharacterCarryTwoCocycle_apply,
    inflatedFiniteCyclicCarryTwoCocycle_apply]
  apply congrArg (fun n : ℕ => n • a)
  exact Cohomology.zmodCarry_eq_of_scaled_values k hk hcard
    (Cohomology.finiteCyclicGeneratorCoordinate g hg (q sigma))
    (Cohomology.finiteCyclicGeneratorCoordinate g hg (q tau))
    (-psi (Additive.ofMul sigma)) (-psi (Additive.ofMul tau))
    (hcoord sigma) (hcoord tau)

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

/-- The original chosen-root cup correction is the supplied-coefficient
calculation specialized to its existing original coefficient map. -/
theorem finiteKummerCupCoefficient_correction_coboundary
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(M/K)))
    (alpha a : Rep.ofAlgebraAutOnUnits K M)
    (halpha : ∀ sigma : Gal(M/K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma alpha =
        (finiteKummerCoefficientRepHom K M p hmu).hom
          (ULift.up (chi (Additive.ofMul sigma))) + alpha)
    (hpow : (p : ℕ) • alpha = a)
    (ha : ∀ sigma : Gal(M/K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma a = a) :
    groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits K M)
        (fun sigma ↦ -((-psi (Additive.ofMul sigma)).val • alpha)) =
      (finiteKummerCupCoefficientTwoCocycle K M p hmu chi psi).val -
        (negativeCharacterCarryTwoCocycle K M p psi a ha).val := by
  have : NeZero (p : ℕ) := ⟨p.ne_zero⟩
  exact cyclicCoefficientCup_correction_coboundary
    (Rep.ofAlgebraAutOnUnits K M) (p : ℕ)
    (finiteKummerCoefficientAddHom K M p hmu)
    chi.toAddMonoidHom psi.toAddMonoidHom alpha a halpha hpow

/-- The actual Kummer correction plus the actual norm-prefix cochain
is a primitive of the original coefficient-changed cup. The scaling
index allows the cyclic quotient to have smaller order than the
original coefficient exponent. -/
theorem finiteKummerCupCoefficient_normPrimitive
    {G : Type} [CommGroup G] [Fintype G]
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(M/K)))
    (q : Gal(M/K) →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (k : ℕ) (hk : 0 < k) (hcard : (p : ℕ) = k * Nat.card G)
    (hcoord : ∀ sigma : Gal(M/K),
      (-psi (Additive.ofMul sigma)).val =
        k * (Cohomology.finiteCyclicGeneratorCoordinate g hg (q sigma)).val)
    (B : Rep ℤ G) (φ : Rep.res q B ⟶ Rep.ofAlgebraAutOnUnits K M) (b : B)
    (alpha a : Rep.ofAlgebraAutOnUnits K M)
    (halpha : ∀ sigma : Gal(M/K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma alpha =
        (finiteKummerCoefficientRepHom K M p hmu).hom
          (ULift.up (chi (Additive.ofMul sigma))) + alpha)
    (hpow : (p : ℕ) • alpha = a)
    (hnorm : φ.hom (B.norm.asHom.hom b) = a) :
    groupCohomology.d₁₂ (Rep.ofAlgebraAutOnUnits K M)
        (fun sigma => -((-psi (Additive.ofMul sigma)).val • alpha) +
          φ.hom (Cohomology.finiteCyclicNormPrefixCochain B g hg b (q sigma))) =
      (finiteKummerCupCoefficientTwoCocycle K M p hmu chi psi).val := by
  have : NeZero (p : ℕ) := ⟨p.ne_zero⟩
  exact cyclicCoefficientCup_normPrimitive
    (Rep.ofAlgebraAutOnUnits K M) (p : ℕ)
    (finiteKummerCoefficientAddHom K M p hmu)
    chi.toAddMonoidHom psi.toAddMonoidHom q g hg k hk hcard hcoord
    B φ b alpha a halpha hpow hnorm

/-- The coefficient-changed cup and positive carry have the same H²
class by the displayed original cochain correction. -/
theorem finiteKummerCup_H2pi_eq_negativeCharacterCarry
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(M/K)))
    (alpha a : Rep.ofAlgebraAutOnUnits K M)
    (halpha : ∀ sigma : Gal(M/K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma alpha =
        (finiteKummerCoefficientRepHom K M p hmu).hom
          (ULift.up (chi (Additive.ofMul sigma))) + alpha)
    (hpow : (p : ℕ) • alpha = a)
    (ha : ∀ sigma : Gal(M/K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma a = a) :
    groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K M)
        (finiteKummerCupCoefficientTwoCocycle K M p hmu chi psi) =
      groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K M)
        (negativeCharacterCarryTwoCocycle K M p psi a ha) := by
  rw [groupCohomology.H2π_eq_iff]
  exact ⟨fun sigma ↦ -((-psi (Additive.ofMul sigma)).val • alpha),
    finiteKummerCupCoefficient_correction_coboundary K M p hmu chi psi
      alpha a halpha hpow ha⟩

/-- Factor-set descent along a cyclic quotient.  Its only quotient-specific
input is the pointwise identification of the normalized generator coordinate
with the negative Kummer character. -/
theorem finiteKummerCup_H2pi_eq_inflatedFiniteCyclicCarry
    {G : Type} [CommGroup G] [Fintype G]
    (hmu : (primitiveRoots (p : ℕ) K).Nonempty)
    (chi psi : ContinuousH1ZMod (p := (p : ℕ)) (G := Gal(M/K)))
    (q : Gal(M/K) →* G)
    (g : G) (hg : ∀ x : G, x ∈ Subgroup.zpowers g)
    (hcard : Nat.card G = (p : ℕ))
    (hcoord : ∀ sigma : Gal(M/K),
      (Cohomology.finiteCyclicGeneratorCoordinate g hg (q sigma)).val =
        (-psi (Additive.ofMul sigma)).val)
    (alpha a : Rep.ofAlgebraAutOnUnits K M)
    (halpha : ∀ sigma : Gal(M/K),
      (Rep.ofAlgebraAutOnUnits K M).ρ sigma alpha =
        (finiteKummerCoefficientRepHom K M p hmu).hom
          (ULift.up (chi (Additive.ofMul sigma))) + alpha)
    (hpow : (p : ℕ) • alpha = a)
    (ha : ∀ sigma : Gal(M/K),
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
