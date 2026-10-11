/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.Int
import Nyll.SchemeTheory.Divisors.ReducedIrreducibleComponentGeometry

/-!
# Boundary components surjective over an arithmetic base

This file distinguishes surjectivity of every boundary component from the
weaker condition that every component merely dominates the base.  Over the
integer base, componentwise surjectivity supplies a point of every prime
residue characteristic on every component.  The structure morphism to
`Spec ℤ` is the canonical map to the terminal scheme.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme.EffectiveCartierDivisor

variable {X S : Scheme.{u}}

/-- Every reduced irreducible component of the divisor maps surjectively to
the base scheme.  This is stronger than `IsHorizontalOver`, which only asks
for dense image. -/
def HasSurjectiveComponentsOver
    (D : EffectiveCartierDivisor X) (structural : X ⟶ S) : Prop :=
  ∀ (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme),
    Surjective (D.1.componentToBase structural Z hZ)

/-- Componentwise surjectivity implies componentwise dominance. -/
theorem HasSurjectiveComponentsOver.isHorizontalOver
    {D : EffectiveCartierDivisor X} {structural : X ⟶ S}
    (hD : D.HasSurjectiveComponentsOver structural) :
    D.IsHorizontalOver structural := by
  intro Z hZ
  let g := D.1.componentToBase structural Z hZ
  let : Surjective g := hD Z hZ
  exact g.surjective.denseRange

/-- Componentwise surjectivity lifts a prescribed base point to a point on
the prescribed irreducible component of the divisor. -/
theorem HasSurjectiveComponentsOver.exists_point_on_component_over
    {D : EffectiveCartierDivisor X} {structural : X ⟶ S}
    (hD : D.HasSurjectiveComponentsOver structural)
    (Z : Set D.1.subscheme)
    (hZ : Z ∈ irreducibleComponents D.1.subscheme) (s : S) :
    ∃ x : D.1.subscheme,
      x ∈ Z ∧ structural (D.1.subschemeι x) = s := by
  let g := D.1.componentToBase structural Z hZ
  let : Surjective g := hD Z hZ
  obtain ⟨z, hz⟩ := g.surjective s
  let x : D.1.subscheme :=
    D.1.subscheme.reducedIrreducibleComponentι Z hZ z
  refine ⟨x, ?_, ?_⟩
  · rw [← D.1.subscheme.range_reducedIrreducibleComponentι Z hZ]
    exact ⟨z, rfl⟩
  · simpa only [g, IdealSheafData.componentToBase, Scheme.Hom.comp_apply,
      x] using hz

/-- The canonical integer-base version of componentwise surjectivity. -/
def HasSurjectiveComponentsOverIntegers
    (D : EffectiveCartierDivisor X) : Prop :=
  D.HasSurjectiveComponentsOver (specULiftZIsTerminal.from X)

/-- Integer-base componentwise surjectivity implies horizontality for the
canonical structure morphism. -/
theorem HasSurjectiveComponentsOverIntegers.isHorizontalOverIntegers
    {D : EffectiveCartierDivisor X}
    (hD : D.HasSurjectiveComponentsOverIntegers) :
    D.IsHorizontalOver (specULiftZIsTerminal.from X) :=
  HasSurjectiveComponentsOver.isHorizontalOver hD

end Scheme.EffectiveCartierDivisor

namespace Scheme

/-- The closed point `(p)` of `Spec (ULift ℤ)` attached to a rational
prime. -/
noncomputable def integerPrimePoint (p : ℕ) (hp : p.Prime) :
    Spec (CommRingCat.of (ULift.{u} ℤ)) := by
  letI : Fact p.Prime := ⟨hp⟩
  exact PrimeSpectrum.comap
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).toRingHom
    ⟨Ideal.span {(p : ℤ)}, inferInstance⟩

/-- The residue field at the integer prime point `(p)` has characteristic
`p`. -/
theorem ringChar_residueField_integerPrimePoint
    (p : ℕ) (hp : p.Prime) :
    ringChar
        ((Spec (CommRingCat.of (ULift.{u} ℤ))).residueField
          (integerPrimePoint p hp)) = p := by
  let B := Spec (CommRingCat.of (ULift.{u} ℤ))
  let q : B := integerPrimePoint p hp
  change PrimeSpectrum (ULift.{u} ℤ) at q
  let e : B.residueField q ≃+* q.asIdeal.ResidueField :=
    (Spec.residueFieldIso
      (CommRingCat.of (ULift.{u} ℤ)) q).commRingCatIsoToRingEquiv
  let : Algebra (B.residueField q) q.asIdeal.ResidueField :=
    e.toRingHom.toAlgebra
  rw [Algebra.ringChar_eq (B.residueField q) q.asIdeal.ResidueField]
  apply CharP.ringChar_of_prime_eq_zero hp
  have hp_mem : (p : ULift.{u} ℤ) ∈ q.asIdeal := by
    simp [q, integerPrimePoint]
  simpa only [map_natCast] using
    (Ideal.algebraMap_residueField_eq_zero.mpr hp_mem)

end Scheme

namespace Scheme.EffectiveCartierDivisor

variable {X : Scheme.{u}}

/-- If every component is surjective over the canonical integer base, then
every component contains a normal-crossings point of each rational-prime
residue characteristic. -/
theorem
  HasSurjectiveComponentsOverIntegers.hasNormalCrossingPointOfResidueCharacteristicOnEachComponent
    {D : EffectiveCartierDivisor X}
    (hD : D.HasSurjectiveComponentsOverIntegers)
    (hNC : D.IsNormalCrossings) (p : ℕ) (hp : p.Prime) :
    D.HasNormalCrossingPointOfResidueCharacteristicOnEachComponent p := by
  intro Z hZ
  let B := Spec (CommRingCat.of (ULift.{u} ℤ))
  let s : B := Scheme.integerPrimePoint p hp
  obtain ⟨x, hxZ, hx⟩ :=
    HasSurjectiveComponentsOver.exists_point_on_component_over
      hD Z hZ s
  refine ⟨x, hxZ, ?_, ?_⟩
  · let : Algebra
        (B.residueField
          ((specULiftZIsTerminal.from X) (D.1.subschemeι x)))
        (X.residueField (D.1.subschemeι x)) :=
      ((specULiftZIsTerminal.from X).residueFieldMap
        (D.1.subschemeι x)).hom.toAlgebra
    calc
      ringChar (X.residueField (D.1.subschemeι x)) =
          ringChar (B.residueField
            ((specULiftZIsTerminal.from X) (D.1.subschemeι x))) :=
        (Algebra.ringChar_eq
          (B.residueField
            ((specULiftZIsTerminal.from X) (D.1.subschemeι x)))
          (X.residueField (D.1.subschemeι x))).symm
      _ = ringChar (B.residueField s) := by rw [hx]
      _ = p := Scheme.ringChar_residueField_integerPrimePoint p hp
  · apply hNC
    exact x.property

end Scheme.EffectiveCartierDivisor

end AlgebraicGeometry

end
