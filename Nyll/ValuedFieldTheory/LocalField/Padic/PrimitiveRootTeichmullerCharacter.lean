/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.Padic.Teichmuller
import Mathlib.Algebra.Algebra.Tower
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Teichmüller characters from a specified primitive root

A primitive `p`-th root in a domain defines a p-adic character of its
algebra automorphisms over any base ring. Its reduction records the actual
action on that root. Restricting scalars preserves this character because
it preserves the underlying automorphism and the specified root.

The ambient algebra need not be a cyclotomic extension. No finiteness,
normality, characteristic-zero, or prime-to-`p` group-order assumption is
required. A scalar tower is supplied once; no local instances are installed.
-/

namespace LocalFieldTheory.DiscreteValuationField

open Examples.Qp

universe u v w

section Restriction

variable (F : Type u) {M : Type v} {E : Type w}
    [CommRing F] [CommRing M] [CommRing E] [IsDomain E]
    [Algebra F M] [Algebra F E] [Algebra M E] [IsScalarTower F M E]

/-- The exponent on the same primitive root is unchanged by restriction of scalars. -/
theorem primitiveRoot_autToPow_restrictScalars
    {n : ℕ} [NeZero n] {ζ : E} (hζ : IsPrimitiveRoot ζ n) (σ : E ≃ₐ[M] E) :
    hζ.autToPow F (σ.restrictScalars F) = hζ.autToPow M σ := by
  apply Units.ext
  apply ZMod.val_injective
  apply hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _)
  rw [hζ.autToPow_spec F (σ.restrictScalars F), hζ.autToPow_spec M σ,
    AlgEquiv.restrictScalars_apply]

end Restriction

section Character

variable (F : Type u) {E : Type w}
    [CommRing F] [CommRing E] [IsDomain E] [Algebra F E]
    (p : ℕ) [Fact p.Prime] {ζ : E}

/-- The Teichmüller lift of the action on a specified primitive `p`-th root. -/
noncomputable def primitiveRootTeichmullerCharacter (hζ : IsPrimitiveRoot ζ p) :
    (E ≃ₐ[F] E) →* ℤ_[p]ˣ :=
  (teichmullerUnits p).comp (hζ.autToPow F)

/-- Reduction modulo `p` gives the actual action on the specified primitive root. -/
theorem primitiveRootTeichmullerCharacter_spec
    (hζ : IsPrimitiveRoot ζ p) (σ : E ≃ₐ[F] E) :
    ζ ^ (PadicInt.toZMod (primitiveRootTeichmullerCharacter F p hζ σ : ℤ_[p])).val =
      σ ζ := by
  have h : PadicInt.toZMod (primitiveRootTeichmullerCharacter F p hζ σ : ℤ_[p]) =
      (hζ.autToPow F σ : ZMod p) :=
    congrArg (fun a : (ZMod p)ˣ => (a : ZMod p))
      (toZMod_teichmullerUnits p (hζ.autToPow F σ))
  rw [h]
  exact hζ.autToPow_spec F σ

/-- A specified exponent for the actual root action differs from the
Teichmüller character by an actual multiple of `p` in the p-adic integers. -/
theorem exists_primitiveRootTeichmullerCharacter_sub_natCast_eq_prime_mul
    (hζ : IsPrimitiveRoot ζ p) (σ : E ≃ₐ[F] E)
    (a : ℕ) (ha : a < p) (hact : σ ζ = ζ ^ a) :
    ∃ c : ℤ_[p], (primitiveRootTeichmullerCharacter F p hζ σ : ℤ_[p]) -
      (a : ℤ_[p]) = (p : ℤ_[p]) * c := by
  have hval :
      (PadicInt.toZMod (primitiveRootTeichmullerCharacter F p hζ σ : ℤ_[p])).val = a :=
    hζ.pow_inj (ZMod.val_lt _) ha
      ((primitiveRootTeichmullerCharacter_spec F p hζ σ).trans hact)
  have hmod : PadicInt.toZMod (primitiveRootTeichmullerCharacter F p hζ σ : ℤ_[p]) =
      (a : ZMod p) := by
    rw [← hval]
    exact (ZMod.natCast_zmod_val _).symm
  have hzero : PadicInt.toZMod
      ((primitiveRootTeichmullerCharacter F p hζ σ : ℤ_[p]) - (a : ℤ_[p])) = 0 := by
    rw [map_sub, map_natCast, hmod, sub_self]
  have hdiv : (p : ℤ_[p]) ∣
      (primitiveRootTeichmullerCharacter F p hζ σ : ℤ_[p]) - (a : ℤ_[p]) := by
    rw [← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p,
      ← PadicInt.ker_toZMod, RingHom.mem_ker]
    exact hzero
  exact hdiv

end Character

/-- The actual characters agree along the inclusion of automorphisms obtained
by restricting scalars through a single scalar tower. -/
theorem primitiveRootTeichmullerCharacter_comp_restrictScalars
    (F : Type u) {M : Type v} {E : Type w}
    [CommRing F] [CommRing M] [CommRing E] [IsDomain E]
    [Algebra F M] [Algebra F E] [Algebra M E] [IsScalarTower F M E]
    (p : ℕ) [Fact p.Prime] {ζ : E} (hζ : IsPrimitiveRoot ζ p) :
    (primitiveRootTeichmullerCharacter F p hζ).comp
        (AlgEquiv.restrictScalarsHom F : (E ≃ₐ[M] E) →* (E ≃ₐ[F] E)) =
      primitiveRootTeichmullerCharacter M p hζ := by
  apply MonoidHom.ext
  intro σ
  change teichmullerUnits p (hζ.autToPow F (σ.restrictScalars F)) =
    teichmullerUnits p (hζ.autToPow M σ)
  rw [primitiveRoot_autToPow_restrictScalars F hζ σ]

end LocalFieldTheory.DiscreteValuationField
