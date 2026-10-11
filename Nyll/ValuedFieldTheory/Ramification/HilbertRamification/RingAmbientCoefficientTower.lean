/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.DVRUniformizerFactorization
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingRestrictedInertiaDVRTransition
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Uniformizer-ratio coefficients in a common field

Transports the uniformizer-ratio tower identity to a common field where the upper action fixes
the coefficient map. This removes the unit correction and gives the relation at the additive
valuation of the mapped uniformizer.
-/

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

universe u v w

/-- Push the existing literal coefficient-ratio calculation directly to a
common field. Fixing that field removes the unit correction; no intermediate
residue field or local-homomorphism instance is needed. -/
theorem uniformizerAmbientCoefficient_tower_of_ringHom
    (A : Type u) (B : Type v) (k : Type w)
    [CommRing A] [CommRing B] [IsDomain B] [Field k]
    (f : A →+* B) (s : A →+* A) (t : B →+* B)
    (iA : A →+* k) (iB : B →+* k)
    (hi : iB.comp f = iA) (hfixed : iB.comp t = iB)
    (π : A) (ρ : B) (hρ : ρ ≠ 0) (r : ℕ) (u : Bˣ)
    (hfactor : f.toFun π = ρ ^ r * u.val)
    (c : A) (d : B) (hc : π * c = s.toFun π) (hd : ρ * d = t.toFun ρ)
    (hcomm : f.comp s = t.comp f) :
    iA.toFun c = iB.toFun d ^ r := by
  have hraw := uniformizerRatioCoefficient_tower_of_ringHom A B f s t
    π ρ hρ r u hfactor c d hc hd hcomm
  have hfix : iB.toFun (t.toFun u.val) = iB.toFun u.val :=
    congrArg (fun j : B →+* k => j.toFun u.val) hfixed
  have hmapped : iB.toFun (f.toFun c) * iB.toFun u.val =
      iB.toFun d ^ r * iB.toFun u.val := by
    calc
      _ = iB.toFun (f.toFun c * u.val) := (map_mul iB (f.toFun c) u.val).symm
      _ = iB.toFun (d ^ r * t.toFun u.val) := congrArg iB.toFun hraw
      _ = iB.toFun (d ^ r) * iB.toFun (t.toFun u.val) :=
        map_mul iB (d ^ r) (t.toFun u.val)
      _ = _ := congrArg₂ (fun x y : k => x * y) (map_pow iB d r) hfix
  have hunit : iB.toFun u.val ≠ 0 := (u.isUnit.map iB).ne_zero
  have hscalar : iB.toFun (f.toFun c) = iB.toFun d ^ r :=
    mul_right_cancel₀ hunit hmapped
  exact (congrArg (fun j : A →+* k => j.toFun c) hi).symm.trans hscalar

/-- The common-field raw relation at the actual DVR order. Both the unit
factorization and the coefficient-ratio identity come from their existing
owners; only the ambient scalar calculation is performed here. -/
theorem uniformizerAmbientCoefficient_tower_addVal_of_ringHom
    (A : Type u) (B : Type v) (k : Type w)
    [CommRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Field k]
    (f : A →+* B) (hinj : Function.Injective f.toFun)
    (s : A →+* A) (t : B →+* B)
    (hcomm : f.comp s = t.comp f)
    (iA : A →+* k) (iB : B →+* k)
    (hi : iB.comp f = iA) (hfixed : iB.comp t = iB)
    (π : A) (hπ : Irreducible π) (ρ : B) (hρ : Irreducible ρ)
    (c : A) (d : B) (hc : π * c = s.toFun π) (hd : ρ * d = t.toFun ρ) :
    iA.toFun c = iB.toFun d ^
      (IsDiscreteValuationRing.addVal B (f.toFun π)).toNat := by
  obtain ⟨u, hu⟩ := mappedUniformizer_factorization_addVal A B f hinj π hπ ρ hρ
  exact uniformizerAmbientCoefficient_tower_of_ringHom A B k f s t iA iB hi hfixed
    π ρ hρ.ne_zero (IsDiscreteValuationRing.addVal B (f.toFun π)).toNat
    u hu c d hc hd hcomm

end RamificationTheory.HilbertRamification.DiscreteValuationRing
