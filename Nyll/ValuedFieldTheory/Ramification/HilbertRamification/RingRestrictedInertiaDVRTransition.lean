/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Ideal.Defs
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RingInertiaCharacter
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.DVRUniformizerFactorization
import Mathlib.Tactic.Ring

/-!
# Uniformizer-ratio identities across DVR maps

Proves ratio and residue-coefficient identities for compatible ring maps and group actions
across a DVR tower. The exponents are identified with the additive valuation and ramification
index of a mapped uniformizer.
-/

noncomputable section

namespace RamificationTheory.HilbertRamification.DiscreteValuationRing

open IsLocalRing

universe u v w z

/-- The coefficient calculation depends only on the two actual ring maps and
their ratio equations. Group actions are not data of this calculation. -/
theorem uniformizerRatioCoefficient_tower_of_ringHom
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsDomain B]
    (f : A →+* B) (s : A →+* A) (t : B →+* B)
    (π : A) (ρ : B) (hρ : ρ ≠ 0) (r : ℕ) (u : Bˣ)
    (hfactor : f π = ρ ^ r * (u : B)) (c : A) (d : B)
    (hc : π * c = s π) (hd : ρ * d = t ρ)
    (hcomm : f.comp s = t.comp f) :
    f c * (u : B) = d ^ r * t (u : B) := by
  apply mul_left_cancel₀ (pow_ne_zero r hρ)
  calc
    _ = f π * f c := by rw [hfactor]; ring
    _ = f (s π) := by rw [← map_mul, hc]
    _ = t (f π) := RingHom.congr_fun hcomm π
    _ = (t ρ) ^ r * t (u : B) := by rw [hfactor, map_mul, map_pow]
    _ = _ := by rw [← hd, mul_pow]; ring

/-- Residue fixing of the upper coefficient map removes the unit correction
from the same ring-map ratio calculation. -/
theorem uniformizerResidueCoefficient_tower_of_ringHom
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [IsDomain B]
    [IsLocalRing B]
    (f : A →+* B) (s : A →+* A) (t : B →+* B)
    (π : A) (ρ : B) (hρ : ρ ≠ 0) (r : ℕ) (u : Bˣ)
    (hfactor : f π = ρ ^ r * (u : B)) (c : A) (d : B)
    (hc : π * c = s π) (hd : ρ * d = t ρ)
    (hcomm : f.comp s = t.comp f)
    (hfixed : (residue B).comp t = residue B) :
    residue B (f c) = residue B d ^ r := by
  have hu : residue B (t (u : B)) = residue B (u : B) :=
    RingHom.congr_fun hfixed (u : B)
  have hres := congrArg (residue B)
    (uniformizerRatioCoefficient_tower_of_ringHom A B f s t
      π ρ hρ r u hfactor c d hc hd hcomm)
  rw [map_mul, map_mul, map_pow, hu] at hres
  exact mul_right_cancel₀ (u.isUnit.map (residue B)).ne_zero hres

variable (A : Type u) (B : Type v)
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable (G : Type w) (H : Type z) [Group G] [Group H]
variable [MulSemiringAction H A] [MulSemiringAction G B]

/-- The coefficient ratio calculation for two actual compatible automorphisms.
Only the lower group acts on the lower DVR; no pulled-back action is installed. -/
theorem uniformizerRatioCoefficient_tower_of_compatible
    (f : A →+* B) (π : A) (hπ : Irreducible π) (ρ : B) (hρ : Irreducible ρ)
    (r : ℕ) (u : Bˣ) (hfactor : f π = ρ ^ r * (u : B))
    (g : G) (h : H) (hcomm : ∀ x : A, f (h • x) = g • f x) :
    f (uniformizerRatioUnit A H π hπ h : A) * (u : B) =
      (uniformizerRatioUnit B G ρ hρ g : B) ^ r * (g • (u : B)) := by
  exact uniformizerRatioCoefficient_tower_of_ringHom A B f
    (MulSemiringAction.toRingHom H A h) (MulSemiringAction.toRingHom G B g)
    π ρ hρ.ne_zero r u hfactor
    (uniformizerRatioUnit A H π hπ h : A) (uniformizerRatioUnit B G ρ hρ g : B)
    (uniformizerRatioUnit_spec A H π hπ h)
    (uniformizerRatioUnit_spec B G ρ hρ g) (RingHom.ext hcomm)

/-- Upper ideal inertia removes the constructed unit correction. The result
is in the upper residue field, so it requires no lower residue structure. -/
theorem uniformizerResidueCoefficient_tower_of_compatible
    (f : A →+* B) (π : A) (hπ : Irreducible π) (ρ : B) (hρ : Irreducible ρ)
    (r : ℕ) (u : Bˣ) (hfactor : f π = ρ ^ r * (u : B))
    (g : G) (h : H) (hcomm : ∀ x : A, f (h • x) = g • f x)
    (hg : g ∈ (maximalIdeal B).inertia G) :
    residue B (f (uniformizerRatioUnit A H π hπ h : A)) =
      residue B (uniformizerRatioUnit B G ρ hρ g : B) ^ r := by
  apply uniformizerResidueCoefficient_tower_of_ringHom A B f
    (MulSemiringAction.toRingHom H A h) (MulSemiringAction.toRingHom G B g)
    π ρ hρ.ne_zero r u hfactor
    (uniformizerRatioUnit A H π hπ h : A) (uniformizerRatioUnit B G ρ hρ g : B)
    (uniformizerRatioUnit_spec A H π hπ h)
    (uniformizerRatioUnit_spec B G ρ hρ g) (RingHom.ext hcomm)
  apply RingHom.ext
  intro x
  exact inertia_residue_fixed B G ⟨g, hg⟩ x

/-- An injective coefficient map and an actual compatible group restriction
produce the raw residue-character relation at the native DVR order. -/
theorem uniformizerResidueCoefficient_tower_addVal_of_actionHom
    (f : A →+* B) (hinj : Function.Injective f)
    (φ : G →* H) (hcomm : ∀ (g : G) (x : A), f ((φ g) • x) = g • f x)
    (π : A) (hπ : Irreducible π) (ρ : B) (hρ : Irreducible ρ)
    (g : G) (hg : g ∈ (maximalIdeal B).inertia G) :
    residue B (f (uniformizerRatioUnit A H π hπ (φ g) : A)) =
      residue B (uniformizerRatioUnit B G ρ hρ g : B) ^
        (IsDiscreteValuationRing.addVal B (f π)).toNat := by
  obtain ⟨u, hu⟩ := mappedUniformizer_factorization_addVal A B f hinj π hπ ρ hρ
  exact uniformizerResidueCoefficient_tower_of_compatible A B G H
    f π hπ ρ hρ (IsDiscreteValuationRing.addVal B (f π)).toNat u hu
    g (φ g) (hcomm g) hg

/-- The same actual different-group relation at the actual local ramification
index, with the entire unit factor supplied by the native DVR owner. -/
theorem uniformizerResidueCoefficient_tower_ramificationIdx_of_actionHom
    [Algebra A B] [(maximalIdeal B).LiesOver (maximalIdeal A)]
    (hinj : Function.Injective (algebraMap A B))
    (φ : G →* H)
    (hcomm : ∀ (g : G) (x : A), algebraMap A B ((φ g) • x) = g • algebraMap A B x)
    (π : A) (hπ : Irreducible π) (ρ : B) (hρ : Irreducible ρ)
    (g : G) (hg : g ∈ (maximalIdeal B).inertia G) :
    residue B (algebraMap A B (uniformizerRatioUnit A H π hπ (φ g) : A)) =
      residue B (uniformizerRatioUnit B G ρ hρ g : B) ^
        (maximalIdeal B).ramificationIdx A := by
  obtain ⟨u, hu⟩ := mappedUniformizer_factorization_ramificationIdx A B hinj π hπ ρ hρ
  exact uniformizerResidueCoefficient_tower_of_compatible A B G H
    (algebraMap A B) π hπ ρ hρ ((maximalIdeal B).ramificationIdx A) u hu
    g (φ g) (hcomm g) hg

end RamificationTheory.HilbertRamification.DiscreteValuationRing

end
