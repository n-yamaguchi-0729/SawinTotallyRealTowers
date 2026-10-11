/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteContinuousCharacterAction
import Nyll.ProCGroups.ProP.ContinuousH1
import Mathlib.Algebra.Ring.Aut

/-!
# The canonical action on continuous degree-one classes

The character action with trivial coefficients gives the additive action on H¹.
Restriction along relative Galois automorphisms gives the action for an extension.
-/

namespace KummerTheory

open ClassFieldTower.ProP

variable {K : Type*} [Field K] (n : ℕ)

local instance discreteZModTopology : TopologicalSpace (ZMod n) := ⊥
local instance discreteZMod : DiscreteTopology (ZMod n) := discreteTopology_bot _

/-- Pullback of continuous degree-one classes by inverse Galois conjugation. -/
noncomputable def absoluteH1Transform (τ : RingAut K)
    (c : ContinuousH1ZMod (p := n) (G := Field.absoluteGaloisGroup K)) :
    ContinuousH1ZMod (p := n) (G := Field.absoluteGaloisGroup K) :=
  h1OfCharacter (absoluteContinuousCharacterTransform τ (characterOfH1 c))

/-- Evaluation of the degree-one transform on an absolute Galois element. -/
theorem absoluteH1Transform_apply (τ : RingAut K)
    (c : ContinuousH1ZMod (p := n) (G := Field.absoluteGaloisGroup K))
    (σ : Gal(AlgebraicClosure K/K)) :
    absoluteH1Transform n τ c (Additive.ofMul (σ : Field.absoluteGaloisGroup K)) =
      c (Additive.ofMul
        (absoluteGaloisConjugate τ.symm σ : Field.absoluteGaloisGroup K)) := by
  rfl

/-- The identity automorphism fixes every continuous degree-one class. -/
theorem absoluteH1Transform_one
    (c : ContinuousH1ZMod (p := n) (G := Field.absoluteGaloisGroup K)) :
    absoluteH1Transform n 1 c = c := by
  unfold absoluteH1Transform
  rw [absoluteContinuousCharacterTransform_one]
  exact (h1CharacterEquiv (p := n) (G := Field.absoluteGaloisGroup K)).left_inv c

/-- Degree-one transforms satisfy the left action law. -/
theorem absoluteH1Transform_mul (τ υ : RingAut K)
    (c : ContinuousH1ZMod (p := n) (G := Field.absoluteGaloisGroup K)) :
    absoluteH1Transform n (τ * υ) c =
      absoluteH1Transform n τ (absoluteH1Transform n υ c) := by
  unfold absoluteH1Transform
  change h1OfCharacter (absoluteContinuousCharacterTransform (τ * υ) (characterOfH1 c)) =
    h1OfCharacter (absoluteContinuousCharacterTransform τ
      (absoluteContinuousCharacterTransform υ (characterOfH1 c)))
  rw [absoluteContinuousCharacterTransform_mul]

/-- Automorphisms of the field act additively on its continuous degree-one classes. -/
noncomputable def absoluteH1Action :
    RingAut K →* Multiplicative
      (AddAut (ContinuousH1ZMod (p := n) (G := Field.absoluteGaloisGroup K))) where
  toFun τ :=
    Multiplicative.ofAdd
      { toFun := absoluteH1Transform n τ
        invFun := absoluteH1Transform n τ⁻¹
        left_inv c := by
          rw [← absoluteH1Transform_mul, inv_mul_cancel, absoluteH1Transform_one]
        right_inv c := by
          rw [← absoluteH1Transform_mul, mul_inv_cancel, absoluteH1Transform_one]
        map_add' c d := by
          apply ContinuousAddMonoidHom.ext
          intro σ
          rfl }
  map_one' := by
    apply AddEquiv.ext
    intro c
    exact absoluteH1Transform_one n c
  map_mul' τ υ := by
    apply AddEquiv.ext
    intro c
    exact absoluteH1Transform_mul n τ υ c

variable (K) (L : Type*) [Field L] [Algebra K L]

/-- The relative Galois group acts on the continuous absolute H¹ of the extension. -/
noncomputable def relativeGaloisH1Action :
    Gal(L/K) →* Multiplicative
      (AddAut (ContinuousH1ZMod (p := n) (G := Field.absoluteGaloisGroup L))) :=
  (absoluteH1Action n).comp
    { toFun := AlgEquiv.toRingEquiv
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

/-- The relative action is pullback by inverse conjugation in the closure. -/
theorem relativeGaloisH1Action_apply (τ : Gal(L/K))
    (c : ContinuousH1ZMod (p := n) (G := Field.absoluteGaloisGroup L))
    (σ : Gal(AlgebraicClosure L/L)) :
    (relativeGaloisH1Action (n := n) K L τ).toAdd c
        (Additive.ofMul (σ : Field.absoluteGaloisGroup L)) =
      c (Additive.ofMul
        (absoluteGaloisConjugate τ.toRingEquiv.symm σ : Field.absoluteGaloisGroup L)) := by
  rfl

end KummerTheory
