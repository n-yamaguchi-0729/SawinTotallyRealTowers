/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Kummer.Concrete.AbsoluteH1Action
import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureConjugation
import Nyll.GaloisCohomology.Kummer.Concrete.GaloisClosureCharacterConjugation
import Nyll.ProCGroups.ProP.ContinuousH1
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Instances.ZMod

/-!
# Trivial H¹ actions fix continuous characters

Triviality of the relative action on H¹ gives invariance under forward
conjugation by applying the inverse automorphism's action. The constructed
closure comparison then gives invariance under any actual semilinear lift.
-/

namespace KummerTheory

open ClassFieldTower.ProP

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- A trivial relative H¹ action fixes every continuous cyclic character
under forward absolute Galois conjugation. -/
theorem absoluteCharacter_conjugation_invariant_of_relativeH1Action_eq_one
    (τ : Gal(L/K)) (hτ : relativeGaloisH1Action (n := n) K L τ = 1)
    (f : Gal(AlgebraicClosure L/L) →ₜ* Multiplicative (ZMod n))
    (σ : Gal(AlgebraicClosure L/L)) :
    f (absoluteGaloisConjugate τ.toRingEquiv σ) = f σ := by
  have hinv : relativeGaloisH1Action (n := n) K L τ⁻¹ = 1 := by
    rw [map_inv, hτ, inv_one]
  let c : ContinuousH1ZMod (p := n) (G := Field.absoluteGaloisGroup L) :=
    h1OfCharacter f
  have hvalue := congrArg
    (fun b : Multiplicative
      (AddAut (ContinuousH1ZMod (p := n) (G := Field.absoluteGaloisGroup L))) =>
      b.toAdd c (Additive.ofMul (σ : Field.absoluteGaloisGroup L))) hinv
  rw [relativeGaloisH1Action_apply] at hvalue
  apply Multiplicative.toAdd.injective
  change (f (absoluteGaloisConjugate τ.toRingEquiv σ)).toAdd = (f σ).toAdd at hvalue
  exact hvalue

variable {Ω : Type*} [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

/-- Triviality of the relative H¹ action also fixes continuous cyclic
characters on any actual algebraic closure, for every semilinear lift. -/
theorem semilinearCharacter_invariant_of_relativeH1Action_eq_one
    (τ : Gal(L/K)) (hτ : relativeGaloisH1Action (n := n) K L τ = 1)
    (a : Ω ≃+* Ω)
    (ha : ∀ l : L, a (algebraMap L Ω l) = algebraMap L Ω (τ l))
    (ψ : Gal(Ω/L) →ₜ* Multiplicative (ZMod n)) (σ : Gal(Ω/L)) :
    ψ (semilinearGaloisConjugate τ.toRingEquiv a ha σ) = ψ σ := by
  let e : Gal(Ω/L) ≃ₜ* Gal(AlgebraicClosure L/L) := absoluteGaloisClosureEquiv L Ω
  let f : Gal(AlgebraicClosure L/L) →ₜ* Multiplicative (ZMod n) :=
    ⟨ψ.toMonoidHom.comp e.symm.toMulEquiv.toMonoidHom,
      ψ.continuous.comp e.symm.continuous⟩
  have hvalue := absoluteGaloisClosureEquiv_character_conjugation τ.toRingEquiv a ha f σ
  have hinvariant :=
    absoluteCharacter_conjugation_invariant_of_relativeH1Action_eq_one τ hτ f (e σ)
  have heq := hvalue.trans hinvariant
  change ψ (e.symm (e (semilinearGaloisConjugate τ.toRingEquiv a ha σ))) =
    ψ (e.symm (e σ)) at heq
  simpa only [ContinuousMulEquiv.symm_apply_apply] using heq

end KummerTheory
