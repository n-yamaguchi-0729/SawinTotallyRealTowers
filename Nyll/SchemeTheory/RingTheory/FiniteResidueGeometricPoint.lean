/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Geometric points of finite algebras over a local ring

Every maximal ideal of a finite algebra above the closed point can be
represented over the same chosen algebraic closure of the base residue field.
The resulting ring map has the given kernel and the canonical base map.
-/

noncomputable section

namespace SchemeTheory

universe u v

/-- A closed point of a finite algebra lifts to the fixed algebraic closure
of the local base's residue field, preserving the actual base map. -/
theorem exists_finite_residue_geometricPoint
    (R : Type u) [CommRing R] [IsLocalRing R]
    (B : Type v) [CommRing B] [Algebra R B] [Module.Finite R B]
    (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver (IsLocalRing.maximalIdeal R)] :
    ∃ φ : B →+* AlgebraicClosure (IsLocalRing.ResidueField R),
      RingHom.ker φ = Q ∧
      φ.comp (algebraMap R B) =
        (algebraMap (IsLocalRing.ResidueField R)
          (AlgebraicClosure (IsLocalRing.ResidueField R))).comp (IsLocalRing.residue R) := by
  let k := IsLocalRing.ResidueField R
  let Ω := AlgebraicClosure k
  let : Field (B ⧸ Q) := Ideal.Quotient.field Q
  let : Algebra k (B ⧸ Q) := Ideal.Quotient.algebraOfLiesOver Q (IsLocalRing.maximalIdeal R)
  have : IsScalarTower R k (B ⧸ Q) :=
    Ideal.Quotient.isScalarTower_of_liesOver R Q (IsLocalRing.maximalIdeal R)
  have : Module.Finite k (B ⧸ Q) := Module.Finite.of_restrictScalars_finite R k (B ⧸ Q)
  let e : (B ⧸ Q) →ₐ[k] Ω := IsAlgClosed.lift (R := k) (S := B ⧸ Q) (M := Ω)
  let φ : B →+* Ω := e.toRingHom.comp (Ideal.Quotient.mk Q)
  refine ⟨φ, ?_, ?_⟩
  · change RingHom.ker (e.toRingHom.comp (Ideal.Quotient.mk Q)) = Q
    rw [RingHom.ker_comp_of_injective _ e.injective]
    ext b
    exact Ideal.Quotient.eq_zero_iff_mem
  · apply RingHom.ext
    intro r
    change e (algebraMap B (B ⧸ Q) (algebraMap R B r)) =
      algebraMap k Ω (IsLocalRing.residue R r)
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply R k (B ⧸ Q),
      e.commutes]
    rfl

end SchemeTheory
