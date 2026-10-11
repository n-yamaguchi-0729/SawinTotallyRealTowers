/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.NumberTheory.Cyclotomic.Basic

/-!
# Commuting automorphisms in a cyclotomic compositum

An automorphism fixing the lower cyclotomic field commutes with an
automorphism fixing the other normal field. A primitive root in the lower
field generates the upper cyclotomic extension, so their commutation on
the two fields determines their commutation everywhere.
-/

namespace ValuationTheory.DiscreteValuationField

variable (F K L E : Type*) [Field F] [Field K] [Field L] [Field E]
  [Algebra F K] [Algebra F L] [Algebra F E] [Algebra K E] [Algebra L E]
  [IsScalarTower F K E] [IsScalarTower F L E] [Normal F K]

/-- The two relative automorphism groups commute in the actual cyclotomic
compositum; its generation is supplied by a primitive root in `L`. -/
theorem cyclotomic_compositum_aut_commute
    (n : ℕ) [NeZero n]
    [IsCyclotomicExtension {n} F L] [IsCyclotomicExtension {n} K E]
    (τ : E ≃ₐ[L] E) (δ : E ≃ₐ[K] E) :
    Commute τ.toRingEquiv δ.toRingEquiv := by
  have : Normal F L := (IsCyclotomicExtension.isGalois {n} F L).to_normal
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot F L
    (Set.mem_singleton n) (NeZero.ne n)
  have hζE : IsPrimitiveRoot (algebraMap L E ζ) n :=
    hζ.map_of_injective (algebraMap L E).injective
  have hgen : Algebra.adjoin K ({algebraMap L E ζ} : Set E) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top hζE
  apply RingEquiv.ext
  intro x
  change τ (δ x) = δ (τ x)
  have hx : x ∈ Algebra.adjoin K ({algebraMap L E ζ} : Set E) := by
    rw [hgen]
    trivial
  refine Algebra.adjoin_induction (p := fun y _hy => τ (δ y) = δ (τ y))
    ?_ ?_ ?_ ?_ hx
  · intro y hy
    have hyζ : y = algebraMap L E ζ := Set.mem_singleton_iff.mp hy
    subst y
    have hδL : algebraMap L E ((δ.restrictScalars F).restrictNormal L ζ) =
        δ (algebraMap L E ζ) :=
      (δ.restrictScalars F).restrictNormal_commutes L ζ
    rw [τ.commutes, ← hδL, τ.commutes]
  · intro k
    have hτK : algebraMap K E ((τ.restrictScalars F).restrictNormal K k) =
        τ (algebraMap K E k) :=
      (τ.restrictScalars F).restrictNormal_commutes K k
    rw [δ.commutes, ← hτK, δ.commutes]
  · intro y z _hy _hz hy hz
    simp only [map_add, hy, hz]
  · intro y z _hy _hz hy hz
    simp only [map_mul, hy, hz]

end ValuationTheory.DiscreteValuationField
