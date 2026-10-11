/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.TotallySplit
import Mathlib.LinearAlgebra.Pi

/-!
# Surjectivity onto a split algebra from lifts of idempotents

The coordinate idempotents of a finite split algebra form a basis. If
their preimages and the scalar coefficient preimages exist, every element
has an explicitly constructed preimage. For proper H⁰, the idempotents
are lifted by the actual proper-section lifting theorem.
-/

noncomputable section

namespace Algebra

universe u v w z

/-- Surjectivity onto a finite split algebra follows from lifting each
idempotent and lifting scalar coefficients. -/
theorem surjective_of_isFiniteSplit_of_idempotents_mem_range
    {R : Type u} {K : Type v} {A : Type w} {B : Type z}
    [CommRing R] [CommRing K] [CommRing A] [CommRing B]
    [Algebra R K] [Algebra R A] [Algebra R B] [Algebra K B]
    [IsScalarTower R K B] [IsFiniteSplit K B]
    (f : A →ₐ[R] B) (hK : Function.Surjective (algebraMap R K))
    (hIdempotents : ∀ e : B, IsIdempotentElem e → e ∈ f.range) :
    Function.Surjective f := by
  classical
  obtain ⟨n, ⟨E⟩⟩ := IsFiniteSplit.nonempty_algEquiv_fun K B
  let δ : Fin n → (Fin n → K) := fun i => Pi.single i 1
  have hSingle (i : Fin n) : IsIdempotentElem (δ i) := by
    change δ i * δ i = δ i
    ext j
    by_cases hji : j = i
    · subst j
      simp only [δ, Pi.mul_apply, Pi.single_eq_same, one_mul]
    · simp only [δ, Pi.mul_apply, Pi.single_eq_of_ne hji, zero_mul]
  have hLift (i : Fin n) : ∃ a : A, f a = E.symm (δ i) :=
    hIdempotents _ ((hSingle i).map E.symm.toRingHom)
  choose a ha using hLift
  intro b
  choose c hc using fun i : Fin n => hK (E b i)
  refine ⟨∑ i, algebraMap R A (c i) * a i, E.injective ?_⟩
  rw [map_sum, map_sum]
  have hTerm (i : Fin n) :
      E (f (algebraMap R A (c i) * a i)) = (Pi.single i (E b i) : Fin n → K) := by
    rw [map_mul, f.commutes, ha, map_mul,
      IsScalarTower.algebraMap_apply R K B, E.commutes, hc, E.apply_symm_apply]
    ext j
    change E b i * δ i j = (Pi.single i (E b i) : Fin n → K) j
    by_cases hji : j = i
    · subst j
      simp only [δ, Pi.single_eq_same, mul_one]
    · simp only [δ, Pi.single_eq_of_ne hji, mul_zero]
  simp only [hTerm]
  exact Finset.univ_sum_single (E b)

end Algebra
