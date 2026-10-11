/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Nyll.SchemeTheory.Normalization.Products.LocalRingFactor

/-!
# Generic primes below a selected DVR product factor

In a product of local rings, fix the maximal prime selected by one coordinate.
If that coordinate is a DVR, the only strictly smaller prime is the kernel of
coordinate evaluation.  This identifies a selected generic component with the
generic point of the specified DVR factor.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uι uA

variable {ι : Type uι} (A : ι → Type uA)
variable [∀ j, CommRing (A j)] [∀ j, IsDomain (A j)]
variable [∀ j, IsDiscreteValuationRing (A j)]

/-- A prime strictly below the maximal prime selected by a DVR coordinate is
exactly the kernel of coordinate evaluation. -/
theorem prime_eq_ker_coordinateEval_of_le_of_ne
    (i : ι) (N : Ideal (∀ j, A j)) [N.IsPrime]
    (hNP : N ≤ productCoordinatePrime A i)
    (hNne : N ≠ productCoordinatePrime A i) :
    N = RingHom.ker (Pi.evalRingHom A i) := by
  classical
  let f := Pi.evalRingHom A i
  let e : ∀ j, A j := Pi.single i 1
  have heP : e ∉ productCoordinatePrime A i := by
    rw [mem_productCoordinatePrime]
    simp [e]
  have heN : e ∉ N := fun he ↦ heP (hNP he)
  have heMul : e * (1 - e) = 0 := by
    ext j
    by_cases hij : i = j
    · subst j
      simp [e]
    · simp [e, hij]
  have honeSub : 1 - e ∈ N :=
    ((inferInstance : N.IsPrime).mem_or_mem_of_mul_eq_zero heMul).resolve_left heN
  have hker : RingHom.ker f ≤ N := by
    rw [show RingHom.ker f =
        Ideal.span ({1 - Pi.single i 1} : Set (∀ j, A j)) by
      exact ker_productCoordinateEval A i]
    apply Ideal.span_le.2
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact honeSub
  let q := N.map f
  have hqprime : q.IsPrime :=
    Ideal.map_isPrime_of_surjective f.surjective hker
  have hcomap : q.comap f = N := by
    dsimp only [q]
    rw [Ideal.comap_map_of_surjective f f.surjective]
    apply sup_eq_left.mpr
    change RingHom.ker f ≤ N
    exact hker
  by_cases hqzero : q = ⊥
  · calc
      N = q.comap f := hcomap.symm
      _ = (⊥ : Ideal (A i)).comap f := by rw [hqzero]
      _ = RingHom.ker f := rfl
  · have hqmax : q.IsMaximal := hqprime.isMaximal hqzero
    have hqeq : q = IsLocalRing.maximalIdeal (A i) :=
      IsLocalRing.eq_maximalIdeal hqmax
    exfalso
    apply hNne
    calc
      N = q.comap f := hcomap.symm
      _ = (IsLocalRing.maximalIdeal (A i)).comap f := by rw [hqeq]
      _ = productCoordinatePrime A i := rfl

end EtaleFundamentalGroups

end
