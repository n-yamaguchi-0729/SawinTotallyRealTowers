/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Statement adapted from Formal Conjectures:
https://github.com/google-deepmind/formal-conjectures/blob/8323e878b83fcd7f4a448256069352a265460d75/FormalConjectures/ErdosProblems/90.lean#L193
Original statement: Copyright 2025 The Formal Conjectures Authors; Apache 2.0.
-/

import SawinTotallyRealTowers.RealProPFrobeniusFixedFieldSplitting
import SawinTotallyRealTowers.SawinDiscriminantBound
import SawinTotallyRealTowers.MaximalRealProPOutside
import SawinTotallyRealTowers.SixPrimeSupport
import ClassFieldTheory.AlgebraicNumberTheory.Galois.UnboundedDegree
import ClassFieldTheory.AlgebraicNumberTheory.NumberField.CompletelySplitFinset
import ClassFieldTheory.AlgebraicNumberTheory.NumberField.RootDiscriminantBound
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false

/-!
# Sawin's totally real tower

A single infinite set of rational primes congruent to one modulo four
splits completely in totally real number fields of unbounded degree and
uniformly bounded root discriminant. The statement matches the arithmetic
input `Erdos90.sawin_totally_real_tower` in Formal Conjectures.
-/

open scoped NumberField
open NumberField IsDedekindDomain

namespace ClassFieldTower.Sawin

open AlgebraicNumberTheory.PrimeSelection
open AlgebraicNumberTheory.DiscriminantBounds

/-- Sawin's totally real tower, with one prime set fixed before the degree bound. -/
theorem sawin_totally_real_tower :
    ∃ (rdBound : ℝ) (Q : Set ℕ), Q.Infinite ∧ (∀ q ∈ Q, q.Prime ∧ q % 4 = 1) ∧
      ∀ N : ℕ, ∃ (F : Type) (_ : Field F) (_ : CharZero F) (_ : NumberField F)
        (_ : IsTotallyReal F),
        N ≤ Module.finrank ℚ F ∧
        (|(NumberField.discr F : ℝ)|) ^ ((1 : ℝ) / Module.finrank ℚ F) ≤ rdBound ∧
        ∀ q ∈ Q, ∃ (factors : Finset (Ideal (𝓞 F))),
          factors.card = Module.finrank ℚ F ∧
          ∀ p ∈ factors, p.IsMaximal ∧ (q : 𝓞 F) ∈ p := by
  classical
  let instPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨primes, L, hGal, _, hInfinite, hL, hprimes, _, hsplit⟩ :=
    exists_sawinInfinite_totallyReal_split_field
  let Q : Set ℕ := Set.range (fun n : ℕ ↦ (primes n).val)
  have hQ : Q.Infinite :=
    Set.infinite_of_forall_exists_gt
      (fun a ↦ ⟨(primes a).val, ⟨a, rfl⟩, (hprimes a).1⟩)
  refine ⟨255255, Q, hQ, ?_, ?_⟩
  · rintro q ⟨n, rfl⟩
    exact ⟨(primes n).property, (hprimes n).2.2⟩
  · intro N
    obtain ⟨E, hE, hN⟩ :=
      @AlgebraicNumberTheory.exists_finiteGaloisIntermediateField_le_finrank_ge_of_infinite_aut
        ℚ (AlgebraicClosure ℚ) _ _ _ L hGal hInfinite N
    let instNumberFieldE : NumberField E := NumberField.of_module_finite ℚ E
    let instGalE : IsGalois ℚ E := E.isGalois
    have hAdm :=
      (isAdmissibleFiniteLayer_iff_le_maximalRealProPOutside
        2 sawinRationalPrimeSupport E).mpr (hE.trans hL)
    let instTotallyRealE : IsTotallyReal E :=
      (isUnramifiedAtInfinitePlaces_rat_iff_isTotallyReal E).mp hAdm.2.2
    have hdiscr := discr_natAbs_le_of_sawin_ramification E hAdm.1 hAdm.2.1
    have hroot := rootDiscr_le_of_natAbs_discr_le_pow E 255255 hdiscr
    refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, hN, ?_, ?_⟩
    · simpa only [NumberField.rootDiscr_def, Int.cast_abs, one_div, Nat.cast_ofNat] using hroot
    · rintro q ⟨n, rfl⟩
      exact exists_finset_maximalIdeals_of_finitePlaceSplitsCompletely
        E (primes n) (hsplit E hE n)

end ClassFieldTower.Sawin
