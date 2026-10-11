/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.RamificationField

/-!
# Hilbert ramification theory: fixed-field maximality

This file records the fixed-field maximality statements behind
the inertia-field maximality theorem and the ramification-field maximality theorem.  The
valuation-theoretic
words "unramified" and "tamely ramified" still require the unramified and tame ramification API;
the purely Galois-theoretic part is already available: a subextension lies in
`Z_w`, `T_w`, or `V_w` exactly when the corresponding canonical subgroup acts
trivially on it.
-/

namespace RamificationTheory


noncomputable section

universe u v

namespace HilbertRamification
namespace ValuationSubring


variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The localization and decomposition comparison gives:
`Z_w` is the largest intermediate field of `L/K` on which `G_w` acts
trivially. -/
theorem le_decompositionField_iff
    (A : _root_.ValuationSubring L) (E : IntermediateField K L) :
    E ≤ decompositionField K A ↔
      ∀ σ : decompositionGroup K A, ∀ x : E,
        ((σ : L ≃ₐ[K] L) (x : L)) = x := by
  constructor
  · intro h σ x
    exact (mem_decompositionField_iff (K := K) A (x : L)).mp
      (h x.property) σ σ.property
  · intro h x hx
    exact (mem_decompositionField_iff (K := K) A x).mpr
      (fun σ hσ => by
        simpa using h ⟨σ, hσ⟩ ⟨x, hx⟩)

/-- The inertia field satisfies:
`T_w` is the largest intermediate field of `L/K` on which `I_w` acts
trivially. -/
theorem le_inertiaField_iff
    (A : _root_.ValuationSubring L) (E : IntermediateField K L) :
    E ≤ inertiaField K A ↔
      ∀ σ : inertiaGroup K A, ∀ x : E,
        ((σ : decompositionGroup K A) : L ≃ₐ[K] L) (x : L) = x := by
  constructor
  · intro h σ x
    exact (mem_inertiaField_iff (K := K) A (x : L)).mp (h x.property) σ
  · intro h x hx
    exact (mem_inertiaField_iff (K := K) A x).mpr
      (fun σ => by
        simpa using h σ ⟨x, hx⟩)

/-- The ramification field satisfies:
`V_w` is the largest intermediate field of `L/K` on which `R_w` acts
trivially. -/
theorem le_ramificationField_iff
    (A : _root_.ValuationSubring L) (E : IntermediateField K L) :
    E ≤ ramificationField K A ↔
      ∀ σ : ramificationGroup K A, ∀ x : E,
        (((σ : inertiaGroup K A) : decompositionGroup K A) :
          L ≃ₐ[K] L) (x : L) = x := by
  constructor
  · intro h σ x
    exact (mem_ramificationField_iff (K := K) A (x : L)).mp
      (h x.property) σ
  · intro h x hx
    exact (mem_ramificationField_iff (K := K) A x).mpr
      (fun σ => by
        simpa using h σ ⟨x, hx⟩)

/-- Inertia-field maximality:
over the decomposition field `Z_w`, `T_w` is the largest subextension of
`L/Z_w` on which `I_w` acts trivially. -/
theorem le_inertiaFieldOverDecompositionField_iff
    (A : _root_.ValuationSubring L)
    (E : IntermediateField (decompositionField K A) L) :
    E ≤ inertiaFieldOverDecompositionField K A ↔
      ∀ σ : inertiaGroup K A, ∀ x : E,
        ((σ : decompositionGroup K A) : L ≃ₐ[K] L) (x : L) = x := by
  constructor
  · intro h σ x
    exact (mem_inertiaFieldOverDecompositionField_iff
      (K := K) A (x : L)).mp (h x.property) σ
  · intro h x hx
    exact (mem_inertiaFieldOverDecompositionField_iff
      (K := K) A x).mpr
      (fun σ => by
        simpa using h σ ⟨x, hx⟩)

/-- Ramification-field maximality:
over the inertia field `T_w`, `V_w` is the largest subextension of `L/T_w`
on which `R_w` acts trivially. -/
theorem le_ramificationFieldOverInertiaField_iff
    (A : _root_.ValuationSubring L)
    (E : IntermediateField (inertiaField K A) L) :
    E ≤ ramificationFieldOverInertiaField K A ↔
      ∀ σ : ramificationGroup K A, ∀ x : E,
        (((σ : inertiaGroup K A) : decompositionGroup K A) :
          L ≃ₐ[K] L) (x : L) = x := by
  constructor
  · intro h σ x
    exact (mem_ramificationFieldOverInertiaField_iff
      (K := K) A (x : L)).mp (h x.property) σ
  · intro h x hx
    exact (mem_ramificationFieldOverInertiaField_iff
      (K := K) A x).mpr
      (fun σ => by
        simpa using h σ ⟨x, hx⟩)

/-- Ramification-field maximality:
over the decomposition field `Z_w`, `V_w` is the largest subextension of
`L/Z_w` on which `R_w` acts trivially. -/
theorem le_ramificationFieldOverDecompositionField_iff
    (A : _root_.ValuationSubring L)
    (E : IntermediateField (decompositionField K A) L) :
    E ≤ ramificationFieldOverDecompositionField K A ↔
      ∀ σ : ramificationGroup K A, ∀ x : E,
        (((σ : inertiaGroup K A) : decompositionGroup K A) :
          L ≃ₐ[K] L) (x : L) = x := by
  constructor
  · intro h σ x
    exact (mem_ramificationFieldOverDecompositionField_iff
      (K := K) A (x : L)).mp (h x.property) σ
  · intro h x hx
    exact (mem_ramificationFieldOverDecompositionField_iff
      (K := K) A x).mpr
      (fun σ => by
        simpa using h σ ⟨x, hx⟩)

end ValuationSubring
end HilbertRamification

end
end RamificationTheory
