/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisDescent
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.StandardClassComparison

/-!
# Galois descent on the standard idele-class carrier

The standard scalar inclusion has exactly the classes fixed by the actual
finite Galois action. Tensor descent is used only inside the proof through
the existing finite-level comparison.
-/

@[expose] public section

open scoped NumberField TensorProduct

noncomputable section

namespace NumberField.IdeleClassGroup

universe u v

variable (K : Type u) (L : Type v)
  [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L]

/-- A standard idele class comes from the base field exactly when all
Galois automorphisms of the finite extension fix it. -/
theorem mem_range_fieldInclusion_iff_fixed [IsGalois K L]
    (c : IdeleClassGroup (𝓞 L) L) :
    c ∈ (fieldInclusion K L).range ↔
      ∀ σ : L ≃ₐ[K] L, congr (σ.restrictScalars ℚ) c = c := by
  let e := relativeClassComparison K L
  obtain ⟨d, rfl⟩ := e.surjective c
  have hinc (a : _root_.IdeleClassGroup K) :
      fieldInclusion K L a =
        e (RelativeIdeleGroup.classInclusion K L a) :=
    fieldInclusion_relativeClassComparison K L a
  constructor
  · rintro ⟨a, ha⟩ σ
    rw [hinc] at ha
    have hd := e.injective ha
    subst d
    rw [← relativeClassComparison_conjugation]
    exact congrArg e
      ((RelativeIdeleGroup.classInclusion_range_le_galoisFixed K L) ⟨a, rfl⟩ σ)
  · intro hc
    have hd : d ∈ RelativeIdeleGroup.galoisFixedClassSubgroup K L := by
      intro σ
      apply e.injective
      rw [relativeClassComparison_conjugation]
      exact hc σ
    rw [← RelativeIdeleGroup.classInclusion_range_eq_galoisFixedClassSubgroup K L] at hd
    obtain ⟨a, ha⟩ := hd
    exact ⟨a, (hinc a).trans (congrArg e ha)⟩

end NumberField.IdeleClassGroup
