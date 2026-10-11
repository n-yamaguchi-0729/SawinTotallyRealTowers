/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.GroupTheory.Torsion

/-!
# Transport of finite primary roots along field embeddings

Primary roots embed through the actual map on units. A finite extension embedded
in a chosen overfield is identified with its actual intermediate field range.
-/

namespace KummerTheory
universe u v w

/-- Primary roots of a subfield inject into those of the ambient field. -/
theorem finite_primaryComponent_of_fieldEmbedding
    {E : Type u} {F : Type v} [Field E] [Field F] (f : E →+* F)
    (p : ℕ) [Finite (CommGroup.primaryComponent Fˣ p)] :
    Finite (CommGroup.primaryComponent Eˣ p) := by
  let i : CommGroup.primaryComponent Eˣ p → CommGroup.primaryComponent Fˣ p :=
    fun z => ⟨Units.map f.toMonoidHom z, by
      obtain ⟨n, hn⟩ := CommGroup.mem_primaryComponent.mp z.property
      apply CommGroup.mem_primaryComponent.mpr
      refine ⟨n, ?_⟩
      simpa only [map_pow, map_one] using congrArg (Units.map f.toMonoidHom) hn⟩
  apply Finite.of_injective i
  intro a b hab
  apply Subtype.ext
  apply Units.ext
  apply f.injective
  exact congrArg (fun z : CommGroup.primaryComponent Fˣ p => ((z : Fˣ) : F)) hab

/-- Root finiteness on finite intermediate fields applies to any embedded finite extension. -/
theorem finite_primaryComponent_of_finiteExtension_embedding
    {K : Type u} {E : Type v} {Ω : Type w}
    [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra K Ω]
    [FiniteDimensional K E] (f : E →ₐ[K] Ω) (p : ℕ)
    (hRoots : ∀ L : IntermediateField K Ω, FiniteDimensional K L →
      Finite (CommGroup.primaryComponent Lˣ p)) :
    Finite (CommGroup.primaryComponent Eˣ p) := by
  have hF : FiniteDimensional K f.fieldRange :=
    Module.Finite.equiv f.equivFieldRange.toLinearEquiv
  have : Finite (CommGroup.primaryComponent f.fieldRangeˣ p) := hRoots f.fieldRange hF
  exact finite_primaryComponent_of_fieldEmbedding f.equivFieldRange.toRingHom p

end KummerTheory
