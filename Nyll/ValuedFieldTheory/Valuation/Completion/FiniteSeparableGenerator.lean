/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Valuation.Completion.SeparableGeneratorDescent
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.RingTheory.PowerBasis

/-!
# Generators of finite extensions over a dense subfield

Embed a finite separable extension into an algebraic closure of its base.
The generator descended there belongs to the image of the extension, so it
pulls back to a generator of the original field with the same degree.
-/

namespace ValuationTheory.Completion

open IntermediateField

/-- A finite separable extension of a complete nonarchimedean field has a
generator separable over any dense subfield, of the same degree. -/
theorem exists_isSeparable_generator_of_denseRange
    {K A E : Type*} [Field K] [NontriviallyNormedField A] [Field E]
    [CompleteSpace A] [IsUltrametricDist A]
    [Algebra K A] [Algebra A E] [Algebra K E] [IsScalarTower K A E]
    [FiniteDimensional A E] [Algebra.IsSeparable A E]
    (hd : DenseRange (algebraMap K A)) :
    ∃ γ : E, IsSeparable K γ ∧ Algebra.adjoin A ({γ} : Set E) = ⊤ ∧
      (minpoly K γ).natDegree = Module.finrank A E := by
  let pb : PowerBasis A E := Field.powerBasisOfFiniteOfSeparable A E
  let ι : E →ₐ[A] AlgebraicClosure A := IsAlgClosed.lift
  have hαsep : IsSeparable A (ι pb.gen) :=
    (Algebra.IsSeparable.isSeparable A pb.gen).map ι ι.injective
  obtain ⟨β, hβsep, hβeq, hβdegree⟩ :=
    exists_isSeparable_adjoin_eq_of_denseRange hd (ι pb.gen) hαsep
  have hrange : A⟮ι pb.gen⟯ ≤ ι.fieldRange :=
    IntermediateField.adjoin_simple_le_iff.mpr ⟨pb.gen, rfl⟩
  have hβmem : β ∈ A⟮ι pb.gen⟯ := by
    rw [← hβeq]
    exact IntermediateField.mem_adjoin_simple_self A β
  obtain ⟨γ, hγ⟩ := AlgHom.mem_fieldRange.mp (hrange hβmem)
  have hγsep : IsSeparable K γ := by
    apply (isSeparable_map_iff (ι.restrictScalars K) ι.injective).mp
    change IsSeparable K (ι γ)
    rw [hγ]
    exact hβsep
  have hpbtop : A⟮pb.gen⟯ = ⊤ :=
    (Field.primitive_element_iff_minpoly_natDegree_eq A pb.gen).mpr
      (pb.natDegree_minpoly.trans pb.finrank.symm)
  have hγtop : A⟮γ⟯ = ⊤ := by
    apply IntermediateField.map_injective ι
    calc
      (A⟮γ⟯).map ι = A⟮ι γ⟯ := by
        rw [IntermediateField.adjoin_map, Set.image_singleton]
      _ = A⟮ι pb.gen⟯ := by rw [hγ]; exact hβeq
      _ = (A⟮pb.gen⟯).map ι := by
        rw [IntermediateField.adjoin_map, Set.image_singleton]
      _ = (⊤ : IntermediateField A E).map ι := congrArg (IntermediateField.map ι) hpbtop
  have hgen : Algebra.adjoin A ({γ} : Set E) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra (F := A) ({γ} : Set E), hγtop]
    rfl
  refine ⟨γ, hγsep, hgen, ?_⟩
  calc
    (minpoly K γ).natDegree = (minpoly K (ι γ)).natDegree := by
      change (minpoly K γ).natDegree =
        (minpoly K ((ι.restrictScalars K) γ)).natDegree
      rw [minpoly.algHom_eq (ι.restrictScalars K) ι.injective]
    _ = (minpoly K β).natDegree := congrArg (fun x => (minpoly K x).natDegree) hγ
    _ = (minpoly A (ι pb.gen)).natDegree := hβdegree
    _ = (minpoly A pb.gen).natDegree := by rw [minpoly.algHom_eq ι ι.injective]
    _ = Module.finrank A E := pb.natDegree_minpoly.trans pb.finrank.symm

end ValuationTheory.Completion
