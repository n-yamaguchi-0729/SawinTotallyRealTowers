/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.RingTheory.AlgebraicIndependent.Adjoin
import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Finiteness of algebraic constants in a finitely generated field
-/

namespace FieldTheory

universe u v w

attribute [local instance] MvPolynomial.algebraMvPolynomial FractionRing.liftAlgebra

/-- An algebraic subextension of a finitely generated field extension is finite. -/
theorem finite_algebraic_subextension
    (F : Type u) (C : Type v) (K : Type w)
    [Field F] [Field C] [Field K] [Algebra F C] [Algebra F K] [Algebra C K]
    [IsScalarTower F C K] [Algebra.IsAlgebraic F C] [Algebra.EssFiniteType F K] :
    Module.Finite F C := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis F K
  let x : s → K := Subtype.val
  have hx : AlgebraicIndependent F x := hs.1
  have hxC : AlgebraicIndependent C x := hx.extendScalars C
  let P := MvPolynomial s F
  let Q := MvPolynomial s C
  let A := FractionRing P
  let B := FractionRing Q
  let T := IntermediateField.adjoin F (Set.range x)
  have : Algebra.IsAlgebraic T K := hs.isAlgebraic_field
  have : Algebra.EssFiniteType T K := Algebra.EssFiniteType.of_comp F T K
  have : Module.Finite T K := Algebra.finite_of_essFiniteType_of_isAlgebraic
  let : Algebra P K := (MvPolynomial.aeval x : P →ₐ[F] K).toAlgebra
  let : Algebra Q K := (MvPolynomial.aeval x : Q →ₐ[C] K).toAlgebra
  have : FaithfulSMul P K :=
    (faithfulSMul_iff_algebraMap_injective P K).mpr hx
  have : FaithfulSMul Q K :=
    (faithfulSMul_iff_algebraMap_injective Q K).mpr hxC
  have : IsScalarTower P Q K := IsScalarTower.of_algebraMap_eq fun p => by
    change MvPolynomial.eval₂ (algebraMap F K) x p =
      MvPolynomial.eval₂ (algebraMap C K) x (MvPolynomial.map (algebraMap F C) p)
    rw [MvPolynomial.eval₂_map, ← IsScalarTower.algebraMap_eq]
  have : Module.Finite A K := Module.Finite.of_equiv_equiv
    hx.aevalEquivField.symm.toRingEquiv (RingEquiv.refl K) (by
      ext t
      change IsFractionRing.lift hx (hx.aevalEquivField.symm t) = (t : K)
      exact hx.lift_reprField t)
  have : Module.Finite A B :=
    Module.Finite.of_injective (IsScalarTower.toAlgHom A B K).toLinearMap
      (algebraMap B K).injective
  have hrank := Algebra.IsAlgebraic.rank_fractionRing_mvPolynomial (R := F) (S := C) s
  have hfinite : Module.rank A B < Cardinal.aleph0 := Module.rank_lt_aleph0 A B
  rw [hrank, Cardinal.lift_lt_aleph0] at hfinite
  exact Module.rank_lt_aleph0_iff.mp hfinite

/-- The relative algebraic closure of a finite base field in a finitely
generated extension is a finite field. -/
theorem finite_algebraicClosure_of_finite_base
    (F : Type u) (K : Type v) [Field F] [Field K] [Algebra F K]
    [Finite F] [Algebra.EssFiniteType F K] :
    Finite (algebraicClosure F K) := by
  have : Module.Finite F (algebraicClosure F K) :=
    finite_algebraic_subextension F (algebraicClosure F K) K
  exact Finite.of_injective (Module.finBasis F (algebraicClosure F K)).equivFun
    (Module.finBasis F (algebraicClosure F K)).equivFun.injective

end FieldTheory
