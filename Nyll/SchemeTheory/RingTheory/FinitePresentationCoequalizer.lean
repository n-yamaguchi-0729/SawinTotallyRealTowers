/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Quotient.Operations


/-!
# Finite coequalization over an algebra

Two maps from a finitely generated algebra into a finite, finitely presented
stage which agree in the target can be coequalized by an actual finite,
finitely presented quotient of that stage. Its defining ideal is generated
by the differences on a finite set of algebra generators.

This supplies the parallel-arrow construction for the intended filtered
diagram of finite, finitely presented models. It does not assume or assert
that diagram's smallness or colimit comparison.
-/

noncomputable section

universe u v w

namespace AlgHom

/-- Parallel maps into a finite, finitely presented stage that agree over
`B` become equal in an actual finite, finitely presented quotient over `B`.
The quotient remains in the original stage's universe. -/
theorem exists_finitePresentation_coequalizer
    (R : Type u) [CommRing R] (A : Type w) [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (C : Type u) [CommRing C] [Algebra R C]
    [Module.Finite R C] [Algebra.FinitePresentation R C]
    (B : Type v) [CommRing B] [Algebra R B]
    (f g : A →ₐ[R] C) (φ : C →ₐ[R] B) (hφ : φ.comp f = φ.comp g) :
    ∃ Q : CommAlgCat.{u} R, Module.Finite R Q ∧ Algebra.FinitePresentation R Q ∧
      ∃ (q : C →ₐ[R] Q) (ψ : Q →ₐ[R] B),
        Function.Surjective q ∧ ψ.comp q = φ ∧ q.comp f = q.comp g := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := A)
  let I : Ideal C := Ideal.span ((fun a : A => f a - g a) '' (s : Set A))
  have hIfg : I.FG := Submodule.fg_span (s.finite_toSet.image (fun a : A => f a - g a))
  have hIker : I ≤ RingHom.ker φ.toRingHom := by
    rw [Ideal.span_le]
    rintro _ ⟨a, _, rfl⟩
    change φ (f a - g a) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr (congrArg (fun k : A →ₐ[R] B => k a) hφ)
  have hzero (c : C) (hc : c ∈ I) : φ c = 0 := hIker hc
  let q : C →ₐ[R] C ⧸ I := Ideal.Quotient.mkₐ R I
  let ψ : C ⧸ I →ₐ[R] B := Ideal.Quotient.liftₐ I φ hzero
  have hq : Function.Surjective q := Ideal.Quotient.mkₐ_surjective R I
  have : Module.Finite R (C ⧸ I) := Module.Finite.of_surjective q.toLinearMap hq
  have : Algebra.FinitePresentation R (C ⧸ I) := Algebra.FinitePresentation.quotient hIfg
  refine ⟨CommAlgCat.of R (C ⧸ I), inferInstance, inferInstance, q, ψ, hq,
    Ideal.Quotient.liftₐ_comp I φ hzero, ?_⟩
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro a ha
  change Ideal.Quotient.mk I (f a) = Ideal.Quotient.mk I (g a)
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem (R := C) (I := I) (f a) (g a)).mpr
  exact Ideal.subset_span ⟨a, ha, rfl⟩

end AlgHom
