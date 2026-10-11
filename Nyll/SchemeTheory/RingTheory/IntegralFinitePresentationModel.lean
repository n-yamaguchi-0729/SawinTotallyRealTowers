/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Insert
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs


/-!
# Finite, finitely presented models for finite sets of integral elements

Each finite subset of an integral algebra is contained in the image of an
actual finite, finitely presented algebra over the original base. The model
is constructed by successively adjoining roots of the elements' monic
polynomials. No Noetherian hypothesis on the base is needed.

This is a ring-local precursor to the finite-presentation refinement in
Stacks Project, Tag 09Z0. A filtered diagram, its colimit comparison, and a
global relative-Spec approximation are separate constructions.
-/

noncomputable section

universe u v

namespace Algebra.IsIntegral

/-- A finite set in an integral algebra lifts to an actual finite, finitely
presented algebra. The source model lies in the universe of the base ring,
even when the target algebra lies in a different universe. -/
theorem exists_finitePresentation_range_finset
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    [Algebra.IsIntegral R B] (s : Finset B) :
    ∃ A : CommAlgCat.{u} R, Module.Finite R A ∧ Algebra.FinitePresentation R A ∧
      ∃ φ : A →ₐ[R] B, (s : Set B) ⊆ Set.range φ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨CommAlgCat.of R R, inferInstance, inferInstance, Algebra.ofId R B, ?_⟩
    intro y hy
    exact (Finset.notMem_empty y hy).elim
  | @insert b s _ ih =>
    obtain ⟨A, hfinite, hfp, φ, hφ⟩ := ih
    have : Module.Finite R A := hfinite
    have : Algebra.FinitePresentation R A := hfp
    obtain ⟨p, hp, hpzero⟩ := Algebra.IsIntegral.isIntegral (R := R) b
    let q : Polynomial A := p.map (algebraMap R A)
    have hq : q.Monic := hp.map (algebraMap R A)
    have hqzero : q.eval₂ φ.toRingHom b = 0 := by
      change (p.map (algebraMap R A)).eval₂ φ.toRingHom b = 0
      have hφR : φ.toRingHom.comp (algebraMap R A) = algebraMap R B :=
        φ.comp_algebraMap
      calc
        (p.map (algebraMap R A)).eval₂ φ.toRingHom b =
            p.eval₂ (φ.toRingHom.comp (algebraMap R A)) b :=
          Polynomial.eval₂_map (p := p) (algebraMap R A) φ.toRingHom b
        _ = p.eval₂ (algebraMap R B) b :=
          congrArg (fun χ : R →+* B => p.eval₂ χ b) hφR
        _ = 0 := hpzero
    let ψ : AdjoinRoot q →ₐ[R] B := AdjoinRoot.liftAlgHom q φ b hqzero
    have : Module.Finite A (AdjoinRoot q) := hq.finite_adjoinRoot
    have : Module.Finite R (AdjoinRoot q) := Module.Finite.trans A (AdjoinRoot q)
    refine ⟨CommAlgCat.of R (AdjoinRoot q), inferInstance, inferInstance, ψ, ?_⟩
    intro y hy
    rcases Finset.mem_insert.mp hy with hyb | hy
    · exact ⟨AdjoinRoot.root q, (AdjoinRoot.liftAlgHom_root q φ b hqzero).trans hyb.symm⟩
    · obtain ⟨a, ha⟩ := hφ hy
      refine ⟨AdjoinRoot.of q a, ?_⟩
      exact (AdjoinRoot.liftAlgHom_of q φ b hqzero a).trans ha

end Algebra.IsIntegral
