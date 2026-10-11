/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.FinitePresentationCoequalizer
import Nyll.SchemeTheory.RingTheory.IntegralFinitePresentationDiagram
import Nyll.SchemeTheory.RingTheory.IntegralFinitePresentationModel
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Algebra.Category.Ring.Colimits
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.InducedCategory
import Mathlib.CategoryTheory.Limits.Preserves.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Data.Finset.Insert
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Defs


/-!
# Integral algebras as filtered colimits of finite-FP models

The actual small model cocone is jointly surjective for an integral target,
by the finite-subset model construction. Equality of two elements in one
stage is detected later by coequalizing the two polynomial evaluation maps.
The native filtered-colimit criterion for types then proves that the
underlying commutative-ring cocone is colimiting.

All stages and the index remain in the base universe. This is the actual
ring-local approximation; global relative-Spec approximation is separate.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace Algebra.FinitePresentationModel

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- Every element of an integral algebra occurs in an actual indexed model. -/
theorem jointly_surjective [Algebra.IsIntegral R B] (b : B) :
    ∃ (M : FinitePresentationModel R B) (x : M.stage), M.map x = b := by
  obtain ⟨A, hfinite, hfp, φ, hφ⟩ :=
    Algebra.IsIntegral.exists_finitePresentation_range_finset R B {b}
  have : Module.Finite R A := hfinite
  have : Algebra.FinitePresentation R A := hfp
  obtain ⟨x, hx⟩ := hφ (Finset.mem_singleton_self b)
  obtain ⟨M, ⟨e⟩⟩ := exists_representation A φ
  let α : A →ₐ[R] M.stage := e.hom.left.hom
  have hα : M.map.comp α = φ := congrArg CommAlgCat.Hom.hom (Over.w e.hom)
  refine ⟨M, α x, ?_⟩
  exact (congrArg (fun k : A →ₐ[R] B => k x) hα).trans hx

/-- Equality in the target is detected after one actual transition map.
No integrality assumption is needed for this equality assertion. -/
theorem eventually_equal (M : FinitePresentationModel R B) (x y : M.stage)
    (h : M.map x = M.map y) :
    ∃ (N : FinitePresentationModel R B) (f : M ⟶ N),
      ((diagram R B).map f) x = ((diagram R B).map f) y := by
  have : Module.Finite R M.stage := M.finite
  have : Algebra.FinitePresentation R M.stage := M.finitePresentation
  let α : Polynomial R →ₐ[R] M.presentation.eval.obj := Polynomial.aeval x
  let β : Polynomial R →ₐ[R] M.presentation.eval.obj := Polynomial.aeval y
  let η : M.presentation.eval.obj →ₐ[R] B := M.map
  have hαβ : η.comp α = η.comp β := by
    apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, α, β, Polynomial.aeval_X]
    exact h
  obtain ⟨Q, hfinite, hfp, q, ψ, _, hψ, hq⟩ :=
    AlgHom.exists_finitePresentation_coequalizer.{u, u, u} R (Polynomial R)
      (M.presentation.eval.obj : Type u) B α β η hαβ
  have : Module.Finite R Q := hfinite
  have : Algebra.FinitePresentation R Q := hfp
  have hqxy : q x = q y := by
    have hX := congrArg (fun k : Polynomial R →ₐ[R] Q => k Polynomial.X) hq
    simpa only [AlgHom.comp_apply, α, β, Polynomial.aeval_X] using hX
  obtain ⟨N, ⟨e⟩⟩ := exists_representation Q ψ
  let a : M.toOver ⟶ Over.mk (CommAlgCat.ofHom ψ) :=
    Over.homMk (CommAlgCat.ofHom q) (by
      apply CommAlgCat.hom_ext
      exact hψ)
  refine ⟨N, InducedCategory.homMk (a ≫ e.hom), ?_⟩
  change e.hom.left (q x) = e.hom.left (q y)
  exact congrArg (fun z : Q => e.hom.left z) hqxy

variable (R B)

/-- The existing model diagram, viewed as a diagram of commutative rings. -/
def ringDiagram : FinitePresentationModel R B ⥤ CommRingCat.{u} :=
  diagram R B ⋙ forget₂ (CommAlgCat.{u} R) CommRingCat.{u}

/-- The actual model cocone in commutative rings. -/
def ringCocone : Cocone (ringDiagram R B) :=
  (forget₂ (CommAlgCat.{u} R) CommRingCat.{u}).mapCocone (cocone R B)

/-- The small filtered finite-FP model cocone is an actual ring colimit
when the target is integral over the base. -/
def ringCoconeIsColimit [Algebra.IsIntegral R B] : IsColimit (ringCocone R B) := by
  have : ReflectsColimit (ringDiagram R B) (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms (ringDiagram R B) (forget CommRingCat.{u})
  apply isColimitOfReflects (forget CommRingCat.{u})
  refine CategoryTheory.Limits.Types.FilteredColimit.isColimitOf'
    (ringDiagram R B ⋙ forget CommRingCat.{u})
    ((forget CommRingCat.{u}).mapCocone (ringCocone R B)) ?_ ?_
  · intro b
    obtain ⟨M, x, hx⟩ := jointly_surjective (R := R) (B := B) (show B from b)
    exact ⟨M, x, hx.symm⟩
  · intro M x y h
    obtain ⟨N, f, hxy⟩ := eventually_equal M x y h
    exact ⟨N, f, hxy⟩

end Algebra.FinitePresentationModel
