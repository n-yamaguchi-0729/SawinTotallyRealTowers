/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.FiniteNeighborhoodSection
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Maps.Basic


/-!
# Detecting étale coverings on the closed fiber of a proper local scheme

For a universally closed scheme over a local spectrum, an étale morphism is
surjective exactly when its base change to the closed fiber is surjective.
The open image of the étale morphism contains the entire closed fiber. The
existing closed-map neighborhood theorem then supplies an open neighborhood
of the closed point, which must be the entire local spectrum.

In particular this applies to every proper morphism over a local ring. It is
the covering-detection input for descent from the closed fiber in the
proper-local comparison. It asserts no cohomological base-change theorem.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Etale

/-- An étale morphism into a universally closed scheme over a local spectrum
is surjective if its image contains the closed fiber. -/
theorem surjective_of_closedFiber_subset_range
    (R : Type u) [CommRing R] [IsLocalRing R]
    {X U : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f]
    (p : U ⟶ X) [Etale p]
    (hfiber : ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ Set.range p) :
    Surjective p := by
  let V : X.Opens := ⟨Set.range p, p.isOpenMap.isOpen_range⟩
  obtain ⟨W, hW, hWV⟩ := f.exists_preimage_le_of_fiber_subset
    (IsLocalRing.closedPoint R) V (fun x hx => hfiber x hx)
  have hWtop : W = ⊤ := (IsLocalRing.closedPoint_mem_iff W).mp hW
  refine ⟨fun x => ?_⟩
  have hxW : f x ∈ W := by
    rw [hWtop]
    exact TopologicalSpace.Opens.mem_top (f x)
  exact hWV hxW

/-- Surjectivity of an étale morphism into a universally closed local scheme
is detected after base change to its actual scheme-theoretic closed fiber. -/
theorem surjective_iff_closedFiber
    (R : Type u) [CommRing R] [IsLocalRing R]
    {X U : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [UniversallyClosed f]
    (p : U ⟶ X) [Etale p] :
    Surjective p ↔
      Surjective (pullback.snd p (pullback.fst f
        (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) := by
  constructor
  · intro hp
    have : Surjective p := hp
    infer_instance
  · intro hp
    apply surjective_of_closedFiber_subset_range R f p
    intro x hx
    let s : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) ⟶
        Spec (CommRingCat.of R) :=
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))
    let q : pullback f s ⟶ X := pullback.fst f s
    let x₀ : Spec (CommRingCat.of (IsLocalRing.ResidueField R)) := default
    have hs : s x₀ = IsLocalRing.closedPoint R :=
      IsLocalRing.PrimeSpectrum.comap_residue R x₀
    obtain ⟨z, hzx, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := s) x x₀ (hx.trans hs.symm)
    have : Surjective (pullback.snd p q) := hp
    obtain ⟨w, hw⟩ := (pullback.snd p q).surjective z
    refine ⟨pullback.fst p q w, ?_⟩
    have hcomm : p (pullback.fst p q w) = q (pullback.snd p q w) := by
      simpa only [Scheme.Hom.comp_apply] using
        congrArg (fun k : pullback p q ⟶ X => k w) (pullback.condition (f := p) (g := q))
    exact hcomm.trans ((congrArg q hw).trans hzx)

end AlgebraicGeometry.Etale
