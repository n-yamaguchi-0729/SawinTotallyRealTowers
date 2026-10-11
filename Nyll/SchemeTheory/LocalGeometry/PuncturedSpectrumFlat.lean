/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.LocalGeometry.PuncturedSpectrum
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Topology.Inseparable

/-!
# Density of a punctured local spectrum after flat base change

The inverse image of a nonempty punctured local spectrum is dense under
any flat morphism. For a point over the closed point, flat going-down lifts
the generalization from a chosen puncture point. Every remaining point is
already in the inverse image. No finite-presentation or quasi-compactness
assumption on the flat morphism is needed.
-/

open CategoryTheory

namespace AlgebraicGeometry.Scheme

universe u

/-- A nonempty punctured local spectrum remains dense after arbitrary flat
base change, including flat maps that are not locally of finite presentation. -/
theorem dense_preimage_puncturedSpectrumOpen_of_flat
    (R : Type u) [CommRing R] [IsLocalRing R]
    [Nonempty (puncturedSpectrum R)]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of R)) [Flat f] :
    Dense (f ⁻¹' (puncturedSpectrumOpen R : Set (Spec (.of R)))) := by
  classical
  obtain ⟨q⟩ := (inferInstance : Nonempty (puncturedSpectrum R))
  let q₀ : Spec (.of R) := (puncturedSpectrumOpen R).ι q
  have hq₀ : q₀ ∈ puncturedSpectrumOpen R :=
    (Scheme.Opens.range_ι (puncturedSpectrumOpen R)).subset ⟨q, rfl⟩
  intro x
  by_cases hx : f x = IsLocalRing.closedPoint R
  · have hspecializes : q₀ ⤳ f x := by
      rw [hx]
      exact IsLocalRing.specializes_closedPoint q₀
    obtain ⟨y, hy, hfy⟩ := (Flat.generalizingMap f) hspecializes
    apply hy.mem_closed isClosed_closure
    apply subset_closure
    change f y ∈ puncturedSpectrumOpen R
    rw [hfy]
    exact hq₀
  · apply subset_closure
    exact (mem_puncturedSpectrumOpen_iff R (f x)).mpr hx

end AlgebraicGeometry.Scheme
