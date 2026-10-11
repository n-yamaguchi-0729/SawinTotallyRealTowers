/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.ProCGroups.Abelian.ProfiniteBidual
import Mathlib.Topology.Algebra.PontryaginDual
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Detecting isomorphisms of profinite abelian groups by actual characters

Bijectivity of pullback on continuous circle-valued characters detects
bijectivity of the original homomorphism. Surjectivity uses the actual
profinite biduality theorem and the continuity of the inverse between the
discrete character groups.
-/

noncomputable section

namespace ProCGroups.Duality

universe u v

variable {G : Type u} {H : Type v} [CommGroup G] [CommGroup H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  [CompactSpace G] [CompactSpace H]
  [TotallyDisconnectedSpace G] [TotallyDisconnectedSpace H]

/-- Actual character pullback detects bijectivity of a continuous homomorphism. -/
theorem bijective_of_bijective_character_pullback (f : G →ₜ* H)
    (hf : Function.Bijective (PontryaginDual.map f)) : Function.Bijective f := by
  let e : PontryaginDual H ≃* PontryaginDual G :=
    MulEquiv.ofBijective (PontryaginDual.map f).toMonoidHom hf
  let eInv : PontryaginDual G →ₜ* PontryaginDual H :=
    { toMonoidHom := e.symm.toMonoidHom
      continuous_toFun := continuous_of_discreteTopology }
  constructor
  · intro x y hxy
    apply profinite_bidualEvaluation_injective
    apply PontryaginDual.ext
    intro χ
    obtain ⟨ψ, rfl⟩ := hf.surjective χ
    change ψ (f x) = ψ (f y)
    exact congrArg ψ hxy
  · intro y
    let η : PontryaginDual (PontryaginDual G) := (bidualEvaluation H y).comp eInv
    obtain ⟨x, hx⟩ := profinite_bidualEvaluation_surjective η
    refine ⟨x, ?_⟩
    apply profinite_bidualEvaluation_injective
    apply PontryaginDual.ext
    intro χ
    have h := congrArg (fun z : PontryaginDual (PontryaginDual G) =>
      z (PontryaginDual.map f χ)) hx
    change χ (f x) = (e.symm (e χ)) y at h
    rw [e.symm_apply_apply] at h
    exact h

/-- The original homomorphism is a topological group isomorphism when its
actual character pullback is bijective. -/
def equivOfBijectiveCharacterPullback (f : G →ₜ* H)
    (hf : Function.Bijective (PontryaginDual.map f)) : G ≃ₜ* H := by
  let e : G ≃* H := MulEquiv.ofBijective f.toMonoidHom
    (bijective_of_bijective_character_pullback f hf)
  exact
    { toMulEquiv := e
      continuous_toFun := f.continuous
      continuous_invFun := (Continuous.homeoOfEquivCompactToT2 (f := e.toEquiv)
        f.continuous).continuous_invFun }

end ProCGroups.Duality
