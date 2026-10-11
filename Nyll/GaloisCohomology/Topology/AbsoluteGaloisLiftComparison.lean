/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.Topology.AbsoluteGaloisMap

/-!
# Independence of closure lifts for commutative characters

A closure embedding intertwining two Galois automorphisms identifies their
values under every continuous character with commutative target. Its difference
from mathlib's chosen lift is removed by an inner automorphism.
-/

namespace Field.absoluteGaloisGroup

variable {K L : Type*} [Field K] [Field L]

/-- Any compatible closure embedding computes the same commutative character
restriction as the chosen absolute Galois map. -/
theorem character_map_apply_of_lift
    {A : Type*} [CommGroup A] [TopologicalSpace A]
    (f : K →+* L) (j : AlgebraicClosure K →+* AlgebraicClosure L)
    (hj : ∀ x : K, j (algebraMap K (AlgebraicClosure K) x) =
      algebraMap L (AlgebraicClosure L) (f x))
    (σ : Gal(AlgebraicClosure L/L)) (θ : Gal(AlgebraicClosure K/K))
    (hθ : ∀ x, j (θ x) = σ (j x))
    (χ : Gal(AlgebraicClosure K/K) →ₜ* A) :
    χ (map f σ) = χ θ := by
  let : Algebra K L := f.toAlgebra
  let j₁ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L :=
    { toRingHom := closureLift f
      commutes' := closureLift_algebraMap f }
  let j₂ : AlgebraicClosure K →ₐ[K] AlgebraicClosure L :=
    { toRingHom := j
      commutes' := hj }
  let : Algebra (AlgebraicClosure K) (AlgebraicClosure L) := j₁.toAlgebra
  let η : Gal(AlgebraicClosure K/K) := j₂.restrictNormal' (AlgebraicClosure K)
  have hη (x : AlgebraicClosure K) : j₁ (η x) = j₂ x :=
    j₂.restrictNormal_commutes (AlgebraicClosure K) x
  let ρ : Gal(AlgebraicClosure K/K) := map f σ
  have hcomm : ρ * η = η * θ := by
    ext x
    apply j₁.injective
    change j₁ (ρ (η x)) = j₁ (η (θ x))
    calc
      j₁ (ρ (η x)) = σ (j₁ (η x)) := map_closureLift f σ (η x)
      _ = σ (j₂ x) := congrArg σ (hη x)
      _ = j₂ (θ x) := (hθ x).symm
      _ = j₁ (η (θ x)) := (hη (θ x)).symm
  have hχ := congrArg χ hcomm
  rw [map_mul, map_mul, mul_comm (χ η)] at hχ
  exact mul_right_cancel hχ

end Field.absoluteGaloisGroup
