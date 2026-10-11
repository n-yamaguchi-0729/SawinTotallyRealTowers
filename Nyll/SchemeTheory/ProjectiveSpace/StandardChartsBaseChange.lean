/-
Copyright (c) 2026 Naganori Yamaguchi (local additions and compilation).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

This library builds on Anthropic's Fermat's Last Theorem in Lean 4;
no direct Anthropic source-file match is established for this module.
Upstream NOTICE (Copyright 2026 Anthropic, PBC): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
Repository maintainer: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic

/-!
# Coordinate opens under projective-space base change

The inverse image of a coordinate basic open under the base-change map of projective
spaces is the corresponding coordinate basic open over the new ring.
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_map_preimage_basicOpen_X

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

attribute [local instance] MvPolynomial.gradedAlgebra

theorem _root_.AlgebraicGeometry.ProjSpace.map_preimage_basicOpen_X (R A : Type u) [CommRing R]
    [CommRing A] [Algebra R A] (n : ℕ) (j : Fin (n + 1)) :
    ProjSpace.map R A n ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
        (MvPolynomial.X j)
      = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X j) := by
  rw [ProjSpace.map_eq, AlgebraicGeometry.Proj.map_preimage_basicOpen]
  exact congrArg (AlgebraicGeometry.Proj.basicOpen _) (MvPolynomial.map_X _ j)

end
end AlgebraicCurves.Geometry.Projective.Proofs.ProjSpace_map_preimage_basicOpen_X
end ProofImplementation
