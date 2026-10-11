/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ProjSpaceCover.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.ProjectiveSpace.Basic
import Nyll.SchemeTheory.Cohomology.Cech.OrderedAffineCoverCech
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-!
# The standard affine cover of projective space

The coordinate basic opens give an ordered affine cover of projective space and affine
pullback covers for affine morphisms into projective space.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace MvPolynomial

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjSpace

section StdCover

variable (R : Type u) [CommRing R] (n : ℕ)

local notation "𝒜" => MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The standard ordered affine cover of projective space by the coordinate basic opens. -/
def stdCover : Scheme.OrderedAffineCover.{u} (Proj 𝒜) where
  ι := ULift.{u} (Fin (n + 1))
  U j := AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j.down)
  isAffineOpen j := AlgebraicGeometry.Proj.isAffineOpen_basicOpen 𝒜 (MvPolynomial.X j.down)
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R j.down))
    one_pos
  iSup_eq_top := by
    have key : (⨆ j : ULift.{u} (Fin (n + 1)),
        AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j.down))
        = ⨆ j : Fin (n + 1), AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j) := by
      refine le_antisymm (iSup_le fun j => ?_) (iSup_le fun j => ?_)
      · exact le_iSup (fun j' : Fin (n + 1) => AlgebraicGeometry.Proj.basicOpen 𝒜 (X j')) j.down
      · exact le_iSup (fun j' : ULift.{u} (Fin (n + 1)) =>
          AlgebraicGeometry.Proj.basicOpen 𝒜 (X j'.down)) (ULift.up j)
    rw [key]
    exact AlgebraicGeometry.Proj.iSup_basicOpen_eq_top 𝒜 _
      (irrelevant_le_span_X R n)

theorem stdCover_U (j : ULift.{u} (Fin (n + 1))) :
    (stdCover R n).U j = AlgebraicGeometry.Proj.basicOpen 𝒜 (MvPolynomial.X j.down) := rfl

end StdCover

section StdCoverPullback

variable {A : Type u} [CommRing A] {n : ℕ}
variable {W : Scheme.{u}}
  (ι : W ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]

/-- Pull back the standard coordinate cover along an affine morphism to projective space. -/
def stdCoverPullback : Scheme.OrderedAffineCover.{u} W :=
  let f := ι
  { ι := ULift.{u} (Fin (n + 1))
    U := fun j => f ⁻¹ᵁ ((stdCover A n).U j)
    isAffineOpen := fun j => ((stdCover A n).isAffineOpen j).preimage f
    iSup_eq_top := Scheme.Hom.iSup_preimage_eq_top f (stdCover A n).iSup_eq_top }

theorem stdCoverPullback_U (j : ULift.{u} (Fin (n + 1))) :
    (stdCoverPullback ι).U j = ι ⁻¹ᵁ (stdCover A n).U j := rfl

end StdCoverPullback

end ProjSpace

end AlgebraicGeometry

end
