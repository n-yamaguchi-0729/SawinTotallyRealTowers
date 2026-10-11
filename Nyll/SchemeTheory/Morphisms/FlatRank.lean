/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 file has no copyright notice; its holder requires review.

Based on pi1 source (comparison revision; exact copied commit unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/FundamentalGroup/Rank.lean
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Constant rank of finite flat morphisms

The locally constant rank of a finite flat morphism of finite presentation is constant
on a preconnected target.
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace TensorProduct

universe u

namespace AlgebraicGeometry

noncomputable section

variable {X S : Scheme.{u}} (f : X ⟶ S)

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [IsFinite f]
    [LocallyOfFinitePresentation f]

lemma finrank_eq_const_of_preconnectedSpace [PreconnectedSpace Y] (y y' : Y) :
    f.finrank y = f.finrank y' := by
  apply IsLocallyConstant.apply_eq_of_preconnectedSpace
  apply f.isLocallyConstant_finrank

end

end AlgebraicGeometry
