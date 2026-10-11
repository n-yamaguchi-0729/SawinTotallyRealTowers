/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/

/-
Based on pi1 source (comparison revision; exact copied commit unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/Mathlib/AlgebraicGeometry/Morphisms/Finite.lean
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Cancellation for finite scheme morphisms

Finite morphisms satisfy cancellation after postcomposition by a finite morphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits MorphismProperty

namespace AlgebraicGeometry

namespace IsFinite

instance : HasOfPostcompProperty @IsFinite @IsFinite where
  of_postcomp f g _ _ := .of_comp f g

end IsFinite

end AlgebraicGeometry
