/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.FlatRank
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank

/-!
# Rank comparisons on actual generic and scheme-theoretic fibers

For finite flat morphisms, the literal scheme-theoretic fiber has the
rank of the original morphism at the chosen point. Over an integral base,
finite presentation makes this rank equal to the rank on any specified
actual generic-stalk pullback square. These comparisons are proved at the
scheme level, before introducing a field extension or its scalar structures.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A finite flat finitely presented morphism over an integral base has
the rank of its actual generic-stalk pullback at every base point. -/
theorem finrank_eq_genericStalkPullback
    {X Y Z : Scheme.{u}} [IsIntegral X]
    (f : Y ⟶ X) [Flat f] [IsFinite f] [LocallyOfFinitePresentation f]
    (i : Z ⟶ Y) (g : Z ⟶ Spec X.functionField)
    (H : IsPullback i g f (X.fromSpecStalk (genericPoint X))) (x : X) :
    f.finrank x = g.finrank (IsLocalRing.closedPoint X.functionField) := by
  calc
    f.finrank x = f.finrank (genericPoint X) :=
      finrank_eq_const_of_preconnectedSpace f x (genericPoint X)
    _ = f.finrank (X.fromSpecStalk (genericPoint X)
        (IsLocalRing.closedPoint X.functionField)) := by
      rw [Scheme.fromSpecStalk_closedPoint]
    _ = g.finrank (IsLocalRing.closedPoint X.functionField) :=
      (Scheme.Hom.finrank_of_isPullback i g f
        (X.fromSpecStalk (genericPoint X)) H
        (IsLocalRing.closedPoint X.functionField)).symm

/-- The rank of the actual scheme-theoretic fiber is the original rank
at the point, evaluated on the unique point of its residue-field spectrum. -/
theorem finrank_fiberToSpecResidueField
    {X Y : Scheme.{u}} (f : Y ⟶ X) [Flat f] [IsFinite f] (x : X) :
    (f.fiberToSpecResidueField x).finrank
        (IsLocalRing.closedPoint (X.residueField x)) = f.finrank x := by
  let p : Spec (X.residueField x) := IsLocalRing.closedPoint (X.residueField x)
  exact (Scheme.Hom.finrank_pullback_snd f (X.fromSpecResidueField x) p).trans
    (congrArg f.finrank (Scheme.fromSpecResidueField_apply x p))

end AlgebraicGeometry.Scheme.Hom
