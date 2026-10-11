/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.PlaneCurves.ConstantExtension
import Nyll.SchemeTheory.PlaneCurves.CoordinateRing
import Nyll.SchemeTheory.PlaneCurves.Dimension
import Nyll.SchemeTheory.PlaneCurves.Geometric
import Nyll.SchemeTheory.PlaneCurves.MonicChange
import Nyll.SchemeTheory.PlaneCurves.MonicProjection
import Nyll.SchemeTheory.PlaneCurves.NormalImpliesSimple
import Nyll.SchemeTheory.PlaneCurves.NormalPoint
import Nyll.SchemeTheory.PlaneCurves.PartialDerivatives
import Nyll.SchemeTheory.PlaneCurves.RationalPoints
import Nyll.SchemeTheory.PlaneCurves.SimpleImpliesNormal

/-!
# Affine plane curves

This facade collects coordinate rings, rational points, monic projections,
and the equivalence between simple and normal points on affine plane curves.
-/

/- Canonical aggregate for SchemeTheory.PlaneCurves. -/
