/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.AffineClosedLift
import Nyll.SchemeTheory.Etale.AffineResidueField
import Nyll.SchemeTheory.Etale.AffineGeometricFiberBound
import Nyll.SchemeTheory.Etale.AffineFinitePresentationRefinement
import Nyll.SchemeTheory.Etale.AffineLocalFactorDescent
import Nyll.SchemeTheory.Etale.ChosenResidueExtension
import Nyll.SchemeTheory.Etale.ClosedNeighborhoodEqualizer
import Nyll.SchemeTheory.Etale.ClosedNeighborhoodLift
import Nyll.SchemeTheory.Etale.FiniteNeighborhoodSection
import Nyll.SchemeTheory.Etale.FiniteAffineCover
import Nyll.SchemeTheory.Etale.FiniteRadicialLocalSection
import Nyll.SchemeTheory.Etale.GeometricFiberNeighborhood
import Nyll.SchemeTheory.Etale.IsomorphismNeighborhood
import Nyll.SchemeTheory.Etale.NormalizationRemainder
import Nyll.SchemeTheory.Etale.NormalizationRemainderDegree
import Nyll.SchemeTheory.Etale.OverField.All
import Nyll.SchemeTheory.Etale.ProperLocalCover
import Nyll.SchemeTheory.Etale.ResidueBaseChange
import Nyll.SchemeTheory.Etale.ResidueFieldExtension
import Nyll.SchemeTheory.Etale.UniversalHomeomorphismSections
import Nyll.SchemeTheory.Etale.AffineBaseChangeProperties
import Nyll.SchemeTheory.Etale.HenselianLocalSection
import Nyll.SchemeTheory.Etale.GeometricFiberBound
import Nyll.SchemeTheory.Etale.IntegralRefinement
import Nyll.SchemeTheory.Etale.LocalResidueFieldExtension
import Nyll.SchemeTheory.Etale.ResidueFieldPushout
import Nyll.SchemeTheory.Etale.ClosedFiberBaseChange
import Nyll.SchemeTheory.Etale.PurelyInseparableFiniteFactor
import Nyll.SchemeTheory.Etale.FiniteRadicialLocalSplitting
import Nyll.SchemeTheory.Etale.FiniteRadicialSplittingAlgebra
import Nyll.SchemeTheory.Etale.FiniteRadicialSplittingCover
import Nyll.SchemeTheory.Etale.MaximalSectionExtension
import Nyll.SchemeTheory.Etale.AffineFiniteSubalgebraRefinement
import Nyll.SchemeTheory.Etale.LocalFactorBaseChange
import Nyll.SchemeTheory.Etale.AffineChartFiniteSubalgebra
import Nyll.SchemeTheory.Etale.LocalFactorOpenCover
import Nyll.SchemeTheory.Etale.FiniteRefinement
import Nyll.SchemeTheory.Etale.FiniteGeometricPoints
import Nyll.SchemeTheory.Etale.HenselianLocalGeometricSection

/- Canonical aggregate for SchemeTheory.Etale. -/
