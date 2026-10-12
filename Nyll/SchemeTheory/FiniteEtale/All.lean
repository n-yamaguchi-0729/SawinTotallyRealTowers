/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.AffineEquivalence
import Nyll.SchemeTheory.FiniteEtale.AffineThickening
import Nyll.SchemeTheory.FiniteEtale.AffineUniversalHomeomorphismModel
import Nyll.SchemeTheory.FiniteEtale.Algebra.All
import Nyll.SchemeTheory.FiniteEtale.Away.All
import Nyll.SchemeTheory.FiniteEtale.BaseChange.All
import Nyll.SchemeTheory.FiniteEtale.ClopenFull
import Nyll.SchemeTheory.FiniteEtale.ClopenPullback
import Nyll.SchemeTheory.FiniteEtale.ConnectedFiberSections
import Nyll.SchemeTheory.FiniteEtale.ConnectedFiberFullyFaithful
import Nyll.SchemeTheory.FiniteEtale.MaximalOpenExtension
import Nyll.SchemeTheory.FiniteEtale.FullOfSectionDescent
import Nyll.SchemeTheory.FiniteEtale.DensePullback
import Nyll.SchemeTheory.FiniteEtale.DVRUnramifiedExtension
import Nyll.SchemeTheory.FiniteEtale.Forget.All
import Nyll.SchemeTheory.FiniteEtale.Henselian.All
import Nyll.SchemeTheory.FiniteEtale.Local.All
import Nyll.SchemeTheory.FiniteEtale.LocalSplitting
import Nyll.SchemeTheory.FiniteEtale.PullbackFaithful
import Nyll.SchemeTheory.FiniteEtale.PullbackRepresentable
import Nyll.SchemeTheory.FiniteEtale.RadicialDescentCocycle
import Nyll.SchemeTheory.FiniteEtale.RadicialDescentIso
import Nyll.SchemeTheory.FiniteEtale.RingCover
import Nyll.SchemeTheory.FiniteEtale.ThickeningFullyFaithful
import Nyll.SchemeTheory.FiniteEtale.ThickeningGluing
import Nyll.SchemeTheory.FiniteEtale.UniversalHomeomorphismFullyFaithful
import Nyll.SchemeTheory.FiniteEtale.SectionsDescent
import Nyll.SchemeTheory.FiniteEtale.AffinizationExtension
import Nyll.SchemeTheory.FiniteEtale.PointSections
import Nyll.SchemeTheory.FiniteEtale.InverseLimitHom
import Nyll.SchemeTheory.FiniteEtale.InverseLimitEquality
import Nyll.SchemeTheory.FiniteEtale.FilteredColimitSpec
import Nyll.SchemeTheory.FiniteEtale.AffineTransitionModel
import Nyll.SchemeTheory.FiniteEtale.AffineTransitionCharts
import Nyll.SchemeTheory.FiniteEtale.RelativeGluing
import Nyll.SchemeTheory.FiniteEtale.TwoOpenGluing
import Nyll.SchemeTheory.FiniteEtale.InverseLimitIsomorphism
import Nyll.SchemeTheory.FiniteEtale.AffineTransitionLocalModel
import Nyll.SchemeTheory.FiniteEtale.InverseLimitOpenEquations
import Nyll.SchemeTheory.FiniteEtale.InverseLimitFiniteCover
import Nyll.SchemeTheory.FiniteEtale.InverseLimitIsoDescent
import Nyll.SchemeTheory.FiniteEtale.InverseLimitIsoModels
import Nyll.SchemeTheory.FiniteEtale.InverseLimitOpenIsomorphisms
import Nyll.SchemeTheory.FiniteEtale.AffineTransitionOverlapRecovery
import Nyll.SchemeTheory.FiniteEtale.InverseLimitGluingRelations
import Nyll.SchemeTheory.FiniteEtale.RelativePullbackGluing
import Nyll.SchemeTheory.FiniteEtale.RelativeOverlapFiniteness
import Nyll.SchemeTheory.FiniteEtale.InverseLimitRecoveredModel
import Nyll.SchemeTheory.FiniteEtale.RawOverlapFiniteness
import Nyll.SchemeTheory.FiniteEtale.InverseLimitRawCharts
import Nyll.SchemeTheory.FiniteEtale.InverseLimitRawModel
import Nyll.SchemeTheory.FiniteEtale.InverseLimitModel
import Nyll.SchemeTheory.FiniteEtale.StrictLocalSections
import Nyll.SchemeTheory.FiniteEtale.ProperClosedFiberFaithful
import Nyll.SchemeTheory.FiniteEtale.ProperHenselianSections
import Nyll.SchemeTheory.FiniteEtale.AffineUniversalHomeomorphismEquivalence
import Nyll.SchemeTheory.FiniteEtale.isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper


/-!
# Finite étale scheme theory

This facade collects affine Weil restriction, fpqc descent for finite étale
algebras, exactness of the forgetful functor, and étale schemes over a field.
-/

/- Canonical aggregate for SchemeTheory.FiniteEtale. -/
