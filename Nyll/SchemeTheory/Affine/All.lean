/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.SeparatedIntersections
import Nyll.SchemeTheory.Affine.PullbackSectionsPushout
import Nyll.SchemeTheory.Affine.FlatBaseChangeSections
import Nyll.SchemeTheory.Affine.FlatMinimalPrime
import Nyll.SchemeTheory.Affine.GeometricPointLocalization
import Nyll.SchemeTheory.Affine.GeometricIrreducibility
import Nyll.SchemeTheory.Affine.Over
import Nyll.SchemeTheory.Affine.Property
import Nyll.SchemeTheory.Affine.RegularSection
import Nyll.SchemeTheory.Affine.StalkLocalization
import Nyll.SchemeTheory.Affine.WeilRestriction.All
import Nyll.SchemeTheory.Affine.PrimePairHartogs
import Nyll.SchemeTheory.Affine.RegularPairHartogs
import Nyll.SchemeTheory.Affine.FlatBaseChangeAffinization
import Nyll.SchemeTheory.Affine.AffinizationDescent

import Nyll.SchemeTheory.Affine.ChartStalkLocalization

import Nyll.SchemeTheory.Affine.StalkBaseChange
import Nyll.SchemeTheory.Affine.SpecSectionMap
import Nyll.SchemeTheory.Affine.HomeomorphismIdempotentSections
import Nyll.SchemeTheory.Affine.ConnectedOfGlobalSections
import Nyll.SchemeTheory.Affine.GeometricallyConnectedOfGlobalSections
import Nyll.SchemeTheory.Affine.FaithfullyFlatSectionSurjectivity
import Nyll.SchemeTheory.Affine.SpecFlatBaseChangeSections
import Nyll.SchemeTheory.Affine.SurjectiveSectionPushout
import Nyll.SchemeTheory.Affine.StalkBaseChangeSections
/-!
# Affine scheme infrastructure

This facade collects affine-over-base colimits, affine morphism properties,
flat minimal-prime control, and geometric irreducibility of affine schemes.
-/

/- Canonical aggregate for SchemeTheory.Affine. -/
