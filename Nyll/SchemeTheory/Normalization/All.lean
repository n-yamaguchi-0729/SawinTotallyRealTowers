/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Nyll.SchemeTheory.Normalization.Affine
import Nyll.SchemeTheory.Normalization.CompositumEmbedding
import Nyll.SchemeTheory.Normalization.ConductorQuotient
import Nyll.SchemeTheory.Normalization.FiniteEtaleOpen
import Nyll.SchemeTheory.Normalization.FiniteSeparable
import Nyll.SchemeTheory.Normalization.GenericFiber.All
import Nyll.SchemeTheory.Normalization.HenselianIntegralSection
import Nyll.SchemeTheory.Normalization.HenselianSectionFactor
import Nyll.SchemeTheory.Normalization.IntegralClosure.All
import Nyll.SchemeTheory.Normalization.IntegralOpen
import Nyll.SchemeTheory.Normalization.Localization.All
import Nyll.SchemeTheory.Normalization.Normal
import Nyll.SchemeTheory.Normalization.PrimeSeparation
import Nyll.SchemeTheory.Normalization.Products.All
import Nyll.SchemeTheory.Normalization.QuotientFiniteFactor

import Nyll.SchemeTheory.Normalization.AffineFiniteEtale




/- Canonical aggregate for SchemeTheory.Normalization. -/
import Nyll.SchemeTheory.Normalization.NativeNormalizationPrime
import Nyll.SchemeTheory.Normalization.IntegralClosureAutomorphisms
import Nyll.SchemeTheory.Normalization.NormalizationAutomorphismSurjectivity
import Nyll.SchemeTheory.Normalization.NormalizationGaloisSurjectivity
import Nyll.SchemeTheory.Normalization.IntegralClosureAutomorphismRestriction
import Nyll.SchemeTheory.Normalization.NormalizationAutomorphismGroupMap
import Nyll.SchemeTheory.Normalization.ScalarRestrictionGroupMap
import Nyll.SchemeTheory.Normalization.NativeAutomorphismRingMaps
import Nyll.SchemeTheory.Normalization.AmbientNormalizationGroupMap
import Nyll.SchemeTheory.Normalization.NativeNormalizationRingMap
import Nyll.SchemeTheory.Normalization.SubalgebraNormalizationTower
import Nyll.SchemeTheory.Normalization.SubalgebraNormalizationTowerRamification
import Nyll.SchemeTheory.Normalization.FiniteNormalSource

/-!
# Normalization of affine curves

This facade collects normalization finiteness, conductor-quotient, and
prime-separation results.
-/
