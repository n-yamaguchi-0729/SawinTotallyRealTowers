/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleDatum
import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatOnOpenImage
import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatAlgebraEqualizer
import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatGradedAlgebraEqualizer
import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleEqualizer
import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatModuleHomDescent
import Nyll.SchemeTheory.RingTheory.Descent.ModuleBaseChangeHomExt
import Nyll.SchemeTheory.RingTheory.Descent.PrimeAwayAlgebraGluing
import Nyll.SchemeTheory.RingTheory.Descent.PrimeAwayPairGluing
import Nyll.SchemeTheory.RingTheory.Descent.PrimeAwayTensorDetection
import Nyll.SchemeTheory.RingTheory.Descent.FiniteSubalgebraLocalization
import Nyll.SchemeTheory.RingTheory.Descent.FiniteEtaleNeighborhood
import Nyll.SchemeTheory.RingTheory.Descent.BoundaryNormalIntegralClosure
import Nyll.SchemeTheory.RingTheory.Descent.IntegralClosureLocalizationAway
import Nyll.SchemeTheory.RingTheory.Descent.FiniteNormalizationModel
import Nyll.SchemeTheory.RingTheory.Descent.EtaleLocalNormality

import Nyll.SchemeTheory.RingTheory.Descent.EtalePrimeLocalization
import Nyll.SchemeTheory.RingTheory.Descent.FiniteNormalizationNeighborhood
import Nyll.SchemeTheory.RingTheory.Descent.FiniteNormalizationSpreading

import Nyll.SchemeTheory.RingTheory.Descent.FiniteType
import Nyll.SchemeTheory.RingTheory.Descent.FinitePresentation
import Nyll.SchemeTheory.RingTheory.Descent.EtaleAtPrimeNormality
import Nyll.SchemeTheory.RingTheory.Descent.FaithfullyFlatNormality
import Nyll.SchemeTheory.RingTheory.Descent.SmoothAtPrimeNormality

import Nyll.SchemeTheory.RingTheory.Descent.InvertibleModule


/- Canonical aggregate for SchemeTheory.RingTheory.Descent. -/
import Nyll.SchemeTheory.RingTheory.Descent.TensorComparison
import Nyll.SchemeTheory.RingTheory.Descent.GradedSubalgebra
import Nyll.SchemeTheory.RingTheory.Descent.GradedBaseChange
import Nyll.SchemeTheory.RingTheory.Descent.EtaleSource
import Nyll.SchemeTheory.RingTheory.Descent.EtaleOpenImage
import Nyll.SchemeTheory.RingTheory.Descent.PrincipalLocalizationModel
import Nyll.SchemeTheory.RingTheory.Descent.LocalizationNormalIntegralClosure
import Nyll.SchemeTheory.RingTheory.Descent.FiniteUnramifiedNeighborhood
import Nyll.SchemeTheory.RingTheory.Descent.EtaleLocalDomainOfIntegralNormalExtension
import Nyll.SchemeTheory.RingTheory.Descent.EtaleLocalIrreducibilityOfIntegralNormalExtension

/-!
# Faithfully flat descent and gluing of algebras

This aggregate exposes module and algebra equalizers, homomorphism descent, prime-away
gluing, finite etale neighborhoods, and descent of finite type and finite presentation.
-/
