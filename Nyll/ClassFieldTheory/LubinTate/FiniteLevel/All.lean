/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.ChangedLevelCompositum
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.ChangedPrimitiveEvaluation
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.CompletedEvaluation
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.CompletedIterates
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.DivisionPolynomial
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameterFiltration
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.FiniteParameters
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.GaloisParameterFiltration
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.HerbrandFormula
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.HigherUnitLevelEquiv
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.LevelAbelian
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.LevelAutomorphisms
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.LevelFieldTower
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.LevelValuation
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.LocalUpperRamification
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.LowerRamification
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.LowerRamificationFormula
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.NormSubgroup
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.NormUniformizer
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.ParameterCongruence
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveAction
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveEisenstein
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveRoot
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveTorsion
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveUniformizer
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.StandardLocalField
import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.UpperRamification

/-!
# General finite-level Lubin--Tate theory

Public aggregate for the characteristic-independent standard division
polynomials, primitive torsion fields, analytic formal-module action, explicit
finite Galois parameterization, integral-closure valuation, ramification
filtrations and their Herbrand formula, level-field tower, and the norm of a
primitive uniformizer.  It also exports stability of a standard level under
a principal-unit change of its defining uniformizer.
-/
