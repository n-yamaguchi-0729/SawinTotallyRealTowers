/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FiniteEtale.Algebra.Basic
import Nyll.SchemeTheory.FiniteEtale.Algebra.Descent
import Nyll.SchemeTheory.FiniteEtale.Algebra.Equalizer
import Nyll.SchemeTheory.FiniteEtale.Algebra.EtaleQuotientLift
import Nyll.SchemeTheory.FiniteEtale.Algebra.EtaleSection
import Nyll.SchemeTheory.FiniteEtale.Algebra.FaithfullyFlatDescent
import Nyll.SchemeTheory.FiniteEtale.Algebra.FiniteFieldModel
import Nyll.SchemeTheory.FiniteEtale.Algebra.FiniteCoefficientModel
import Nyll.SchemeTheory.FiniteEtale.Algebra.FinitelyGeneratedModel
import Nyll.SchemeTheory.FiniteEtale.Algebra.FilteredColimitModel
import Nyll.SchemeTheory.FiniteEtale.Algebra.FormallyEtaleNilpotent
import Nyll.SchemeTheory.FiniteEtale.Algebra.HenselianBaseChange
import Nyll.SchemeTheory.FiniteEtale.Algebra.HenselianEtaleSection
import Nyll.SchemeTheory.FiniteEtale.Algebra.HenselianEtaleMapLift
import Nyll.SchemeTheory.FiniteEtale.Algebra.HenselianFullness
import Nyll.SchemeTheory.FiniteEtale.Algebra.HenselianQuotientLift
import Nyll.SchemeTheory.FiniteEtale.Algebra.IdempotentFactor
import Nyll.SchemeTheory.FiniteEtale.Algebra.IntegralFiniteModel
import Nyll.SchemeTheory.FiniteEtale.Algebra.JacobsonBaseChange
import Nyll.SchemeTheory.FiniteEtale.Algebra.JacobsonConservativity
import Nyll.SchemeTheory.FiniteEtale.Algebra.JacobsonRigidity
import Nyll.SchemeTheory.FiniteEtale.Algebra.JacobsonSection
import Nyll.SchemeTheory.FiniteEtale.Algebra.NilpotentBaseChange
import Nyll.SchemeTheory.FiniteEtale.Algebra.SectionFactor
import Nyll.SchemeTheory.FiniteEtale.Algebra.Splitting
import Nyll.SchemeTheory.FiniteEtale.Algebra.PrimeRigidity


/- Canonical aggregate for SchemeTheory.FiniteEtale.Algebra. -/
import Nyll.SchemeTheory.FiniteEtale.Algebra.PointSpecialization
import Nyll.SchemeTheory.FiniteEtale.Algebra.FiniteGeometricallyReducedEtale
import Nyll.SchemeTheory.FiniteEtale.Algebra.FiniteSplitIdempotentSurjectivity
import Nyll.SchemeTheory.FiniteEtale.Algebra.LocalEtaleFromClosedFiber
import Nyll.SchemeTheory.FiniteEtale.Algebra.FiniteEtaleSplittingField
import Nyll.SchemeTheory.FiniteEtale.Algebra.EtaleFromLocalizations
import Nyll.SchemeTheory.FiniteEtale.Algebra.ProductBaseChangeComparison
import Nyll.SchemeTheory.FiniteEtale.Algebra.UniversalHomeomorphismAlgHom
import Nyll.SchemeTheory.FiniteEtale.Algebra.FiniteRadicialEssentialSurjectivity
import Nyll.SchemeTheory.FiniteEtale.Algebra.IntegralRadicialEssentialSurjectivity
