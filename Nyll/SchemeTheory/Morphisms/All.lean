/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Morphisms.ClosedImmersion
import Nyll.SchemeTheory.Morphisms.ClosedImmersionLift
import Nyll.SchemeTheory.Morphisms.DominantBaseChange
import Nyll.SchemeTheory.Morphisms.EtaleRadicial
import Nyll.SchemeTheory.Morphisms.EtaleReduced
import Nyll.SchemeTheory.Morphisms.Finite
import Nyll.SchemeTheory.Morphisms.FiniteDescent
import Nyll.SchemeTheory.Morphisms.Flat
import Nyll.SchemeTheory.Morphisms.FlatRank
import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralDescent
import Nyll.SchemeTheory.Morphisms.NormalizationFiniteFactor
import Nyll.SchemeTheory.Morphisms.OpenImmersionLocalization
import Nyll.SchemeTheory.Morphisms.OpenImmersionQuotient
import Nyll.SchemeTheory.Morphisms.RadicialDescent
import Nyll.SchemeTheory.Morphisms.Smooth
import Nyll.SchemeTheory.Morphisms.SmoothLocus
import Nyll.SchemeTheory.Morphisms.SigmaPullback
import Nyll.SchemeTheory.Morphisms.UnramifiedHomExt
import Nyll.SchemeTheory.Morphisms.SmoothGeometricallyIntegral
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleOverAlgebraicallyClosed
import Nyll.SchemeTheory.Morphisms.GeometricallyIrreducibleConnected
import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralFieldDescent
import Nyll.SchemeTheory.Morphisms.FiberRank
import Nyll.SchemeTheory.Morphisms.QuasiFinite
import Nyll.SchemeTheory.Morphisms.UnramifiedPointRigidity
import Nyll.SchemeTheory.Morphisms.ResiduePointFixedness
import Nyll.SchemeTheory.Morphisms.ProperNormalization
import Nyll.SchemeTheory.Morphisms.FlatBaseChangeNormalization
import Nyll.SchemeTheory.Morphisms.AffineNormalizationPushforward
import Nyll.SchemeTheory.Morphisms.NormalizationPushforward
import Nyll.SchemeTheory.Morphisms.NormalizationFlatBaseChangeIso
import Nyll.SchemeTheory.Morphisms.EtalePostcomposition
import Nyll.SchemeTheory.Morphisms.FiniteEtaleGeometricallyReduced
import Nyll.SchemeTheory.Morphisms.ProperHenselianClosedRestriction
import Nyll.SchemeTheory.Morphisms.ProperHenselianClopenLift
import Nyll.SchemeTheory.Morphisms.ProperIntegralHenselianConnectedFiber
import Nyll.SchemeTheory.Morphisms.ProperIntegralHenselianSections
import Nyll.SchemeTheory.Morphisms.NoetherianProperFiberSections
import Nyll.SchemeTheory.Morphisms.ChowDatumProj_nonempty_of
import Nyll.SchemeTheory.Morphisms.ChowDatum_nonempty
import Nyll.SchemeTheory.Morphisms.exists_appTop_pullback_map_eq_appTop_pullback_fst_of_isProper
import Nyll.SchemeTheory.Morphisms.ProperHenselianSheafRestriction

/-!
# Scheme morphisms

This facade collects the finite, flat, smooth, rank, reduced-etale, and
closed-immersion lemmas used by the finite étale and fundamental-group
developments.
-/

/- Canonical aggregate for SchemeTheory.Morphisms. -/
