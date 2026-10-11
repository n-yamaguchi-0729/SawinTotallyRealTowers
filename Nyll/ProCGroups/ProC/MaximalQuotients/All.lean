/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualOrdinaryFaithfulness
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualProGroupFaithfulness
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualAbelianizationMonotonicity
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualMonotonicity
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualEquivalence
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientTransport
import Nyll.ProCGroups.ProC.MaximalQuotients.ConjugationComparison
import Nyll.ProCGroups.ProC.MaximalQuotients.Definitions
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualCore
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualIdempotence
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotient
import Nyll.ProCGroups.ProC.MaximalQuotients.SubgroupComparison
import Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualUniversalProperty
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualQuotientAction
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualPrimeExclusion
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualSigmaPower
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualAbelianizationPrimePowers
import Nyll.ProCGroups.ProC.MaximalQuotients.ResidualPowerDetection

/-!
# Maximal pro-\(C\) quotients

This aggregate exports the universal-property definition of a maximal pro-\(C\) quotient, its
construction from the intersection of all admissible kernels, and the resulting factorization
theorems.
-/
