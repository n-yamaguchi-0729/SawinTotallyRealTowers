/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.Abelian.PrimeQuotients
import Nyll.ProCGroups.Abelian.AbelianModPower
import Nyll.ProCGroups.Abelian.SubgroupCommutator
import Nyll.ProCGroups.Abelian.Transfer
import Nyll.ProCGroups.Abelian.PrimaryDetection
import Nyll.ProCGroups.Abelian.CharacterDetection
import Nyll.ProCGroups.Abelian.FiniteInvariantQuotients
import Nyll.ProCGroups.Abelian.TopologicalAbelianization
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationKernel
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationFunctoriality
import Nyll.ProCGroups.Abelian.TopologicalAbelianizationLimits
import Nyll.ProCGroups.Abelian.PrimeExponentCharacters
import Nyll.ProCGroups.Abelian.PrimePowerCharacters

import Nyll.ProCGroups.Abelian.TopologicalAbelianizationQuotientFaithfulness

import Nyll.ProCGroups.Abelian.PrimaryTorsion

import Nyll.ProCGroups.Abelian.PowerQuotientAction
import Nyll.ProCGroups.Abelian.FiniteBidual
import Nyll.ProCGroups.Abelian.ProfiniteBidual

import Nyll.ProCGroups.Abelian.FullTateModule
import Nyll.ProCGroups.Abelian.FullTateCharacters
import Nyll.ProCGroups.Abelian.RestrictedTateModule
import Nyll.ProCGroups.Abelian.ProfiniteCharacterCriterion
import Nyll.ProCGroups.Abelian.FiniteCharacterCriterion
import Nyll.ProCGroups.Abelian.RootsOfUnityCharacterCriterion
/-!
# Abelian constructions

This aggregate module exposes topological abelianization, its functoriality, and its compatibility
with inverse limits.
-/
