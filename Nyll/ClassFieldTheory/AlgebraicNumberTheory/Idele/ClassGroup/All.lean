/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivAdeleTopology
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivFiniteIntegral
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivIdeleClassTopology
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivTopology
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.BaseChange
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.ConnectedComponentQuotientCongr
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Core
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.InfiniteAlgEquiv
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibComparison
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.MathlibTopologyComparison
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormalClosureNorm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange

/-!
# Idelic class groups

Public aggregate for the ordinary ideal class quotient of the ideles and its
base-change, norm-comparison, tower, and algebra-equivalence constructions.
-/
