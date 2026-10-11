/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.EmbeddingNorm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisDescent
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisNorm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdealClass
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleClassBaseChange
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNormComponents
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.InfiniteOnePlaceBaseNorm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalComponent
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.LocalNorm
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormLocalOrder
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.NormProperties
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.OnePlaceBaseNorm

/-!
# Ideles in finite extensions of number fields

Public aggregate for base change, extension, and norm maps on ideles and
idele classes.
-/
