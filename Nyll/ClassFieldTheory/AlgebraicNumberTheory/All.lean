/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Adele.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.CompositumEmbedding
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.FiniteAbelianCompositum
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceAdicCompletionCongrEquiv
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivTopology
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NormalClosure
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.PowerResidueSymbols.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.QuadraticReciprocity
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Ramification.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.RayClass.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SUnit.All
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.SeparableClosureEmbedding
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.TensorProduct

/-!
# Algebraic number theory

Public root for the reusable global algebraic-number-theory layer used by
class field theory. It exports finite abelian composita, idèles and idèle
classes in extensions, normal-closure and splitting results, ray class groups,
S-units, and the ramification and degree results needed by global applications.
-/
