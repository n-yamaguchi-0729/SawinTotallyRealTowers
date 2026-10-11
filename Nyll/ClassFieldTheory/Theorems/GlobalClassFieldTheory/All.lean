/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianGlobalReciprocity
import Nyll.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianGlobalReciprocityQuotient
import Nyll.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FiniteAbelianReciprocityQuotientEquivMk
import Nyll.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceLocalGlobalNormKernel
import Nyll.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinNormKernel
import Nyll.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinDecomposition
import Nyll.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceCompletionLocalArtin
import Nyll.ClassFieldTheory.Theorems.GlobalClassFieldTheory.FinitePlaceRayArtinLocalValue
import Nyll.ClassFieldTheory.Theorems.GlobalClassFieldTheory.TopologicalGlobalReciprocity
import Nyll.ClassFieldTheory.Theorems.GlobalClassFieldTheory.MaximalAbelianGlobalArtin

/-!
# Global class field theory

This module collects finite ideal-theoretic reciprocity and the topological
maximal-abelian statements. The latter are proved via topological comparison
with the existing restricted-product implementation.
-/
