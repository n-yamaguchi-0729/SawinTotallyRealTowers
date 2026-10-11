/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.KroneckerWeber.LocalCyclotomicEmbedding
import Nyll.ClassFieldTheory.KroneckerWeber.RationalCyclotomicArithmeticReciprocity
import Nyll.ClassFieldTheory.KroneckerWeber.Final
import Nyll.ClassFieldTheory.KroneckerWeber.GlobalCompositumCyclotomicTarget
import Nyll.ClassFieldTheory.KroneckerWeber.GlobalCompositumGlobalEmbedding
import Nyll.ClassFieldTheory.KroneckerWeber.GlobalCompositumLeftFactors
import Nyll.ClassFieldTheory.KroneckerWeber.GlobalCompositumLocalizationEmbedding
import Nyll.ClassFieldTheory.KroneckerWeber.GlobalCompositumValuationInertiaBound
import Nyll.ClassFieldTheory.KroneckerWeber.GlobalCompositumValuedEmbedding
import Nyll.ClassFieldTheory.KroneckerWeber.GlobalPadicPrimePowInertiaBound
import Nyll.ClassFieldTheory.KroneckerWeber.RationalRayClassFieldCyclotomic
import Nyll.ClassFieldTheory.KroneckerWeber.RayClassComparison
import Nyll.ClassFieldTheory.KroneckerWeber.Setup
import Nyll.ClassFieldTheory.KroneckerWeber.UnramifiedCompositumSupport

/-!
# Kronecker--Weber

The reader-facing entry point for the local and global Kronecker--Weber
theorems.  Importing this module exposes both supported endpoints.
-/

/-!
# The global Kronecker--Weber theorem

Every finite abelian extension of `ℚ` is contained in a cyclotomic field.
The arithmetic construction and global degree estimate are kept in the
semantic support modules under `KroneckerWeber.Global`; this root exposes the
canonical theorem statement.
-/

noncomputable section

namespace KroneckerWeber

/-- **Global Kronecker--Weber.**

Every finite abelian extension of `ℚ` embeds in `ℚ(ζₙ)` for some positive
integer `n`.  Here `CyclotomicField n ℚ` is the concrete model of
`ℚ(ζₙ)`. -/
theorem exists_cyclotomicEmbedding
    (L : Type) [Field L] [NumberField L] [IsAbelianGalois ℚ L] :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (L →ₐ[ℚ] CyclotomicField n ℚ) :=
  ⟨kroneckerWeberConductorCandidate (L := L),
    kroneckerWeberConductorCandidate_pos (L := L),
    ⟨kroneckerWeberCyclotomicEmbedding (L := L)⟩⟩

end KroneckerWeber

end
