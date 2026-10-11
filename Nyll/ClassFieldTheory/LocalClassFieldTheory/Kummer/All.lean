/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.CanonicalKummerNorm
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.KummerExponentTower
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.KummerNormPowerClassDegree
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertExponentCompatibility
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairing
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertPairingNondegeneracy
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbol
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.LocalHilbertSymbolLaws
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.MathlibHilbertPairing
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.MaximalLocalKummerPairing
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.PowerResidueTameFormula
import Nyll.ClassFieldTheory.LocalClassFieldTheory.Kummer.SmallHilbertPairingTransport

/-!
# Local Kummer reciprocity

Aggregate for the local Hilbert symbol, its laws, and the maximal local Kummer
pairing, including the tame power-residue formula.
-/
