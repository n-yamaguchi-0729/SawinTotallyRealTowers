/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Basic
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.CompositumUnramified
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.Conjugation
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFieldTower
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFieldUnramified
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.FixedFields
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.NumberFieldPrimes
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.OrbitCardinality
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.PrimeContractions
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.TowerInvariants
import Nyll.ValuedFieldTheory.Ramification.HilbertRamification.Dedekind.ValuedGalois

/-!
# Hilbert ramification over Dedekind domains

This aggregate exposes prime contractions, decomposition and fixed fields, conjugation,
orbit cardinalities, and valued Galois comparisons in Dedekind extensions.
-/
