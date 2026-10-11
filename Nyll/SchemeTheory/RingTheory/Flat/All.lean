/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Flat.LocalCriterion
import Nyll.SchemeTheory.RingTheory.Flat.GenericFlatness
import Nyll.SchemeTheory.RingTheory.Flat.OpenLocus
import Nyll.SchemeTheory.RingTheory.Flat.FiniteSubalgebraLocalization
import Nyll.SchemeTheory.RingTheory.Flat.FiniteSubalgebra

import Nyll.SchemeTheory.RingTheory.Flat.Kernel
import Nyll.SchemeTheory.RingTheory.Flat.TensorInjectivity
import Nyll.SchemeTheory.RingTheory.Flat.TensorExactness
/-!
# Flatness criteria and finite models

This aggregate exposes local flatness criteria, generic flatness, openness of the flat
locus, and finite-subalgebra models.
-/

/- Canonical aggregate for general flatness. -/
