/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.BaseNorm
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.FieldNormImage
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.Galois.All
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.GaloisInvariants
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.Invariants
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.ResidueDegree
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.Valuation

/-!
# Neu1999 local-field value images

This is the umbrella module for the Neu1999 specialization of the
tame Abhyankar value-group frontier.  The implementation is split into:

* `NAField.Valuation`: the normalized integer valuation and norm formula;
* `NAField.Invariants`: elementary `e * f = [L : K]` consequences;
* `NAField.BaseNorm`: concrete norm-subgroup elements from base units;
* `NAField.FieldNormImage`: field-norm value images and subgroup generator
  forms;
* `NAField.ResidueDegree`: concrete residue-degree divisibility;
* `NAField.GaloisInvariants`: field-degree identities for finite Galois valued
  extensions;
* `NAField.GaloisRamification`: ramification-index generators and powered
  lower-branch images from embedded base units in the finite Galois setting;
* `NAField.GaloisNormDown`: valuation images after applying `N_{L/K}` to the
  powered Galois ramification image;
* `NAField.GaloisNormDownPrimitive`: primitive residue-degree divisors
  extracted from those norm-down lcm sources;
* `NAField.GaloisNormDownLcm`: lower Galois residue-degree lcm value-step
  inclusions for the norm-down image.
-/

/- Canonical aggregate for TameRamification.ValueGroup.NonarchimedeanLocalField. -/
