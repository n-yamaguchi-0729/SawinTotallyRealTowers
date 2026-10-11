/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.Galois.Ramification.Basic
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.Galois.Ramification.LocalTop
import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.Galois.Ramification.ValueImage

/-!
# Neu1999 Galois ramification image generators

This umbrella keeps the Galois ramification image source layer available under
the original import path.  The implementation is split into:

* `GaloisRamification.Basic`: embedded-base-unit subgroups, tower transport,
  powered lower-branch images, and their norm-down image;
* `GaloisRamification.ValueImage`: Galois valuation-data generators and exact
  value images for embedded and powered base-unit subgroups;
* `GaloisRamification.LocalTop`: lower local-top residue-degree comparisons
  forced by those powered images.
-/

/- Canonical aggregate for
TameRamification.ValueGroup.NonarchimedeanLocalField.Galois.Ramification. -/
