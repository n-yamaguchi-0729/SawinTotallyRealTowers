/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from the definitions at pinned revision
aa2d8b34692b16c70f699536de0d8e75b9a3e9ef:
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_GradedOAlgebraSectionRing.lean
Upstream NOTICE and per-file ATTRIBUTION (including earlier FLT and Mathlib notices):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md
See SchemeTheory/ANTHROPIC_FLT_SOURCE.md for retained notices.

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.PullbackMonoidal
import Nyll.SchemeTheory.Modules.TensorPowers

/-!
# Canonical comparisons for tensor powers of module sheaves

Tensor powers add under tensor product, transport along an isomorphism, and commute
with pullback. Each comparison is constructed recursively from the monoidal structure.
-/

noncomputable section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Tensoring powers of degrees `m` and `n` gives the power of degree `m + n`. -/
def tensorPowAdd (L : X.Modules) (m : ℕ) :
    (n : ℕ) → (L.tensorPow m ⊗ L.tensorPow n ≅ L.tensorPow (m + n))
  | 0 => ρ_ (L.tensorPow m)
  | n + 1 =>
    (α_ (L.tensorPow m) (L.tensorPow n) L).symm ≪≫ whiskerRightIso (tensorPowAdd L m n) L

/-- Transport a tensor power along an isomorphism of its module sheaf. -/
def tensorPowMapIso {L₁ L₂ : X.Modules} (e : L₁ ≅ L₂) :
    (n : ℕ) → (L₁.tensorPow n ≅ L₂.tensorPow n)
  | 0 => Iso.refl _
  | n + 1 => tensorIso (tensorPowMapIso e n) e

/-- Pullback commutes with tensor powers through its canonical monoidal comparison. -/
def pullbackTensorPowIso {Y : Scheme.{u}} (c : X ⟶ Y) (L : Y.Modules) :
    (n : ℕ) → ((Modules.pullback c).obj (L.tensorPow n) ≅
      ((Modules.pullback c).obj L).tensorPow n)
  | 0 => pullbackTensorUnitObjIso c
  | n + 1 => pullbackTensorObjIso c (L.tensorPow n) L ≪≫
      whiskerRightIso (pullbackTensorPowIso c L n) ((Modules.pullback c).obj L)

end AlgebraicGeometry.Scheme.Modules
