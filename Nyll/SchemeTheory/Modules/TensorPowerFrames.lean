/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Modules.TensorFrames
import Nyll.SchemeTheory.Modules.TensorSections

/-!
# Scheme Modules Is Frame On tensor Pow Section monoidal V2
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs
namespace Scheme_Modules_IsFrameOn_tensorPowSection_monoidalV2

universe u


open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry


theorem _root_.AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorPowSection_monoidalV2 {X :
  AlgebraicGeometry.Scheme.{u}} {L : X.Modules} {U V : X.Opens} {s : Γ(L, U)}
    (hs : AlgebraicGeometry.Scheme.Modules.IsFrameOn s V) (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.IsFrameOn
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s n) V := by
  induction n with
  | zero => exact AlgebraicGeometry.Scheme.Modules.isFrameOn_unitSection V
  | succ n ih =>
    rw [AlgebraicGeometry.Scheme.Modules.tensorPowSection_succ]
    exact AlgebraicGeometry.Scheme.Modules.IsFrameOn.tensorSections_monoidalV2 ih hs
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_IsFrameOn_tensorPowSection_monoidalV2
end ProofImplementation
