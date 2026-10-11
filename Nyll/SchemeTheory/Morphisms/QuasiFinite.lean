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

import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.RingTheory.Unramified.LocalStructure
import Mathlib.Tactic.Algebraize

/-!
# Quasi-finiteness from formal unramifiedness

A formally unramified morphism locally of finite type is locally quasi-finite.
-/

section ProofImplementation


namespace AlgebraicCurves.Geometry.Schemes.Proofs
namespace LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType

open AlgebraicGeometry CategoryTheory

theorem _root_.AlgebraicGeometry.LocallyQuasiFinite.of_formallyUnramified_of_locallyOfFiniteType
    {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y)
    [AlgebraicGeometry.FormallyUnramified f] [AlgebraicGeometry.LocallyOfFiniteType f] :
    AlgebraicGeometry.LocallyQuasiFinite f := by
  rw [locallyQuasiFinite_iff]
  intro U hU V hV e
  have hu : (f.appLE U V e).hom.FormallyUnramified := f.formallyUnramified_appLE hU hV e
  have hft : (f.appLE U V e).hom.FiniteType := f.finiteType_appLE hU hV e
  algebraize [(f.appLE U V e).hom]
  exact inferInstanceAs (Algebra.QuasiFinite Γ(Y, U) Γ(X, V))
end LocallyQuasiFinite_of_formallyUnramified_of_locallyOfFiniteType
end AlgebraicCurves.Geometry.Schemes.Proofs
end ProofImplementation
