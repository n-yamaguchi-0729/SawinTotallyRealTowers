/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.ConnectedOfGlobalSections
import Nyll.SchemeTheory.Affine.FlatBaseChangeAffinization
import Mathlib.AlgebraicGeometry.Geometrically.Connected

/-!
# Geometric connectedness from scalar global sections

If a qcqs scheme over a field has exactly the base field as its global
sections through the actual structure map, it is geometrically connected.
Every extension of the base field is flat, so flat base change preserves
the sections isomorphism and the idempotent argument applies after each
field extension. This supplies the geometric step for normalization fibres
once their actual section maps have been computed.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- A qcqs scheme over a field is geometrically connected if its structure
morphism induces an isomorphism on global sections. -/
lemma geometricallyConnected_of_isIso_appTop_to_field
    {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K))
    [QuasiCompact f] [QuasiSeparated f] [IsIso f.appTop] :
    GeometricallyConnected f := by
  refine ⟨geometrically_iff_of_isClosedUnderIsomorphisms.mpr ?_⟩
  intro L _ g
  have hSections := isPushout_appTop_of_flat f g
  have : IsIso (pullback.snd f g).appTop := hSections.isIso_inr_of_isIso
  exact connectedSpace_of_isIso_appTop_to_field (pullback.snd f g)

end AlgebraicGeometry
