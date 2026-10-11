/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.StalkLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.RingTheory.RingHom.Flat

/-!
# Scalar sections after base change to a stalk

For a qcqs morphism whose structure-sheaf map is an isomorphism, flat base
change to the spectrum of a target stalk preserves the global-section map
as an isomorphism. The section pushout is computed on an affine neighborhood
of the chosen point.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- If the structure sheaf is the pushforward along a qcqs morphism, the
base change to a target stalk induces an isomorphism on global sections. -/
theorem isIso_appTop_pullback_fromSpecStalk_of_isIso_c
    {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [IsIso f.c] (y : S) :
    IsIso (pullback.snd f (S.fromSpecStalk y)).appTop := by
  let q : Spec (S.presheaf.stalk y) ⟶ S := S.fromSpecStalk y
  have hFlat : Flat q := by
    apply Flat.of_stalkMap q
    intro z
    have hIso : IsIso (q.stalkMap z) := S.isIso_fromSpecStalk_stalkMap y z
    exact RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso (q.stalkMap z))
  let U : S.Opens := (S.affineCover.f (S.affineCover.idx y)).opensRange
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hy : y ∈ U := S.affineCover.covers y
  have hqU : q ⁻¹ᵁ U = ⊤ := by
    apply Scheme.preimage_eq_top_of_closedPoint_mem q
    change S.fromSpecStalk y (IsLocalRing.closedPoint (S.presheaf.stalk y)) ∈ U
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hy
  have hUST : (⊤ : (Spec (S.presheaf.stalk y)).Opens) ≤ q ⁻¹ᵁ U := hqU.ge
  have hTop : (⊤ : (pullback f q).Opens) =
      pullback.fst f q ⁻¹ᵁ (f ⁻¹ᵁ U) ⊓ pullback.snd f q ⁻¹ᵁ ⊤ := by
    change ⊤ = (pullback.fst f q ≫ f) ⁻¹ᵁ U ⊓ pullback.snd f q ⁻¹ᵁ ⊤
    rw [pullback.condition]
    change ⊤ = pullback.snd f q ⁻¹ᵁ (q ⁻¹ᵁ U) ⊓ pullback.snd f q ⁻¹ᵁ ⊤
    rw [hqU, Scheme.Hom.preimage_top, inf_top_eq]
  have hSections := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right
    (IsPullback.of_hasPullback f q) hUST
    (show f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U from le_rfl) hTop hU
    (isAffineOpen_top (Spec (S.presheaf.stalk y)))
    (f.isCompact_preimage hU.isCompact) (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  have hPushout := (isIso_pushoutSection_iff
    (IsPullback.of_hasPullback f q) hUST
    (show f ⁻¹ᵁ U ≤ f ⁻¹ᵁ U from le_rfl) hTop).mp hSections
  have hApp : IsIso (f.appLE U (f ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.appLE_eq_app]
    exact NatIso.isIso_app_of_isIso f.c (Opposite.op U)
  have hResult := hPushout.isIso_inr_of_isIso
  have hAppTop : (pullback.snd f q).appTop =
      (pullback.snd f q).appLE ⊤ ⊤ le_top := (pullback.snd f q).app_eq_appLE
  change IsIso (pullback.snd f q).appTop
  rw [hAppTop]
  exact hResult

end AlgebraicGeometry
