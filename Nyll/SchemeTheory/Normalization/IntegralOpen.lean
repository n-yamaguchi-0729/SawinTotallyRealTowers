/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic


/-!
# Extending an integral morphism from a quasi-compact open

Let `p : Z ⟶ V` be integral and `j : V ⟶ Y` a quasi-compact open immersion.
The relative normalization of `Y` in `p ≫ j` restricts over `V` to `Z`.
The canonical normalization map embeds `Z` as exactly the inverse image
of the original open.

This generalizes the existing normalization core in `FiniteEtaleOpen`.
That file retains its finite-étale/Noetherian compatibility interface.
No Noetherian, finite-type or étale hypothesis on `p` is used here. The
construction is the integral-extension step of Stacks Project, Tag 09Z0;
it does not construct a finite-presentation approximation.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

variable {Z V Y : Scheme.{u}} (p : Z ⟶ V) [IsIntegralHom p]
  (j : V ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]

/-- The original integral scheme is the actual restriction of its relative
normalization to the open subscheme on which it was defined. -/
def integralOpenNormalizationIso :
    Z ≅ pullback (p ≫ j).fromNormalization j := by
  let sq : IsPullback (𝟙 Z) p (p ≫ j) j :=
    IsPullback.of_horiz_isIso_mono ⟨Category.id_comp (p ≫ j)⟩
  let q : pullback (p ≫ j) j ⟶ V := pullback.snd (p ≫ j) j
  have hq : IsIntegralHom q := by
    have he : q = sq.isoPullback.inv ≫ p := sq.isoPullback_inv_snd.symm
    rw [he]
    infer_instance
  exact sq.isoPullback ≪≫ asIso q.toNormalization ≪≫
    asIso ((p ≫ j).normalizationPullback j)

/-- The comparison preserves the original integral projection to the open. -/
@[reassoc]
theorem integralOpenNormalizationIso_hom_snd :
    (integralOpenNormalizationIso p j).hom ≫
      pullback.snd (p ≫ j).fromNormalization j = p := by
  simp only [integralOpenNormalizationIso, Iso.trans_hom, asIso_hom, Category.assoc,
    normalizationPullback_snd, toNormalization_fromNormalization,
    IsPullback.isoPullback_hom_snd]

/-- The other projection is the actual canonical normalization map. -/
@[reassoc]
theorem integralOpenNormalizationIso_hom_fst :
    (integralOpenNormalizationIso p j).hom ≫
      pullback.fst (p ≫ j).fromNormalization j = (p ≫ j).toNormalization := by
  simp only [integralOpenNormalizationIso, Iso.trans_hom, asIso_hom, Category.assoc,
    toNormalization_normalizationPullback_fst,
    IsPullback.isoPullback_hom_fst_assoc, Category.id_comp]

/-- The integral morphism extends to the ambient scheme with the original
source as an actual open subscheme of the extension. -/
theorem isOpenImmersion_toNormalization_integral_open :
    IsOpenImmersion (p ≫ j).toNormalization := by
  rw [← integralOpenNormalizationIso_hom_fst p j]
  infer_instance

/-- The open source is precisely the preimage of the original open under
the extended integral morphism. -/
theorem range_toNormalization_integral_open :
    Set.range (p ≫ j).toNormalization =
      (p ≫ j).fromNormalization ⁻¹' Set.range j := by
  exact (range_eq_range_of_surjective (p ≫ j).toNormalization
      (pullback.fst (p ≫ j).fromNormalization j)
      (integralOpenNormalizationIso p j).hom (integralOpenNormalizationIso_hom_fst p j)).trans
    (Scheme.Pullback.range_fst (p ≫ j).fromNormalization j)

end AlgebraicGeometry.Scheme.Hom
