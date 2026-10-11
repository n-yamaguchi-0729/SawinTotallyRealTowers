/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Nyll.SchemeTheory.FiniteEtale.Basic
import Nyll.SchemeTheory.Normalization.IntegralOpen


/-!
# Normalization and finite-etale covers of open subschemes

Let `U ⟶ X` be an open immersion and let `W ⟶ U` be finite etale.
The relative normalization of `X` in the composite `W ⟶ X`, restricted
back to `U`, is canonically isomorphic to `W`.  This comparison does not
assert that the normalization is etale over all of `X`; that is the separate
purity step.
-/

noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.FiniteEtale

universe u

variable {X U : Scheme.{u}}

private theorem compOpenImmersionQuasiCompact
    [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (W : FiniteEtale U) :
    QuasiCompact (W.hom ≫ j) := by
  have hW : QuasiCompact W.hom := inferInstance
  have hj : QuasiCompact j := inferInstance
  exact @quasiCompact_comp W.left U X W.hom j hW hj

private theorem compOpenImmersionQuasiSeparated
    (j : U ⟶ X) [IsOpenImmersion j] (W : FiniteEtale U) :
    QuasiSeparated (W.hom ≫ j) := by
  have hW : QuasiSeparated W.hom := inferInstance
  have hj : QuasiSeparated j := inferInstance
  exact @quasiSeparated_comp W.left U X W.hom j hW hj

attribute [local instance] compOpenImmersionQuasiCompact
  compOpenImmersionQuasiSeparated

private theorem coverCompOpenImmersionIsPullback
    (j : U ⟶ X) [IsOpenImmersion j] (W : FiniteEtale U) :
    IsPullback (𝟙 W.left) W.hom (W.hom ≫ j) j := by
  have hj : Mono j := inferInstance
  exact @IsPullback.of_horiz_isIso_mono _ _ W.left W.left U X
    (𝟙 W.left) W.hom (W.hom ≫ j) j inferInstance hj ⟨rfl⟩

/-- A finite-etale cover of an open subscheme is canonically unchanged by
pulling its composite to the ambient scheme back to that open subscheme. -/
noncomputable def coverCompOpenImmersionPullbackIso
    (j : U ⟶ X) [IsOpenImmersion j] (W : FiniteEtale U) :
    W.left ≅ Limits.pullback (W.hom ≫ j) j :=
  (coverCompOpenImmersionIsPullback j W).isoPullback

@[reassoc (attr := simp)]
lemma coverCompOpenImmersionPullbackIso_hom_snd
    (j : U ⟶ X) [IsOpenImmersion j] (W : FiniteEtale U) :
    (coverCompOpenImmersionPullbackIso j W).hom ≫
        pullback.snd (W.hom ≫ j) j = W.hom :=
  (coverCompOpenImmersionIsPullback j W).isoPullback_hom_snd

local instance finiteEtaleRespectsIso :
    MorphismProperty.RespectsIso
      (@IsFiniteEtale : MorphismProperty Scheme.{u}) := by
  apply MorphismProperty.RespectsIso.mk
  · intro _ _ _ _ f hf
    let : IsFinite f := hf.toIsFinite
    let : Etale f := hf.toEtale
    exact @IsFiniteEtale.mk _ _ _ inferInstance inferInstance
  · intro _ _ _ _ f hf
    let : IsFinite f := hf.toIsFinite
    let : Etale f := hf.toEtale
    exact @IsFiniteEtale.mk _ _ _ inferInstance inferInstance

private theorem pullbackSndCompOpenImmersionFiniteEtale
    (j : U ⟶ X) [IsOpenImmersion j] (W : FiniteEtale U) :
    IsFiniteEtale (pullback.snd (W.hom ≫ j) j) := by
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
    (coverCompOpenImmersionPullbackIso j W).hom _).mp
  rw [coverCompOpenImmersionPullbackIso_hom_snd]
  exact W.prop

/-- The cover over `U` is canonically isomorphic to the pullback to `U` of
the relative normalization of `X` in the composite cover `W ⟶ X`.

Local Noetherianity supplies quasi-compactness of the open immersion, which
is the only finiteness input needed to form the relative normalization. -/
noncomputable def openImmersionNormalizationIso
    [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (W : FiniteEtale U) :
    W.left ≅ Limits.pullback (W.hom ≫ j).fromNormalization j :=
  Scheme.Hom.integralOpenNormalizationIso W.hom j

@[reassoc (attr := simp)]
lemma openImmersionNormalizationIso_hom_snd
    [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (W : FiniteEtale U) :
    (openImmersionNormalizationIso j W).hom ≫
        pullback.snd (W.hom ≫ j).fromNormalization j =
      W.hom :=
  Scheme.Hom.integralOpenNormalizationIso_hom_snd W.hom j

/-- The restriction of the relative normalization to the original open is
finite etale. -/
lemma openImmersion_pullback_fromNormalization_isFiniteEtale
    [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (W : FiniteEtale U) :
    IsFiniteEtale (pullback.snd (W.hom ≫ j).fromNormalization j) := by
  let e := openImmersionNormalizationIso j W
  apply (MorphismProperty.cancel_left_of_respectsIso
    (P := (@IsFiniteEtale : MorphismProperty Scheme.{u})) e.hom _).mp
  rw [openImmersionNormalizationIso_hom_snd]
  exact W.prop

/-- The pullback to `U` of the relative normalization, packaged as a finite
etale object over `U`. -/
noncomputable def normalizationRestriction
    [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (W : FiniteEtale U) : FiniteEtale U :=
  @FiniteEtale.mk U _
    (pullback.snd (W.hom ≫ j).fromNormalization j)
    (openImmersion_pullback_fromNormalization_isFiniteEtale j W)

/-- The original finite-etale cover is isomorphic, over `U`, to the
restriction of the relative normalization. -/
noncomputable def normalizationRestrictionIso
    [IsLocallyNoetherian X]
    (j : U ⟶ X) [IsOpenImmersion j] (W : FiniteEtale U) :
    W ≅ normalizationRestriction j W :=
  MorphismProperty.Over.isoMk (openImmersionNormalizationIso j W)
    (openImmersionNormalizationIso_hom_snd j W)

end AlgebraicGeometry.FiniteEtale
