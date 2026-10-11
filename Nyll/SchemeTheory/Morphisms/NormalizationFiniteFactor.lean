/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Finite open factors in a normalization fiber

For a quasi-finite separated morphism of finite type, Zariski's main theorem
embeds its source into its relative normalization. After arbitrary base change,
an open subscheme finite over the new base is both open and closed in the
base change of that normalization. The map into the normalization fiber is
constructed from the canonical normalization map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S Z T : Scheme.{u}} (f : X ⟶ S) (g : Z ⟶ S)
    [QuasiCompact f] [IsSeparated f]

/-- The base change of the canonical map into the relative normalization. -/
def normalizationBaseChange :
    pullback f g ⟶ pullback f.fromNormalization g :=
  pullback.map f g f.fromNormalization g f.toNormalization (𝟙 Z) (𝟙 S)
    ((Category.comp_id f).trans f.toNormalization_fromNormalization.symm)
    ((Category.comp_id g).trans (Category.id_comp g).symm)

@[reassoc (attr := simp)]
lemma normalizationBaseChange_fst :
    normalizationBaseChange f g ≫ pullback.fst f.fromNormalization g =
      pullback.fst f g ≫ f.toNormalization :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma normalizationBaseChange_snd :
    normalizationBaseChange f g ≫ pullback.snd f.fromNormalization g =
      pullback.snd f g := by
  simp only [normalizationBaseChange, pullback.map, pullback.lift_snd, Category.comp_id]

instance isOpenImmersion_normalizationBaseChange
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] :
    IsOpenImmersion (normalizationBaseChange f g) := by
  exact MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    (f := f) (g := g) (f' := f.fromNormalization) (g' := g)
    (inferInstance : IsOpenImmersion f.toNormalization)
    (inferInstance : IsOpenImmersion (𝟙 Z))
    f.toNormalization_fromNormalization.symm (Category.id_comp g).symm

/-- An open factor of the base-changed source maps canonically into the
base change of the relative normalization. -/
def normalizationFiniteFactor (i : T ⟶ pullback f g) :
    T ⟶ pullback f.fromNormalization g :=
  i ≫ normalizationBaseChange f g

@[reassoc (attr := simp)]
lemma normalizationFiniteFactor_fst (i : T ⟶ pullback f g) :
    normalizationFiniteFactor f g i ≫ pullback.fst f.fromNormalization g =
      i ≫ pullback.fst f g ≫ f.toNormalization := by
  rw [normalizationFiniteFactor, Category.assoc, normalizationBaseChange_fst]

@[reassoc (attr := simp)]
lemma normalizationFiniteFactor_snd (i : T ⟶ pullback f g) :
    normalizationFiniteFactor f g i ≫ pullback.snd f.fromNormalization g =
      i ≫ pullback.snd f g := by
  rw [normalizationFiniteFactor, Category.assoc, normalizationBaseChange_snd]

instance isOpenImmersion_normalizationFiniteFactor
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (i : T ⟶ pullback f g) [IsOpenImmersion i] :
    IsOpenImmersion (normalizationFiniteFactor f g i) := by
  unfold normalizationFiniteFactor
  infer_instance

/-- Finiteness over the base implies finiteness of the map into the
normalization fiber, since that fiber is separated over the base. -/
instance isFinite_normalizationFiniteFactor (i : T ⟶ pullback f g)
    [IsFinite (i ≫ pullback.snd f g)] :
    IsFinite (normalizationFiniteFactor f g i) := by
  have : IsFinite
      (normalizationFiniteFactor f g i ≫ pullback.snd f.fromNormalization g) := by
    rw [normalizationFiniteFactor_snd]
    infer_instance
  exact IsFinite.of_comp (normalizationFiniteFactor f g i)
    (pullback.snd f.fromNormalization g)

/-- A finite open factor is closed in the normalization fiber. -/
instance isClosedImmersion_normalizationFiniteFactor
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (i : T ⟶ pullback f g) [IsOpenImmersion i]
    [IsFinite (i ≫ pullback.snd f g)] :
    IsClosedImmersion (normalizationFiniteFactor f g i) :=
  (IsClosedImmersion.iff_isFinite_and_mono _).mpr ⟨inferInstance, inferInstance⟩

/-- The canonical image of a finite open factor is a clopen subset of the
normalization fiber. -/
lemma isClopen_range_normalizationFiniteFactor
    [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (i : T ⟶ pullback f g) [IsOpenImmersion i]
    [IsFinite (i ≫ pullback.snd f g)] :
    IsClopen (Set.range (normalizationFiniteFactor f g i)) :=
  ⟨(normalizationFiniteFactor f g i).isClosedEmbedding.isClosed_range,
    IsOpenImmersion.isOpen_range (normalizationFiniteFactor f g i)⟩

end AlgebraicGeometry.Scheme.Hom
