/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_LocalRepresentabilityULift.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Earlier source notices recorded for the cited upstream material:
Copyright (c) 2024 Calle Sönne. All rights reserved.
Authors: Calle Sönne, Joël Riou, Ravi Vakil
https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/AlgebraicGeometry/Sites/Representability.lean

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.MorphismProperty.Representable
import Mathlib.AlgebraicGeometry.GluingOneHypercover
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Tactic.Simps.Basic
import Mathlib.Tactic.CategoryTheory.Reassoc
import Mathlib.Tactic.DSimpPercent
import Mathlib.Tactic.Conv
import Mathlib.CategoryTheory.Category.Basic

/-!
# Gluing schemes from locally representable open charts

Representable open charts for a sheaf determine scheme gluing data. The glued scheme
represents the sheaf through the universe-lifted Yoneda functor, with the chart maps giving
the local comparison and the induced Yoneda morphism an isomorphism.
-/

universe w v u

open CategoryTheory Category Limits Opposite

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (P : MorphismProperty C)

/-- The relative morphism property on presheaves defined using the universe-lifted
 Yoneda functor. -/
abbrev presheafULift : MorphismProperty (Cᵒᵖ ⥤ Type (max w v)) := P.relative uliftYoneda.{w}

variable {P}

lemma presheafULift_monomorphisms_le_monomorphisms :
    presheafULift.{w} (monomorphisms C) ≤ monomorphisms _ := fun F G f hf ↦ by
  suffices ∀ {X : C} {a b : uliftYoneda.{w}.obj X ⟶ F}, a ≫ f = b ≫ f → a = b from
    ⟨fun _ _ h ↦ hom_ext_uliftYoneda (fun _ _ ↦ this (by simp only [assoc, h]))⟩
  intro X a b h
  suffices hf.rep.lift (g := a ≫ f) a (𝟙 X) (by simp) =
      hf.rep.lift b (𝟙 X) (by simp [← h]) by
    simpa using uliftYoneda.{w}.congr_map this =≫ (hf.rep.fst (a ≫ f))
  have : Mono (hf.rep.snd (a ≫ f)) := hf.property_snd (a ≫ f)
  simp only [← cancel_mono (hf.rep.snd (a ≫ f)), Functor.relativelyRepresentable.lift_snd]

variable {G : Cᵒᵖ ⥤ Type (max w v)}

lemma presheafULift_mono_of_le (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : uliftYoneda.{w}.obj X ⟶ G} (hf : P.presheafULift f) : Mono f :=
  MorphismProperty.presheafULift_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone hP _ hf)

lemma fst'_self_eq_snd_ULift (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : uliftYoneda.{w}.obj X ⟶ G} (hf : P.presheafULift f) :
    hf.rep.fst' f = hf.rep.snd f := by
  have := presheafULift_mono_of_le hP hf
  apply uliftYoneda.{w}.map_injective
  rw [← cancel_mono f, (hf.rep.isPullback' f).w]

lemma isIso_fst'_self_ULift (hP : P ≤ MorphismProperty.monomorphisms C)
    {X : C} {f : uliftYoneda.{w}.obj X ⟶ G} (hf : P.presheafULift f) : IsIso (hf.rep.fst' f) :=
  have := presheafULift_mono_of_le hP hf
  have := (hf.rep.isPullback' f).isIso_fst_of_mono
  (ULiftYoneda.fullyFaithful C).isIso_of_isIso_map _

end CategoryTheory.MorphismProperty

namespace AlgebraicGeometry

namespace Scheme

variable (F : Sheaf Scheme.zariskiTopology.{u} (Type (max w u)))
  {ι : Type u} {X : ι → Scheme.{u}}
  (f : (i : ι) → uliftYoneda.{w}.obj (X i) ⟶ F.obj)
  (hf : ∀ i, MorphismProperty.presheafULift.{w} @IsOpenImmersion (f i))

namespace LocalRepresentabilityULift

variable {F f} (i j k : ι)

open Functor.relativelyRepresentable

private noncomputable def tripleRotation :
    pullback₃ (hf i).rep (f j) (f k) ⟶ pullback₃ (hf j).rep (f k) (f i) :=
  (hf j).rep.lift₃ (f k) (f i)
    (pullback₃.p₂ (hf i).rep (f j) (f k))
    (pullback₃.p₃ (hf i).rep (f j) (f k))
    (pullback₃.p₁ (hf i).rep (f j) (f k))
    ((pullback₃.map_p₂_comp (hf i).rep (f j) (f k)).trans
      (pullback₃.map_p₃_comp (hf i).rep (f j) (f k)).symm)
    ((pullback₃.map_p₂_comp (hf i).rep (f j) (f k)).trans
      (pullback₃.map_p₁_comp (hf i).rep (f j) (f k)).symm)

private lemma tripleRotation_p₁ :
    tripleRotation hf i j k ≫ pullback₃.p₁ (hf j).rep (f k) (f i) =
      pullback₃.p₂ (hf i).rep (f j) (f k) := by
  unfold tripleRotation
  exact lift₃_p₁ _ _ _ _ _ _ _ _

private lemma tripleRotation_p₂ :
    tripleRotation hf i j k ≫ pullback₃.p₂ (hf j).rep (f k) (f i) =
      pullback₃.p₃ (hf i).rep (f j) (f k) := by
  unfold tripleRotation
  exact lift₃_p₂ _ _ _ _ _ _ _ _

private lemma tripleRotation_p₃ :
    tripleRotation hf i j k ≫ pullback₃.p₃ (hf j).rep (f k) (f i) =
      pullback₃.p₁ (hf i).rep (f j) (f k) := by
  unfold tripleRotation
  exact lift₃_p₃ _ _ _ _ _ _ _ _

/-- The scheme gluing data obtained from the locally representable open charts and
 their pairwise pullbacks. -/
@[simps]
noncomputable def glueData : GlueData where
  J := ι
  U := X
  V := fun (i, j) ↦ (hf i).rep.pullback (f j)
  f i j := (hf i).rep.fst' (f j)
  f_mono i j :=
    have := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip
    IsOpenImmersion.mono _
  f_id i := MorphismProperty.isIso_fst'_self_ULift IsOpenImmersion.le_monomorphisms (hf i)
  t i j := (hf i).rep.symmetry (hf j).rep
  t_id i := by apply (hf i).rep.hom_ext' <;>
    simp [MorphismProperty.fst'_self_eq_snd_ULift IsOpenImmersion.le_monomorphisms (hf i)]
  t' i j k := tripleRotation hf i j k
  t_fac i j k := (hf j).rep.hom_ext'
    (by
      exact (Category.assoc _ _ _).trans
        ((congrArg (fun a : pullback₃ (hf j).rep (f k) (f i) ⟶ X j =>
            tripleRotation hf i j k ≫ a)
          (pullback₃.snd_fst'_eq_p₁ (hf j).rep (f k) (f i))).trans
          ((tripleRotation_p₁ hf i j k).trans
            (congrArg (fun a : (hf i).rep.pullback (f j) ⟶ X j =>
                pullback.fst ((hf i).rep.fst' (f j)) ((hf i).rep.fst' (f k)) ≫ a)
              ((hf i).rep.symmetry_fst (hf j).rep).symm))))
    (by
      exact (Category.assoc _ _ _).trans
        ((tripleRotation_p₃ hf i j k).trans
          (congrArg (fun a : (hf i).rep.pullback (f j) ⟶ X i =>
              pullback.fst ((hf i).rep.fst' (f j)) ((hf i).rep.fst' (f k)) ≫ a)
            ((hf i).rep.symmetry_snd (hf j).rep).symm)))
  cocycle i j k := by
    change tripleRotation hf i j k ≫ tripleRotation hf j k i ≫
      tripleRotation hf k i j = 𝟙 (pullback₃ (hf i).rep (f j) (f k))
    apply pullback₃.hom_ext
    · rw [Category.assoc, Category.assoc, tripleRotation_p₁,
        tripleRotation_p₂, tripleRotation_p₃, Category.id_comp]
    · rw [Category.assoc, Category.assoc, tripleRotation_p₂,
        tripleRotation_p₃, tripleRotation_p₁, Category.id_comp]
    · rw [Category.assoc, Category.assoc, tripleRotation_p₃,
        tripleRotation_p₁, tripleRotation_p₂, Category.id_comp]
  f_open i j := (hf j).property _ _ _ ((hf i).1.isPullback' (f j)).flip

/-- The canonical open immersion from a chart into the scheme obtained by gluing. -/
noncomputable def toGlued (i : ι) : X i ⟶ (glueData hf).glued :=
  (glueData hf).ι i

instance : IsOpenImmersion (toGlued hf i) :=
  GlueData.ι_isOpenImmersion (glueData hf) i


/-- The morphism from the universe-lifted Yoneda sheaf of the glued scheme, defined
 by gluing the given local chart sections. -/
noncomputable def uliftYonedaGluedToSheaf :
    (GrothendieckTopology.uliftYoneda.{w} zariskiTopology).obj (glueData hf).glued ⟶ F where
  hom := uliftYonedaEquiv.symm
    ((glueData hf).sheafValGluedMk (fun i ↦ uliftYonedaEquiv (f i)) (by
      intro (i : ι) (j : ι)
      change F.obj.map ((hf i).rep.fst' (f j)).op (uliftYonedaEquiv (f i)) =
        F.obj.map (((hf j).rep.fst' (f i)).op ≫
          ((hf i).rep.symmetry (hf j).rep).op) (uliftYonedaEquiv (f j))
      rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality]
      congr 1
      rw [← op_comp, Quiver.Hom.unop_op, Quiver.Hom.unop_op]
      erw [Functor.relativelyRepresentable.symmetry_fst, ((hf i).rep.isPullback' (f j)).w]))

@[reassoc (attr := simp)]
lemma uliftYoneda_toGlued_uliftYonedaGluedToSheaf (i : ι) :
    uliftYoneda.{w}.map (toGlued hf i) ≫ (uliftYonedaGluedToSheaf hf).hom = f i := by
  apply uliftYonedaEquiv.injective
  have h := uliftYonedaEquiv_naturality (uliftYonedaGluedToSheaf hf).hom (toGlued hf i).op
  rw [Quiver.Hom.unop_op] at h
  rw [← h]
  simp only [uliftYonedaGluedToSheaf, toGlued, Equiv.apply_symm_apply]
  exact GlueData.sheafValGluedMk_val _ _ _ _

@[simp]
lemma uliftYonedaGluedToSheaf_app_toGlued {i : ι} :
    dsimp% (uliftYonedaGluedToSheaf hf).hom.app (op (X i)) ⟨toGlued hf i⟩ =
      uliftYonedaEquiv (f i) := by
  exact (congrArg (fun a : ULift.{w} (X i ⟶ (glueData hf).glued) =>
      (uliftYonedaGluedToSheaf hf).hom.app (op (X i)) a)
    (uliftYonedaEquiv_uliftYoneda_map (toGlued hf i))).symm.trans
      ((uliftYonedaEquiv_comp (uliftYoneda.{w}.map (toGlued hf i))
        (uliftYonedaGluedToSheaf hf).hom).symm.trans
          (congrArg uliftYonedaEquiv
            (uliftYoneda_toGlued_uliftYonedaGluedToSheaf hf i)))

@[simp]
lemma uliftYonedaGluedToSheaf_app_comp {V U : Scheme.{u}} (γ : V ⟶ U)
    (α : U ⟶ (glueData hf).glued) :
    dsimp% (uliftYonedaGluedToSheaf hf).hom.app (op V) ⟨γ ≫ α⟩ =
      F.obj.map γ.op ((uliftYonedaGluedToSheaf hf).hom.app (op U) ⟨α⟩) :=
  ConcreteCategory.congr_hom ((uliftYonedaGluedToSheaf hf).hom.naturality γ.op) ⟨α⟩

/-- The map from the glued scheme is locally surjective when the original charts cover the sheaf. -/
instance instIsLocallySurjectiveUliftYonedaGluedToSheaf
    [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)] :
    Sheaf.IsLocallySurjective (uliftYonedaGluedToSheaf hf) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac _
    (show Sigma.desc (fun i ↦ uliftYoneda.{w}.map (toGlued hf i)) ≫
      (uliftYonedaGluedToSheaf hf).hom = Sigma.desc f by
        apply Sigma.hom_ext
        intro l
        exact (Category.assoc _ _ _).symm.trans
          ((congrArg (fun a : uliftYoneda.{w}.obj (X l) ⟶
              uliftYoneda.{w}.obj (glueData hf).glued ↦
            a ≫ (uliftYonedaGluedToSheaf hf).hom)
              (Sigma.ι_comp_desc (fun i ↦ uliftYoneda.{w}.map (toGlued hf i)) l)).trans
            ((uliftYoneda_toGlued_uliftYonedaGluedToSheaf hf l).trans
              (Sigma.ι_comp_desc f l).symm)))

lemma comp_toGlued_eq {U : Scheme.{u}} {i j : ι} (a : U ⟶ X i) (b : U ⟶ X j)
    (h : uliftYoneda.{w}.map a ≫ f i = uliftYoneda.{w}.map b ≫ f j) :
    a ≫ toGlued hf i = b ≫ toGlued hf j := by
  rw [← (hf i).rep.lift'_fst a b h, assoc]
  conv_rhs => rw [← (hf i).rep.lift'_snd a b h, assoc]
  congr 1
  exact ((glueData hf).glue_condition i j).symm.trans
    (by
      change (hf i).rep.symmetry (hf j).rep ≫ (hf j).rep.fst' (f i) ≫
        (glueData hf).ι j = (hf i).rep.snd (f j) ≫ (glueData hf).ι j
      exact Functor.relativelyRepresentable.symmetry_fst_assoc
        (hf i).rep (hf j).rep ((glueData hf).ι j))

@[simp]
lemma glueData_openCover_map : (glueData hf).openCover.f j = toGlued hf j := rfl

instance : Sheaf.IsLocallyInjective (uliftYonedaGluedToSheaf hf) where
  equalizerSieve_mem := by
    rintro ⟨U⟩ ⟨α⟩ ⟨β⟩ h
    replace h : (uliftYonedaGluedToSheaf hf).hom.app _ ⟨α⟩ =
        (uliftYonedaGluedToSheaf hf).hom.app _ ⟨β⟩ := h
    have mem := (glueData hf).openCover.mem_grothendieckTopology
    refine GrothendieckTopology.superset_covering _ ?_
      (zariskiTopology.intersection_covering (zariskiTopology.pullback_stable α mem)
        (zariskiTopology.pullback_stable β mem))
    rintro V (γ : _ ⟶ U) ⟨⟨W₁, a, _, ⟨i⟩, fac₁⟩, ⟨W₂, b, _, ⟨j⟩, fac₂⟩⟩
    change V ⟶ X i at a
    change V ⟶ X j at b
    change a ≫ toGlued hf i = γ ≫ α at fac₁
    change b ≫ toGlued hf j = γ ≫ β at fac₂
    change ULift.up (γ ≫ α) = ULift.up (γ ≫ β)
    replace h : (uliftYonedaGluedToSheaf hf).hom.app _ ⟨γ ≫ α⟩ =
        (uliftYonedaGluedToSheaf hf).hom.app _ ⟨γ ≫ β⟩ := by
      dsimp at h; simp [h]
    rw [← fac₁, ← fac₂] at h ⊢
    apply congrArg ULift.up
    apply comp_toGlued_eq
    have hi := (uliftYonedaGluedToSheaf_app_comp hf a (toGlued hf i)).trans
      (congrArg (fun t => F.obj.map a.op t)
        (uliftYonedaGluedToSheaf_app_toGlued hf (i := i)))
    have hj := (uliftYonedaGluedToSheaf_app_comp hf b (toGlued hf j)).trans
      (congrArg (fun t => F.obj.map b.op t)
        (uliftYonedaGluedToSheaf_app_toGlued hf (i := j)))
    have hmap := hi.symm.trans (h.trans hj)
    apply uliftYonedaEquiv.{w}.injective
    have ha := uliftYonedaEquiv_naturality (X := op (X i)) (f i) a.op
    have hb := uliftYonedaEquiv_naturality (X := op (X j)) (f j) b.op
    exact ha.symm.trans (hmap.trans hb)

variable [Presheaf.IsLocallySurjective Scheme.zariskiTopology (Sigma.desc f)]

instance : IsIso (uliftYonedaGluedToSheaf hf) := by
  rw [← Sheaf.isLocallyBijective_iff_isIso (uliftYonedaGluedToSheaf hf)]
  constructor <;> infer_instance

/-- The isomorphism identifying the given sheaf with the universe-lifted Yoneda sheaf
 of the glued scheme. -/
noncomputable def uliftYonedaIsoSheaf :
    (GrothendieckTopology.uliftYoneda.{w} zariskiTopology).obj (glueData hf).glued ≅ F :=
  asIso (uliftYonedaGluedToSheaf hf)

/-- The representation of the underlying presheaf by the scheme obtained by gluing
 its open charts. -/
noncomputable def representableBy : F.obj.RepresentableBy (glueData hf).glued :=
  (Functor.RepresentableBy.equivUliftYonedaIso.{w} _ _).symm
    ((sheafToPresheaf _ _).mapIso (uliftYonedaIsoSheaf hf))

include hf in
theorem isRepresentable : F.obj.IsRepresentable :=
  ⟨_, ⟨representableBy hf⟩⟩

end LocalRepresentabilityULift

end Scheme

end AlgebraicGeometry
