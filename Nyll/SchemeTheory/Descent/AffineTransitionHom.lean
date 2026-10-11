/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-!
# Morphisms between models over an inverse limit

For a cofiltered diagram of qcqs schemes with affine transition maps, a
morphism between two base-changed models descends to an actual stage. The
source model is qcqs over the base and the target is locally of finite
presentation. All base changes are the native chosen pullbacks, and the
recovery assertion is the literal commuting square between them.

This supplies the morphism and eventual-equality parts of Stacks 01ZM for the finite-etale limit
theorem 0BTV. It does not assert descent of objects or eventual finiteness
or etaleness. No integrality or Noetherian condition on the diagram is used.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.AffineTransitionHom

variable {I : Type u} [Category.{u} I] {S Y Z : Scheme.{u}}
    (D : I ⥤ Over S) (c : Cone D)

/-- The actual pullbacks of a model along the coefficient diagram. -/
abbrev diagram (f : Y ⟶ S) : I ⥤ Scheme.{u} where
  obj i := pullback (D.obj i).hom f
  map h := ((Over.pullback f).map (D.map h)).left
  map_id i := (D ⋙ Over.pullback f ⋙ Over.forget Y).map_id i
  map_comp h k := (D ⋙ Over.pullback f ⋙ Over.forget Y).map_comp h k

/-- The actual pullback of the limiting coefficient scheme and its maps to
the stage pullbacks. -/
abbrev cone (f : Y ⟶ S) : Cone (diagram D f) where
  pt := pullback c.pt.hom f
  π :=
    { app i := ((Over.pullback f).map (c.π.app i)).left
      naturality _ _ h :=
        ((Over.pullback f ⋙ Over.forget Y).mapCone c).π.naturality h }

/-- The structure maps of the pullback diagram to its original base. -/
def projection (f : Y ⟶ S) : diagram D f ⟶ (Functor.const I).obj S where
  app i := pullback.snd (D.obj i).hom f ≫ f
  naturality i j h := by
    change ((Over.pullback f).map (D.map h)).left ≫
        (pullback.snd (D.obj j).hom f ≫ f) =
      (pullback.snd (D.obj i).hom f ≫ f) ≫ 𝟙 S
    have hw : ((Over.pullback f).map (D.map h)).left ≫
        pullback.snd (D.obj j).hom f = pullback.snd (D.obj i).hom f :=
      Over.w ((Over.pullback f).map (D.map h))
    rw [Category.comp_id, ← Category.assoc, hw]

/-- Cone maps commute with the projection to the original model. -/
theorem cone_map_snd (f : Y ⟶ S) (i : I) :
    (cone D c f).π.app i ≫ pullback.snd (D.obj i).hom f =
      pullback.snd c.pt.hom f :=
  Over.w ((Over.pullback f).map (c.π.app i))

/-- Cone maps commute with the actual coefficient map. -/
theorem cone_map_fst (f : Y ⟶ S) (i : I) :
    (cone D c f).π.app i ≫ pullback.fst (D.obj i).hom f =
      pullback.fst c.pt.hom f ≫ (c.π.app i).left :=
  pullback.lift_fst _ _ _

/-- Base change preserves this limit; forgetting the structure map preserves
it because the indexing category is connected. -/
def coneIsLimit [IsCofiltered I] (hc : IsLimit c) (f : Y ⟶ S) :
    IsLimit (cone D c f) := by
  have : IsConnected I := IsCofiltered.isConnected I
  exact isLimitOfPreserves (Over.pullback f ⋙ Over.forget Y) hc

/-- Every transition in the pulled-back diagram is the base change of the
original affine transition. -/
theorem diagram_map_isAffineHom (f : Y ⟶ S)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h).left]
    {i j : I} (h : i ⟶ j) : IsAffineHom ((diagram D f).map h) :=
  MorphismProperty.overPullbackMap
    (P := (show MorphismProperty Scheme.{u} from @IsAffineHom))
    f (D.map h) inferInstance

/-- The source-model quasi-compactness supplies quasi-compact stage pullbacks. -/
theorem diagram_obj_compactSpace (f : Y ⟶ S) [QuasiCompact f]
    [∀ i : I, CompactSpace (D.obj i).left] (i : I) :
    CompactSpace ((diagram D f).obj i) :=
  inferInstanceAs (CompactSpace (pullback (D.obj i).hom f : Scheme.{u}))

/-- The source-model quasi-separatedness supplies quasi-separated stage
pullbacks over the original qcqs coefficient schemes. -/
theorem diagram_obj_quasiSeparatedSpace (f : Y ⟶ S) [QuasiSeparated f]
    [∀ i : I, QuasiSeparatedSpace (D.obj i).left] (i : I) :
    QuasiSeparatedSpace ((diagram D f).obj i) := by
  have : QuasiSeparated (pullback.fst (D.obj i).hom f) :=
    MorphismProperty.pullback_fst
      (P := (show MorphismProperty Scheme.{u} from @QuasiSeparated))
      (D.obj i).hom f inferInstance
  exact quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.obj i).hom f)

/-- An arbitrary morphism over the limit between two pulled-back models
descends to a stage, with its exact recovery square. -/
theorem exists_hom_stage [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h).left]
    [∀ i : I, CompactSpace (D.obj i).left]
    [∀ i : I, QuasiSeparatedSpace (D.obj i).left]
    (f : Y ⟶ S) (g : Z ⟶ S) [QuasiCompact f] [QuasiSeparated f]
    [LocallyOfFinitePresentation g]
    (a : pullback c.pt.hom f ⟶ pullback c.pt.hom g)
    (ha : a ≫ pullback.fst c.pt.hom g = pullback.fst c.pt.hom f) :
    ∃ (i : I) (b : pullback (D.obj i).hom f ⟶ pullback (D.obj i).hom g),
      b ≫ pullback.fst (D.obj i).hom g = pullback.fst (D.obj i).hom f ∧
      (cone D c f).π.app i ≫ b = a ≫ (cone D c g).π.app i := by
  have : ∀ {i j : I} (h : i ⟶ j), IsAffineHom ((diagram D f).map h) :=
    fun h ↦ diagram_map_isAffineHom D f h
  have : ∀ i : I, CompactSpace ((diagram D f).obj i) :=
    diagram_obj_compactSpace D f
  have : ∀ i : I, QuasiSeparatedSpace ((diagram D f).obj i) :=
    diagram_obj_quasiSeparatedSpace D f
  have hbase : (a ≫ pullback.snd c.pt.hom g) ≫ g =
      pullback.snd c.pt.hom f ≫ f := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, ha, pullback.condition]
  have hcompat : (cone D c f).π ≫ projection D f =
      (Functor.const I).map ((a ≫ pullback.snd c.pt.hom g) ≫ g) := by
    apply NatTrans.ext
    funext i
    change (cone D c f).π.app i ≫ (pullback.snd (D.obj i).hom f ≫ f) =
      (a ≫ pullback.snd c.pt.hom g) ≫ g
    rw [← Category.assoc, cone_map_snd, hbase]
  obtain ⟨i, b, hrec, hb⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
      (diagram D f) (projection D f) g (cone D c f) (coneIsLimit D c hc f)
      (a ≫ pullback.snd c.pt.hom g) hcompat
  have hb' : b ≫ g = pullback.snd (D.obj i).hom f ≫ f := hb
  let b' : pullback (D.obj i).hom f ⟶ pullback (D.obj i).hom g :=
    pullback.lift (pullback.fst (D.obj i).hom f) b
      ((pullback.condition (f := (D.obj i).hom) (g := f)).trans hb'.symm)
  refine ⟨i, b', pullback.lift_fst _ _ _, ?_⟩
  apply pullback.hom_ext
  · change ((cone D c f).π.app i ≫ b') ≫ pullback.fst (D.obj i).hom g =
      (a ≫ (cone D c g).π.app i) ≫ pullback.fst (D.obj i).hom g
    rw [Category.assoc, pullback.lift_fst, cone_map_fst,
      Category.assoc, cone_map_fst, ← Category.assoc, ha]
  · change ((cone D c f).π.app i ≫ b') ≫ pullback.snd (D.obj i).hom g =
      (a ≫ (cone D c g).π.app i) ≫ pullback.snd (D.obj i).hom g
    rw [Category.assoc, pullback.lift_snd, hrec, Category.assoc, cone_map_snd]

/-- Equality of two morphisms of stage models is detected after an actual
transition. Equality is stated in the original stage target; both maps also
have the same coefficient projection, so it determines equality of their
base changes to the later stage. -/
theorem exists_eq_stage [IsCofiltered I] (hc : IsLimit c)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (D.map h).left]
    [∀ i : I, CompactSpace (D.obj i).left]
    (f : Y ⟶ S) (g : Z ⟶ S) [QuasiCompact f] [LocallyOfFiniteType g]
    (i : I)
    (a b : pullback (D.obj i).hom f ⟶ pullback (D.obj i).hom g)
    (ha : a ≫ pullback.fst (D.obj i).hom g = pullback.fst (D.obj i).hom f)
    (hb : b ≫ pullback.fst (D.obj i).hom g = pullback.fst (D.obj i).hom f)
    (hab : (cone D c f).π.app i ≫ a = (cone D c f).π.app i ≫ b) :
    ∃ (j : I) (hji : j ⟶ i),
      (diagram D f).map hji ≫ a = (diagram D f).map hji ≫ b := by
  have : ∀ {i j : I} (h : i ⟶ j), IsAffineHom ((diagram D f).map h) :=
    fun h ↦ diagram_map_isAffineHom D f h
  have : ∀ i : I, CompactSpace ((diagram D f).obj i) :=
    diagram_obj_compactSpace D f
  have ha' : (projection D f).app i = (a ≫ pullback.snd (D.obj i).hom g) ≫ g := by
    change pullback.snd (D.obj i).hom f ≫ f =
      (a ≫ pullback.snd (D.obj i).hom g) ≫ g
    symm
    rw [Category.assoc, ← pullback.condition (f := (D.obj i).hom) (g := g),
      ← Category.assoc, ha, pullback.condition]
  have hb' : (projection D f).app i = (b ≫ pullback.snd (D.obj i).hom g) ≫ g := by
    change pullback.snd (D.obj i).hom f ≫ f =
      (b ≫ pullback.snd (D.obj i).hom g) ≫ g
    symm
    rw [Category.assoc, ← pullback.condition (f := (D.obj i).hom) (g := g),
      ← Category.assoc, hb, pullback.condition]
  have hab' : (cone D c f).π.app i ≫ (a ≫ pullback.snd (D.obj i).hom g) =
      (cone D c f).π.app i ≫ (b ≫ pullback.snd (D.obj i).hom g) := by
    rw [← Category.assoc, ← Category.assoc, hab]
  obtain ⟨j, hji, heq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    (diagram D f) (projection D f) g (cone D c f) (coneIsLimit D c hc f)
    (a ≫ pullback.snd (D.obj i).hom g)
    (b ≫ pullback.snd (D.obj i).hom g) ha' hb' hab'
  refine ⟨j, hji, ?_⟩
  apply pullback.hom_ext
  · rw [Category.assoc, ha, Category.assoc, hb]
  · simpa only [Category.assoc] using heq

/-- The original scheme-diagram form: models and maps over any fixed stage
descend farther along the same diagram. The limit supplied here is the actual
original limit, and the later stage map is produced rather than assumed. -/
theorem exists_hom_later_stage
    (F : I ⥤ Scheme.{u}) (s : Cone F) [IsCofiltered I] (hs : IsLimit s)
    [∀ {i j : I} (h : i ⟶ j), IsAffineHom (F.map h)]
    [∀ i : I, CompactSpace (F.obj i)] [∀ i : I, QuasiSeparatedSpace (F.obj i)]
    (i : I) (f : Y ⟶ F.obj i) (g : Z ⟶ F.obj i)
    [QuasiCompact f] [QuasiSeparated f] [LocallyOfFinitePresentation g]
    (a : pullback (s.π.app i) f ⟶ pullback (s.π.app i) g)
    (ha : a ≫ pullback.fst (s.π.app i) g = pullback.fst (s.π.app i) f) :
    ∃ (j : I) (hji : j ⟶ i)
      (b : pullback (F.map hji) f ⟶ pullback (F.map hji) g),
      b ≫ pullback.fst (F.map hji) g = pullback.fst (F.map hji) f ∧
      ((Over.pullback f).map
        (Over.homMk (s.π.app j) (s.w hji) :
          Over.mk (s.π.app i) ⟶ Over.mk (F.map hji))).left ≫ b =
      a ≫ ((Over.pullback g).map
        (Over.homMk (s.π.app j) (s.w hji) :
          Over.mk (s.π.app i) ⟶ Over.mk (F.map hji))).left := by
  have : ∀ {j k : Over i} (h : j ⟶ k),
      IsAffineHom (((Over.post F).map h).left) :=
    fun h ↦ inferInstanceAs (IsAffineHom (F.map h.left))
  have : ∀ j : Over i, CompactSpace ((Over.post F).obj j).left :=
    fun j ↦ inferInstanceAs (CompactSpace (F.obj j.left))
  have : ∀ j : Over i, QuasiSeparatedSpace ((Over.post F).obj j).left :=
    fun j ↦ inferInstanceAs (QuasiSeparatedSpace (F.obj j.left))
  obtain ⟨j, b, hb, hrec⟩ := exists_hom_stage (Over.post F) ((Over.conePost F i).obj s)
    (Over.isLimitConePost i hs) f g a ha
  exact ⟨j.left, j.hom, b, hb, hrec⟩

end AlgebraicGeometry.AffineTransitionHom
