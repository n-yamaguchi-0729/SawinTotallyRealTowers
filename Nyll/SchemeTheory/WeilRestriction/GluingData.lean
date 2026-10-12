/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.WeilRestriction.LocalRepresenterDiagram
public import Nyll.SchemeTheory.WeilRestriction.IteratedSlice
public import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Nyll.SchemeTheory.WeilRestriction.LocalRepresenters

/-!
# Gluing data from local relative representers

Local representations of one presheaf on `Over S` determine relative gluing
data on a locally directed open cover. The transition maps and cartesian
squares are constructed from universal elements, using the iterated slice
equivalence to work in `Over S` throughout.

The resulting glued scheme is finite étale if each local representer is.
Its global representing property is a separate sheaf-descent step.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

universe u v

namespace SchemeTheory.WeilRestriction

variable {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
  (𝒰 : S.OpenCover) [Category.{v} 𝒰.I₀] [𝒰.LocallyDirected]
  (W : ∀ i : 𝒰.I₀, Over (𝒰.X i))
  (h : ∀ i : 𝒰.I₀, ((Over.map (𝒰.f i)).op ⋙ F).RepresentableBy (W i))

/-- Construct all the transition maps and pullback squares for local representers. -/
def localRepresenterGluingData : 𝒰.RelativeGluingData := by
  let D : 𝒰.I₀ ⥤ Over S :=
    Over.lift 𝒰.functorOfLocallyDirected 𝒰.functorOfLocallyDirectedHomBase
  let W' : ∀ i : 𝒰.I₀, Over (D.obj i) := fun i ↦
    (Over.iteratedSliceEquiv (Over.mk (𝒰.f i))).inverse.obj (W i)
  let h' : ∀ i : 𝒰.I₀, (sliceRestriction F (D.obj i)).RepresentableBy (W' i) :=
    fun i ↦ representableByIteratedSlice (𝒰.f i) F (W i) (h i)
  exact
    { functor := localRepresenterDiagram F D W' h' ⋙ Over.forget S
      natTrans := Functor.whiskerRight (localRepresenterProjection F D W' h') (Over.forget S)
      equifibered :=
        (localRepresenterProjection_equifibered F D W' h').whiskerRight (Over.forget S) }

/-- The local structure maps of the constructed gluing data are the given ones. -/
lemma localRepresenterGluingData_app (i : 𝒰.I₀) :
    (localRepresenterGluingData F 𝒰 W h).natTrans.app i = (W i).hom := rfl

variable [Quiver.IsThin 𝒰.I₀] [Small.{u} 𝒰.I₀]

/-- The scheme obtained by gluing the local representers, with its map to the base. -/
def gluedLocalRepresenter : Over S :=
  Over.mk (localRepresenterGluingData F 𝒰 W h).toBase

/-- Finite étaleness of the local representers descends to their glued scheme. -/
lemma gluedLocalRepresenter_isFiniteEtale
    (hFinite : ∀ i : 𝒰.I₀, IsFiniteEtale (W i).hom) :
    IsFiniteEtale (gluedLocalRepresenter F 𝒰 W h).hom := by
  let d : 𝒰.RelativeGluingData := localRepresenterGluingData F 𝒰 W h
  let P : MorphismProperty Scheme.{u} := @IsFiniteEtale
  change P d.toBase
  apply IsZariskiLocalAtTarget.of_openCover 𝒰
  intro i
  change P (pullback.snd d.toBase (𝒰.f i))
  let e : (d.functor.obj i) ≅ pullback d.toBase (𝒰.f i) :=
    (d.isPullback_natTrans_ι_toBase i).flip.isoPullback
  have he : e.hom ≫ pullback.snd d.toBase (𝒰.f i) = d.natTrans.app i :=
    (d.isPullback_natTrans_ι_toBase i).flip.isoPullback_hom_snd
  rw [← P.cancel_left_of_respectsIso e.hom, he]
  exact hFinite i

end SchemeTheory.WeilRestriction
