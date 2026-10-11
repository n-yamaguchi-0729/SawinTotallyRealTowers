/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.WeilRestriction.CoverHypercover
public import Nyll.SchemeTheory.WeilRestriction.GluedComparison
public import Nyll.SchemeTheory.WeilRestriction.IteratedSlice
public import Nyll.SchemeTheory.WeilRestriction.LocalRepresenters
public import Mathlib.CategoryTheory.Limits.Types.Multiequalizer
public import Nyll.SchemeTheory.WeilRestriction.GluingData

/-!
# The universal section of glued local representers

The canonical transitions between local representers preserve their universal
elements. These elements therefore form a compatible family on the locally
directed cover of the glued scheme. The sheaf condition supplies a global
section whose restriction to every local representer is its universal element.
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

/-- The universal element of a local representer, viewed over the original base. -/
def localRepresenterUniversalSection (i : 𝒰.I₀) :
    F.obj (Opposite.op ((Over.map (𝒰.f i)).obj (W i))) :=
  (representableByIteratedSlice (𝒰.f i) F (W i) (h i)).homEquiv
    (𝟙 ((Over.iteratedSliceEquiv (Over.mk (𝒰.f i))).inverse.obj (W i)))

variable [Quiver.IsThin 𝒰.I₀] [Small.{u} 𝒰.I₀]

/-- The Zariski hypercover of the glued representer given by its local representing schemes. -/
def gluedLocalRepresenterHypercover :
    (Scheme.zariskiTopology.over S).OneHypercover (gluedLocalRepresenter F 𝒰 W h) :=
  let d : 𝒰.RelativeGluingData := localRepresenterGluingData F 𝒰 W h
  locallyDirectedCoverHypercoverOver d.cover d.toBase
    (fun i ↦ (W i).hom ≫ 𝒰.f i) (fun i ↦ d.ι_toBase i)

/-- The compatible universal sections on the hypercover of the glued local representers. -/
def gluedLocalRepresenterCompatibleSections :
    ((gluedLocalRepresenterHypercover F 𝒰 W h).multicospanIndex F).sections := by
  let D : 𝒰.I₀ ⥤ Over S :=
    Over.lift 𝒰.functorOfLocallyDirected 𝒰.functorOfLocallyDirectedHomBase
  let W' : ∀ i : 𝒰.I₀, Over (D.obj i) := fun i ↦
    (Over.iteratedSliceEquiv (Over.mk (𝒰.f i))).inverse.obj (W i)
  let h' : ∀ i : 𝒰.I₀, (sliceRestriction F (D.obj i)).RepresentableBy (W' i) :=
    fun i ↦ representableByIteratedSlice (𝒰.f i) F (W i) (h i)
  refine { val := fun i ↦ localRepresenterUniversalSection F 𝒰 W h i.down
           property := ?_ }
  rintro ⟨⟨i, j⟩, ⟨k, a, b⟩⟩
  change F.map (localRepresenterMap (h' k) (h' i.down) (D.map a)).op
      ((h' i.down).homEquiv (𝟙 (W' i.down))) =
    F.map (localRepresenterMap (h' k) (h' j.down) (D.map b)).op
      ((h' j.down).homEquiv (𝟙 (W' j.down)))
  exact (localRepresenterMap_universal (h' k) (h' i.down) (D.map a)).trans
    (localRepresenterMap_universal (h' k) (h' j.down) (D.map b)).symm

variable (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F)

/-- The local universal elements glue to a section on the glued representer. -/
def gluedLocalRepresenterUniversalSection :
    F.obj (Opposite.op (gluedLocalRepresenter F 𝒰 W h)) :=
  Multifork.IsLimit.sectionsEquiv
    ((gluedLocalRepresenterHypercover F 𝒰 W h).isLimitMultifork ⟨F, hF⟩)
    (gluedLocalRepresenterCompatibleSections F 𝒰 W h)

/-- Restricting the glued section recovers the corresponding local universal element. -/
lemma gluedLocalRepresenterUniversalSection_restrict (i : 𝒰.I₀) :
    F.map (gluedLocalRepresenterInclusion F 𝒰 W h i).op
        (gluedLocalRepresenterUniversalSection F 𝒰 W h hF) =
      localRepresenterUniversalSection F 𝒰 W h i := by
  exact Multifork.IsLimit.sectionsEquiv_apply_val
    ((gluedLocalRepresenterHypercover F 𝒰 W h).isLimitMultifork ⟨F, hF⟩)
    (gluedLocalRepresenterCompatibleSections F 𝒰 W h) (ULift.up i)

end SchemeTheory.WeilRestriction
