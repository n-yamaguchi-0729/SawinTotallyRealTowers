/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.Directed
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
import Mathlib.CategoryTheory.Limits.IsLimit

/-!
# The original affine-morphism source as a colimit of its section spectra

For an actual affine morphism, pull back the base's affine locally directed
cover. The pullback charts are identified with the literal spectra of the
sections on the inverse-image opens. Their natural isomorphism transports
the existing colimit of the pulled-back cover to a colimit with vertex the
original source. No relative-spectrum comparison or effectivity is assumed.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.AffineSourceColimit

variable {T X : Scheme.{u}} (g : T ⟶ X)

/-- The actual direct-image section rings on the base's affine site. -/
def ringDiagram : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat.{u} :=
  (AffineZariskiSite.toOpensFunctor X).op ⋙ (Opens.map g.base).op ⋙ T.presheaf

/-- The diagram of spectra of these actual section rings. -/
def diagram : X.AffineZariskiSite ⥤ Scheme.{u} :=
  (ringDiagram g).rightOp ⋙ Scheme.Spec

private abbrev sourceCover : T.OpenCover :=
  (AffineZariskiSite.directedCover X).pullback₁ g

private def sourceDiagram : X.AffineZariskiSite ⥤ Scheme.{u} :=
  (sourceCover g).functorOfLocallyDirected

private def sourceCocone : Cocone (sourceDiagram g) :=
  (sourceCover g).coconeOfLocallyDirected

private def sourceCoconeIsColimit : IsColimit (sourceCocone g) :=
  (sourceCover g).isColimitCoconeOfLocallyDirected

private theorem sourceCocone_app (U : X.AffineZariskiSite) :
    (sourceCocone g).ι.app U = pullback.fst g U.1.ι := rfl

variable [IsAffineHom g]

private def chartIso (U : X.AffineZariskiSite) :
    (sourceDiagram g).obj U ≅ Spec Γ(T, g ⁻¹ᵁ U.1) :=
  pullbackRestrictIsoRestrict g U.1 ≪≫ (U.2.preimage g).isoSpec

private theorem chartIso_hom_fromSpec (U : X.AffineZariskiSite) :
    (chartIso g U).hom ≫ (U.2.preimage g).fromSpec = (sourceCocone g).ι.app U := by
  rw [sourceCocone_app]
  change ((pullbackRestrictIsoRestrict g U.1).hom ≫ (U.2.preimage g).isoSpec.hom) ≫
      (U.2.preimage g).fromSpec = pullback.fst g U.1.ι
  rw [Category.assoc, IsAffineOpen.isoSpec_hom_fromSpec,
    pullbackRestrictIsoRestrict_hom_ι]

private theorem diagram_map_fromSpec {U V : X.AffineZariskiSite} (i : U ⟶ V) :
    (diagram g).map i ≫ (V.2.preimage g).fromSpec = (U.2.preimage g).fromSpec :=
  (V.2.preimage g).map_fromSpec (U.2.preimage g)
    ((Opens.map g.base).map ((AffineZariskiSite.toOpensFunctor X).map i)).op

private def chartDiagramIso : sourceDiagram g ≅ diagram g :=
  NatIso.ofComponents (chartIso g) (fun {U V : X.AffineZariskiSite} i => by
    let eU : (sourceDiagram g).obj U ≅ (diagram g).obj U := chartIso g U
    let eV : (sourceDiagram g).obj V ≅ (diagram g).obj V := chartIso g V
    let d : (sourceDiagram g).obj U ⟶ (sourceDiagram g).obj V := (sourceDiagram g).map i
    let k : (diagram g).obj U ⟶ (diagram g).obj V := (diagram g).map i
    let u : (diagram g).obj U ⟶ T := (U.2.preimage g).fromSpec
    let v : (diagram g).obj V ⟶ T := (V.2.preimage g).fromSpec
    let bU : (sourceDiagram g).obj U ⟶ T := (sourceCocone g).ι.app U
    let bV : (sourceDiagram g).obj V ⟶ T := (sourceCocone g).ι.app V
    have hu : eU.hom ≫ u = bU := chartIso_hom_fromSpec g U
    have hv : eV.hom ≫ v = bV := chartIso_hom_fromSpec g V
    have hk : k ≫ v = u := diagram_map_fromSpec g i
    have hd : d ≫ bV = bU := (sourceCocone g).w i
    have : IsOpenImmersion v :=
      IsAffineOpen.isOpenImmersion_fromSpec (V.2.preimage g)
    apply (cancel_mono v).mp
    calc
      (d ≫ eV.hom) ≫ v = d ≫ (eV.hom ≫ v) := Category.assoc d eV.hom v
      _ = d ≫ bV := congrArg (fun z : (sourceDiagram g).obj V ⟶ T => d ≫ z) hv
      _ = bU := hd
      _ = eU.hom ≫ u := hu.symm
      _ = eU.hom ≫ (k ≫ v) :=
        congrArg (fun z : (diagram g).obj U ⟶ T => eU.hom ≫ z) hk.symm
      _ = (eU.hom ≫ k) ≫ v := (Category.assoc eU.hom k v).symm)

/-- The literal source scheme and its affine inverse-image chart maps. -/
def cocone : Cocone (diagram g) where
  pt := T
  ι :=
    { app U := (U.2.preimage g).fromSpec
      naturality {U V} i := by
        change (diagram g).map i ≫ (V.2.preimage g).fromSpec =
          (U.2.preimage g).fromSpec ≫ 𝟙 T
        rw [Category.comp_id]
        exact diagram_map_fromSpec g i }

/-- The original source is the actual colimit of its affine section spectra.
This is transported from the existing locally directed pullback-cover
colimit, using the concrete chart isomorphisms above. -/
def coconeIsColimit : IsColimit (cocone g) := by
  refine (IsColimit.precomposeHomEquiv (chartDiagramIso g) (cocone g)) ?_
  refine IsColimit.ofIsoColimit (sourceCoconeIsColimit g) ?_
  refine Cocone.ext (Iso.refl T) ?_
  intro U
  let b : (sourceDiagram g).obj U ⟶ T := (sourceCocone g).ι.app U
  exact (Category.comp_id b).trans (chartIso_hom_fromSpec g U).symm

end AlgebraicGeometry.Scheme.AffineSourceColimit
