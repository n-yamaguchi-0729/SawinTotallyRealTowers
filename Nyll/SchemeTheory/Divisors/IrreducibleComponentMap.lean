/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale
import Nyll.SchemeTheory.Divisors.Reduced
import Nyll.SchemeTheory.Morphisms.GeometricallyIntegralDescent

/-!
# Morphisms between reduced irreducible components

This file constructs the induced morphism between the reduced closed
subschemes carried by irreducible components.  It also supplies the reverse
component-lifting statement for surjective closed generalizing maps.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace TopologicalSpace

universe u v

/-- For a surjective closed generalizing map, every irreducible component of
the target is the image of an irreducible component of the source. -/
lemma exists_irreducibleComponent_image_eq_of_surjective
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
    [T0Space X] [QuasiSober X] [QuasiSober Y]
    {f : X → Y} (hfc : Continuous f) (hfclosed : IsClosedMap f)
    (hfgeneral : GeneralizingMap f) (hfsurj : Function.Surjective f)
    (W : Set Y) (hW : W ∈ irreducibleComponents Y) :
    ∃ Z : Set X, Z ∈ irreducibleComponents X ∧ f '' Z = W := by
  let η : genericPoints Y := genericPoints.ofComponent ⟨W, hW⟩
  obtain ⟨x, hx⟩ := hfsurj η.1
  let Z : Set X := irreducibleComponent x
  have hZ : Z ∈ irreducibleComponents X :=
    irreducibleComponent_mem_irreducibleComponents x
  obtain ⟨V, hV, himage⟩ :=
    exists_irreducibleComponent_image_eq hfc hfclosed hfgeneral Z hZ
  have hηV : η.1 ∈ V := by
    rw [← himage]
    exact ⟨x, mem_irreducibleComponent, hx⟩
  have hWV : W ⊆ V := by
    have hηW : IsGenericPoint η.1 W := by
      simpa only [η] using
        (genericPoints.isGenericPoint_ofComponent ⟨W, hW⟩)
    rw [← hηW.def]
    exact closure_minimal (Set.singleton_subset_iff.mpr hηV)
      (isClosed_of_mem_irreducibleComponents V hV)
  have hVW : V ⊆ W := hW.2 hV.1 hWV
  exact ⟨Z, hZ, himage.trans (Set.Subset.antisymm hVW hWV)⟩

end TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme

variable {X Y : Scheme.{u}}

instance reducedIrreducibleComponent_isReduced
    (X : Scheme.{u}) (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    AlgebraicGeometry.IsReduced (X.reducedIrreducibleComponent Z hZ) := by
  let I := IdealSheafData.vanishingIdeal
    ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
  have hI : I.IsReduced := by
    rw [IdealSheafData.IsReduced]
    ext U : 2
    exact (PrimeSpectrum.isRadical_vanishingIdeal _).radical
  exact hI.subscheme

/-- The morphism between reduced irreducible components induced by a
morphism whose image on the chosen source component is the chosen target
component. -/
noncomputable def reducedIrreducibleComponentMap (f : X ⟶ Y)
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (W : Set Y) (hW : W ∈ irreducibleComponents Y)
    (himage : f '' Z = W) :
    X.reducedIrreducibleComponent Z hZ ⟶
      Y.reducedIrreducibleComponent W hW :=
  let IZ := IdealSheafData.vanishingIdeal
    ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
  let IW := IdealSheafData.vanishingIdeal
    ⟨W, isClosed_of_mem_irreducibleComponents W hW⟩
  IZ.subschemeMap IW f (by
    have hmap : IZ.map f = IW := by
      dsimp only [IZ, IW]
      rw [IdealSheafData.map_vanishingIdeal]
      congr 1
      apply Closeds.ext
      rw [Closeds.coe_closure]
      change closure (f '' Z) = W
      rw [himage, (isClosed_of_mem_irreducibleComponents W hW).closure_eq]
    exact hmap.ge)

@[reassoc (attr := simp)]
lemma reducedIrreducibleComponentMap_ι (f : X ⟶ Y)
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (W : Set Y) (hW : W ∈ irreducibleComponents Y)
    (himage : f '' Z = W) :
    X.reducedIrreducibleComponentMap f Z hZ W hW himage ≫
        Y.reducedIrreducibleComponentι W hW =
      X.reducedIrreducibleComponentι Z hZ ≫ f := by
  unfold reducedIrreducibleComponentMap
  change _ ≫ (IdealSheafData.vanishingIdeal
      ⟨W, isClosed_of_mem_irreducibleComponents W hW⟩).subschemeι =
    (IdealSheafData.vanishingIdeal
      ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subschemeι ≫ f
  apply IdealSheafData.subschemeMap_subschemeι

instance (f : X ⟶ Y) [IsFinite f]
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (W : Set Y) (hW : W ∈ irreducibleComponents Y)
    (himage : f '' Z = W) :
    IsFinite (X.reducedIrreducibleComponentMap f Z hZ W hW himage) := by
  refine @IsFinite.of_comp _ _ _
    (X.reducedIrreducibleComponentMap f Z hZ W hW himage)
    (Y.reducedIrreducibleComponentι W hW) ?_ ?_
  · rw [reducedIrreducibleComponentMap_ι]
    infer_instance
  · infer_instance

/-- If the image of the chosen source component is the chosen target
component, the induced morphism of reduced components is surjective. -/
lemma reducedIrreducibleComponentMap_surjective (f : X ⟶ Y)
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (W : Set Y) (hW : W ∈ irreducibleComponents Y)
    (himage : f '' Z = W) :
    Function.Surjective
      (X.reducedIrreducibleComponentMap f Z hZ W hW himage) := by
  intro y
  have hyW : y.1 ∈ W := by
    change y.1 ∈ (IdealSheafData.vanishingIdeal
      ⟨W, isClosed_of_mem_irreducibleComponents W hW⟩).support
    simpa only [IdealSheafData.coe_support_vanishingIdeal] using y.2
  have hyimage : y.1 ∈ f '' Z := by
    rw [himage]
    exact hyW
  obtain ⟨x, hxZ, hxy⟩ := hyimage
  let x' : X.reducedIrreducibleComponent Z hZ := ⟨x, by
    change x ∈ (↑(IdealSheafData.vanishingIdeal
      ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).support : Set X)
    rw [IdealSheafData.coe_support_vanishingIdeal]
    exact hxZ⟩
  refine ⟨x', ?_⟩
  apply (Y.reducedIrreducibleComponentι W hW).isEmbedding.injective
  rw [← Scheme.Hom.comp_apply, reducedIrreducibleComponentMap_ι,
    Scheme.Hom.comp_apply]
  exact hxy

instance (f : X ⟶ Y)
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (W : Set Y) (hW : W ∈ irreducibleComponents Y)
    (himage : f '' Z = W) :
    Surjective (X.reducedIrreducibleComponentMap f Z hZ W hW himage) :=
  ⟨X.reducedIrreducibleComponentMap_surjective f Z hZ W hW himage⟩

end Scheme

end AlgebraicGeometry
