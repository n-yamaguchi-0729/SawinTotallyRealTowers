/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Generator.Sheaf
import Mathlib.CategoryTheory.Generator.StrongGenerator
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Sheaves.LocallySurjective
import Mathlib.Topology.Spectral.Prespectral

/-!
# Compact-open generators of topological sheaves

The actual sheafifications of the free representables on compact opens
form a strong generator on a prespectral space. Their maps into a sheaf
are its sections on those opens. Compact-open neighbourhoods therefore
detect equality and supply the local lifts needed to detect isomorphisms.

This is the generator part of the finite-presentation argument in the
Stacks Project, tag 0CAI: https://stacks.math.columbia.edu/tag/0CAI.
The Lean proof is original and uses Mathlib's sheafified free representables.
-/

noncomputable section

universe u

open CategoryTheory Limits TopCat TopologicalSpace Opposite

namespace SchemeTheory

variable {X : TopCat.{u}}

/-- The actual sheafified free representable, with one generator, on an open. -/
def openGenerator (U : Opens X) : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) :=
  CategoryTheory.Sheaf.freeYoneda (Opens.grothendieckTopology X) U PUnit.{u + 1}

/-- Maps from the sheafified open representable are actual sections. -/
def openGeneratorHomEquiv {U : Opens X}
    {F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)} :
    (openGenerator U ⟶ F) ≃ F.obj.obj (op U) :=
  CategoryTheory.Sheaf.freeYonedaHomEquiv.trans
    (TypeCat.homEquiv.trans (Equiv.punitArrowEquiv _))

/-- The section represented by a composite is the image of the represented section. -/
theorem openGeneratorHomEquiv_comp {U : Opens X}
    {F G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)}
    (α : openGenerator U ⟶ F) (f : F ⟶ G) :
    openGeneratorHomEquiv (α ≫ f) = f.hom.app (op U) (openGeneratorHomEquiv α) := by
  have h : CategoryTheory.Sheaf.freeYonedaHomEquiv (α ≫ f) =
      CategoryTheory.Sheaf.freeYonedaHomEquiv α ≫ f.hom.app (op U) := by
    let a : (presheafToSheaf (Opens.grothendieckTopology X) (Type u)).obj
        (CategoryTheory.Presheaf.freeYoneda U PUnit.{u + 1}) ⟶ F := α
    have hn := Adjunction.homEquiv_naturality_right
      (sheafificationAdjunction (Opens.grothendieckTopology X) (Type u)) a f
    exact (congrArg CategoryTheory.Presheaf.freeYonedaHomEquiv hn).trans
      (CategoryTheory.Presheaf.freeYonedaHomEquiv_comp _ f.hom)
  exact congrArg (fun k : PUnit.{u + 1} ⟶ G.obj.obj (op U) => k PUnit.unit) h

/-- The family of actual sheafified representables on compact opens. -/
def compactOpenGenerators (X : TopCat.{u}) :
    ObjectProperty (CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) :=
  ObjectProperty.ofObj
    (fun U : {U : Opens X // IsCompact (U : Set X)} => openGenerator U.1)

/-- Compact-open sections detect morphisms of sheaves. -/
theorem compactOpenGenerators_isSeparating [PrespectralSpace X] :
    (compactOpenGenerators X).IsSeparating := by
  intro F G f g hfg
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  apply TopCat.Presheaf.IsSheaf.section_ext G.property
  intro x hx
  obtain ⟨V, hV, hxV, hVU⟩ :=
    (Opens.isBasis_iff_nbhd.mp (PrespectralSpace.isBasis_opens X)) hx
  refine ⟨V, hVU, hxV, ?_⟩
  let t : F.obj.obj (op V) := F.obj.map (homOfLE hVU).op s
  let α : openGenerator V ⟶ F := openGeneratorHomEquiv.symm t
  have heq : α ≫ f = α ≫ g :=
    hfg (openGenerator V) (ObjectProperty.ofObj_apply
      (fun W : {W : Opens X // IsCompact (W : Set X)} => openGenerator W.1) ⟨V, hV⟩) α
  have ht : f.hom.app (op V) t = g.hom.app (op V) t := by
    have h := congrArg openGeneratorHomEquiv heq
    simpa only [openGeneratorHomEquiv_comp, α, Equiv.apply_symm_apply] using h
  exact (f.hom.naturality_apply (homOfLE hVU).op s).symm.trans
    (ht.trans (g.hom.naturality_apply (homOfLE hVU).op s))

/-- Compact-open sections also detect isomorphisms among monomorphisms. -/
theorem compactOpenGenerators_isStrongGenerator [PrespectralSpace X] :
    (compactOpenGenerators X).IsStrongGenerator := by
  rw [ObjectProperty.isStrongGenerator_iff]
  refine ⟨compactOpenGenerators_isSeparating, ?_⟩
  intro F G f hmono hsurj
  have hi : CategoryTheory.Sheaf.IsLocallyInjective f := by
    apply (CategoryTheory.Sheaf.isLocallyInjective_iff_injective f).mpr
    intro U
    have : Mono f.hom := (sheafToPresheaf (Opens.grothendieckTopology X) (Type u)).map_mono f
    have : Mono (f.hom.app U) := (NatTrans.mono_iff_mono_app f.hom).mp this U
    exact (CategoryTheory.mono_iff_injective (f.hom.app U)).mp this
  have hs : CategoryTheory.Sheaf.IsLocallySurjective f := by
    constructor
    intro U s x hx
    obtain ⟨V, hV, hxV, hVU⟩ :=
      (Opens.isBasis_iff_nbhd.mp (PrespectralSpace.isBasis_opens X)) hx
    let t : G.obj.obj (op V) := G.obj.map (homOfLE hVU).op s
    let α : openGenerator V ⟶ G := openGeneratorHomEquiv.symm t
    obtain ⟨β, hβ⟩ := hsurj (openGenerator V)
      (ObjectProperty.ofObj_apply
      (fun W : {W : Opens X // IsCompact (W : Set X)} => openGenerator W.1) ⟨V, hV⟩) α
    refine ⟨V, homOfLE hVU, ⟨openGeneratorHomEquiv β, ?_⟩, hxV⟩
    have h := congrArg openGeneratorHomEquiv hβ
    simpa only [openGeneratorHomEquiv_comp, α, Equiv.apply_symm_apply] using h
  exact (CategoryTheory.Sheaf.isLocallyBijective_iff_isIso f).mp ⟨hi, hs⟩

end SchemeTheory
