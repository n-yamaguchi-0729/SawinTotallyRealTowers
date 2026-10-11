/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.WeilRestriction.GluedUniversal
public import Nyll.SchemeTheory.WeilRestriction.LocalIsomorphism
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import Nyll.SchemeTheory.WeilRestriction.GluedComparison
public import Nyll.SchemeTheory.WeilRestriction.GluingData
public import Nyll.SchemeTheory.WeilRestriction.IteratedSlice

/-!
# Representability by gluing local relative representers

The universal section constructed from the local universal elements induces
a map from the Yoneda presheaf of the glued scheme. Its restriction to each
cover member is a bijection, by the cartesian gluing square and the local
representing equivalence. The sheaf condition then makes this map an
isomorphism globally.
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u v

namespace SchemeTheory.WeilRestriction

variable {S : Scheme.{u}} (F : (Over S)ᵒᵖ ⥤ Type u)
  (𝒰 : S.OpenCover) [Category.{v} 𝒰.I₀] [𝒰.LocallyDirected]
  (W : ∀ i : 𝒰.I₀, Over (𝒰.X i))
  (h : ∀ i : 𝒰.I₀, ((Over.map (𝒰.f i)).op ⋙ F).RepresentableBy (W i))
  [Quiver.IsThin 𝒰.I₀] [Small.{u} 𝒰.I₀]

/-- The local representing equivalence, expressed on maps into the glued scheme. -/
def gluedLocalRepresenterEvaluationEquiv (i : 𝒰.I₀) (T : Over (𝒰.X i)) :
    ((Over.map (𝒰.f i)).obj T ⟶ gluedLocalRepresenter F 𝒰 W h) ≃
      F.obj (op ((Over.map (𝒰.f i)).obj T)) :=
  (gluedLocalRepresenterHomEquiv F 𝒰 W h i T).trans <|
    ((Over.iteratedSliceEquiv (Over.mk (𝒰.f i))).symm.fullyFaithfulFunctor.homEquiv
      (X := T) (Y := W i)).trans
        (representableByIteratedSlice (𝒰.f i) F (W i) (h i)).homEquiv

variable (hF : Presheaf.IsSheaf (Scheme.zariskiTopology.over S) F)

/-- Evaluation of the glued universal section agrees with the local representing equivalence. -/
lemma gluedLocalRepresenterUniversalSection_eval (i : 𝒰.I₀) (T : Over (𝒰.X i))
    (g : (Over.map (𝒰.f i)).obj T ⟶ gluedLocalRepresenter F 𝒰 W h) :
    (yonedaEquiv.symm (gluedLocalRepresenterUniversalSection F 𝒰 W h hF)).app
        (op ((Over.map (𝒰.f i)).obj T)) g =
      gluedLocalRepresenterEvaluationEquiv F 𝒰 W h i T g := by
  let E := Over.iteratedSliceEquiv (Over.mk (𝒰.f i))
  let h' := representableByIteratedSlice (𝒰.f i) F (W i) (h i)
  let e := gluedLocalRepresenterHomEquiv F 𝒰 W h i T
  obtain ⟨k, rfl⟩ := e.symm.surjective g
  change F.map (e.symm k).op (gluedLocalRepresenterUniversalSection F 𝒰 W h hF) =
    h'.homEquiv (E.inverse.map (e (e.symm k)))
  rw [e.apply_symm_apply, gluedLocalRepresenterHomEquiv_symm,
    op_comp, F.map_comp]
  change F.map ((Over.map (𝒰.f i)).map k).op
      (F.map (gluedLocalRepresenterInclusion F 𝒰 W h i).op
        (gluedLocalRepresenterUniversalSection F 𝒰 W h hF)) =
    h'.homEquiv (E.inverse.map k)
  rw [gluedLocalRepresenterUniversalSection_restrict]
  exact (h'.homEquiv_eq (E.inverse.map k)).symm

/-- Evaluation at the glued universal section is bijective on every local test scheme. -/
lemma gluedLocalRepresenterUniversalSection_bijective (i : 𝒰.I₀) (T : Over (𝒰.X i)) :
    Function.Bijective
      ((yonedaEquiv.symm (gluedLocalRepresenterUniversalSection F 𝒰 W h hF)).app
        (op ((Over.map (𝒰.f i)).obj T))) := by
  have heq :
      (fun g ↦ (yonedaEquiv.symm
        (gluedLocalRepresenterUniversalSection F 𝒰 W h hF)).app
          (op ((Over.map (𝒰.f i)).obj T)) g) =
        (fun g ↦ gluedLocalRepresenterEvaluationEquiv F 𝒰 W h i T g) :=
    funext (gluedLocalRepresenterUniversalSection_eval F 𝒰 W h hF i T)
  change Function.Bijective (fun g ↦
    (yonedaEquiv.symm (gluedLocalRepresenterUniversalSection F 𝒰 W h hF)).app
      (op ((Over.map (𝒰.f i)).obj T)) g)
  rw [heq]
  exact (gluedLocalRepresenterEvaluationEquiv F 𝒰 W h i T).bijective

/-- A sheaf with local relative representers is represented by their glued scheme. -/
def gluedLocalRepresentable : F.RepresentableBy (gluedLocalRepresenter F 𝒰 W h) := by
  let J := Scheme.zariskiTopology.over S
  let η : J.yoneda.obj (gluedLocalRepresenter F 𝒰 W h) ⟶ (⟨F, hF⟩ : Sheaf J (Type u)) :=
    ObjectProperty.homMk (yonedaEquiv.symm (gluedLocalRepresenterUniversalSection F 𝒰 W h hF))
  letI : IsIso η := isIso_of_bijective_on_openCover 𝒰 η
    (fun i T ↦ gluedLocalRepresenterUniversalSection_bijective F 𝒰 W h hF i T)
  exact Functor.representableByEquiv.symm
    ((sheafToPresheaf J (Type u)).mapIso (asIso η))

end SchemeTheory.WeilRestriction
