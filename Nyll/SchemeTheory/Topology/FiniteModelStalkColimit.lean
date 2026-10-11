/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Filtered.Basic
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.Topology.Sheaves.Alexandrov
import Mathlib.Topology.Sheaves.Stalks
import Nyll.SchemeTheory.Topology.CompactOpenFiniteModels
import Nyll.SchemeTheory.Topology.FiniteModelPrincipalStalk

/-!
# The actual stalk colimit of finite-model principal sections

Sections over the inverse images of finite-model principal opens form an
actual filtered diagram. Its germ cocone is a colimit at the actual stalk.
Every germ has a compact-open representative, and equality of germs is
witnessed after adding a compact-open coordinate to an existing model.
The proof uses the concrete filtered-colimit criterion for types.
The Lean proof is original.
-/

noncomputable section

universe u

open CategoryTheory Limits TopCat TopologicalSpace Topology Opposite

namespace SchemeTheory.CompactOpenFiniteModel

variable {X : TopCat.{u}}

private theorem sectionOpen_antitone {S T : Finset (CompactOpens X)}
    (h : S ⊆ T) (x : X) :
    (Opens.map (quotient T)).obj (Alexandrov.principalOpen (quotient T x)) ≤
      (Opens.map (quotient S)).obj (Alexandrov.principalOpen (quotient S x)) := by
  rw [neighborhood_preimage, neighborhood_preimage]
  exact neighborhood_antitone h x

/-- Sections on actual inverse images of finite-model principal opens,
with the actual restriction maps under finite-family refinement. -/
def sectionDiagram
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) (x : X) :
    Finset (CompactOpens X) ⥤ Type u := by
  let P : X.Presheaf (Type u) := F.obj
  exact {
    obj S := P.obj
      (op ((Opens.map (quotient S)).obj (Alexandrov.principalOpen (quotient S x))))
    map {S T} h := P.map (homOfLE (sectionOpen_antitone h.le x)).op
    map_id S := by
      change P.map (𝟙 (op ((Opens.map (quotient S)).obj
        (Alexandrov.principalOpen (quotient S x))))) = _
      exact P.map_id _
    map_comp {S T R} f g := by
      rw [← P.map_comp]
      exact congrArg (fun h :
        op ((Opens.map (quotient S)).obj (Alexandrov.principalOpen (quotient S x))) ⟶
        op ((Opens.map (quotient R)).obj (Alexandrov.principalOpen (quotient R x))) =>
          P.map h) (Subsingleton.elim _ _) }

/-- The actual germ cocone from finite-model principal sections to the stalk. -/
def sectionCocone
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) (x : X) :
    Cocone (sectionDiagram F x) := by
  let P : X.Presheaf (Type u) := F.obj
  let O : Finset (CompactOpens X) → Opens X := fun S =>
    (Opens.map (quotient S)).obj (Alexandrov.principalOpen (quotient S x))
  have hxO (S : Finset (CompactOpens X)) : x ∈ O S := by
    change x ∈ (Opens.map (quotient S)).obj (Alexandrov.principalOpen (quotient S x))
    rw [neighborhood_preimage]
    exact self_mem_neighborhood S x
  exact {
    pt := TopCat.Presheaf.stalk P x
    ι := {
      app S := P.germ (O S) x (hxO S)
      naturality {S T} h := by
        let i : O T ⟶ O S := homOfLE (sectionOpen_antitone h.le x)
        change P.map i.op ≫ P.germ (O T) x (hxO T) =
          P.germ (O S) x (hxO S) ≫ 𝟙 (P.stalk x)
        exact (P.germ_res i x (hxO T)).trans
          (Category.comp_id (P.germ (O S) x (hxO S))).symm } }

/-- The finite-model section diagram has the actual stalk as its colimit.
Surjectivity and eventual equality are proved directly from germs. -/
def sectionCoconeIsColimit [PrespectralSpace X]
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) (x : X) :
    IsColimit (sectionCocone F x) := by
  classical
  let P : X.Presheaf (Type u) := F.obj
  let O : Finset (CompactOpens X) → Opens X := fun S =>
    (Opens.map (quotient S)).obj (Alexandrov.principalOpen (quotient S x))
  have hxO (S : Finset (CompactOpens X)) : x ∈ O S := by
    change x ∈ (Opens.map (quotient S)).obj (Alexandrov.principalOpen (quotient S x))
    rw [neighborhood_preimage]
    exact self_mem_neighborhood S x
  apply Types.FilteredColimit.isColimitOf' (sectionDiagram F x) (sectionCocone F x)
  · intro a
    obtain ⟨V, hxV, s, hs⟩ := TopCat.Presheaf.exists_germ_eq P a
    obtain ⟨U, hU, hxU, hUV⟩ :=
      (Opens.isBasis_iff_nbhd.mp (PrespectralSpace.isBasis_opens X)) hxV
    let W : CompactOpens X := ⟨⟨U, hU⟩, U.isOpen⟩
    have hWV : O {W} ≤ V := by
      change (Opens.map (quotient {W})).obj
        (Alexandrov.principalOpen (quotient {W} x)) ≤ V
      rw [neighborhood_preimage, neighborhood_singleton W x hxU]
      exact hUV
    refine ⟨{W}, P.map (homOfLE hWV).op s, ?_⟩
    change a = P.germ (O {W}) x (hxO {W}) (P.map (homOfLE hWV).op s)
    exact hs.symm.trans (P.germ_res_apply (homOfLE hWV) x (hxO {W}) s).symm
  · intro S s t hst
    change P.germ (O S) x (hxO S) s = P.germ (O S) x (hxO S) t at hst
    obtain ⟨V, hxV, iV, jV, heq⟩ := P.germ_eq x (hxO S) (hxO S) s t hst
    obtain ⟨T, hTV⟩ := exists_neighborhood_le x V hxV
    have hSV : O (S ∪ T) ≤ V := by
      change (Opens.map (quotient (S ∪ T))).obj
        (Alexandrov.principalOpen (quotient (S ∪ T) x)) ≤ V
      rw [neighborhood_preimage]
      exact (neighborhood_antitone Finset.subset_union_right x).trans hTV
    refine ⟨S ∪ T, homOfLE Finset.subset_union_left, ?_⟩
    let k : O (S ∪ T) ⟶ V := homOfLE hSV
    let r : O (S ∪ T) ⟶ O S := homOfLE (sectionOpen_antitone Finset.subset_union_left x)
    change P.map r.op s = P.map r.op t
    have hi : P.map r.op = P.map iV.op ≫ P.map k.op :=
      (congrArg (fun f : op (O S) ⟶ op (O (S ∪ T)) => P.map f)
        (show r.op = iV.op ≫ k.op from Subsingleton.elim _ _)).trans
          (P.map_comp iV.op k.op)
    have hj : P.map r.op = P.map jV.op ≫ P.map k.op :=
      (congrArg (fun f : op (O S) ⟶ op (O (S ∪ T)) => P.map f)
        (show r.op = jV.op ≫ k.op from Subsingleton.elim _ _)).trans
          (P.map_comp jV.op k.op)
    have his := congrArg (fun f : P.obj (op (O S)) ⟶ P.obj (op (O (S ∪ T))) => f s) hi
    have hjt := congrArg (fun f : P.obj (op (O S)) ⟶ P.obj (op (O (S ∪ T))) => f t) hj
    exact his.trans ((congrArg (P.map k.op) heq).trans hjt.symm)

end SchemeTheory.CompactOpenFiniteModel
