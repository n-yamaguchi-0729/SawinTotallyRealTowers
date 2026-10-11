/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Sites.LocallyInjective
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.QuasiSeparated
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import Mathlib.Topology.Spectral.Prespectral

/-!
# Filtered colimits and sections over compact open subsets

The presheaf colimit of a filtered diagram of sheaves satisfies descent for
every finite open covering. The proof uses the actual finite pairwise
intersection diagram, whose limit expresses the sheaf condition.

Compactness then shows that a locally injective map from this presheaf is
injective on compact opens. When compact opens form a basis and are stable
under intersection, local lifts can be refined to a finite compact-open
cover and glued. In particular, the categorical sheafification unit is
bijective on compact opens, as in Stacks Project, tag 009F, parts (2) and
(4). This supplies the section comparison used in tag 0CAI.

References: https://stacks.math.columbia.edu/tag/009F and
https://stacks.math.columbia.edu/tag/0CAI.
The Lean proof is original.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace TopCat.Presheaf

variable {X : TopCat.{u}} {I : Type u} [SmallCategory I] [IsFiltered I]

/-- A filtered presheaf colimit of sheaves preserves the limit expressing
descent for any finite family of open subsets. -/
theorem filteredColimit_preservesLimit_pairwise
    (F : I ⥤ X.Presheaf (Type u))
    (hF : ∀ i : I, (F.obj i).IsSheaf)
    {ι : Type u} [Finite ι] (U : ι → Opens X) :
    PreservesLimit (Pairwise.diagram U).op (colimit F) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hflip : PreservesLimit (Pairwise.diagram U).op F.flip := by
    apply preservesLimit_of_evaluation F.flip (Pairwise.diagram U).op
    intro i
    change PreservesLimit (Pairwise.diagram U).op (F.obj i)
    exact (hF i).isSheafPreservesLimitPairwiseIntersections U
  have hcomp : PreservesLimit (Pairwise.diagram U).op
      (F.flip ⋙ (colim : (I ⥤ Type u) ⥤ Type u)) := inferInstance
  exact preservesLimit_of_natIso (Pairwise.diagram U).op
    (colimitFlipIsoCompColim F.flip).symm

private theorem eq_of_pairwise_restrictions
    (P : X.Presheaf (Type u)) {ι : Type u} (V : ι → Opens X)
    [PreservesLimit (Pairwise.diagram V).op P]
    (U : Opens X) (iVU : ∀ i : ι, V i ⟶ U) (hcover : U ≤ iSup V)
    (s t : P.obj (op U))
    (h : ∀ i : ι, P.map (iVU i).op s = P.map (iVU i).op t) : s = t := by
  have hU : U = iSup V := le_antisymm hcover (iSup_le (fun i => (iVU i).le))
  subst U
  have hlim : IsLimit (P.mapCone (Pairwise.cocone V).op) :=
    isLimitOfPreserves P (Pairwise.coconeIsColimit V).op
  apply ((Types.isLimit_iff_bijective_sectionOfCone
    (P.mapCone (Pairwise.cocone V).op)).mp ⟨hlim⟩).injective
  apply Subtype.ext
  funext j
  change P.map ((Pairwise.cocone V).ι.app j.unop).op s =
    P.map ((Pairwise.cocone V).ι.app j.unop).op t
  rcases j with ⟨j⟩
  cases j with
  | single i => exact h i
  | pair i j =>
    change P.map ((Opens.infLELeft (V i) (V j)) ≫ iVU i).op s =
      P.map ((Opens.infLELeft (V i) (V j)) ≫ iVU i).op t
    rw [op_comp, P.map_comp, types_comp_apply, types_comp_apply, h i]

/-- Local injectivity becomes injectivity on a compact open for the
presheaf filtered colimit of genuine topological sheaves. -/
theorem filteredColimit_app_injective_of_locallyInjective
    (F : I ⥤ X.Presheaf (Type u))
    (hF : ∀ i : I, (F.obj i).IsSheaf)
    {G : X.Presheaf (Type u)} (φ : colimit F ⟶ G)
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) φ]
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    Function.Injective (φ.app (op U)) := by
  classical
  intro s t hst
  have hlocal := CategoryTheory.Presheaf.equalizerSieve_mem
    (Opens.grothendieckTopology X) φ s t hst
  choose V iVU heq hxV using (fun x : U => hlocal x.1 x.2)
  have hcover : (U : Set X) ⊆ ⋃ x : U, (V x : Set X) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨T, hT⟩ := hU.elim_finite_subcover
    (fun x : U => (V x : Set X)) (fun x => (V x).isOpen) hcover
  let W : T → Opens X := fun i => V i.1
  have hW : U ≤ iSup W := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hT hx)
    exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩
  have hp : PreservesLimit (Pairwise.diagram W).op (colimit F) :=
    filteredColimit_preservesLimit_pairwise F hF W
  exact eq_of_pairwise_restrictions (colimit F) W U
    (fun i => iVU i.1) hW s t (fun i => heq i.1)

/-- Sheafification does not identify distinct sections of the presheaf
filtered colimit over a compact open. The map is the categorical
sheafification unit on the actual topological site. -/
theorem filteredColimit_toSheafify_app_injective
    (F : I ⥤ X.Presheaf (Type u))
    (hF : ∀ i : I, (F.obj i).IsSheaf)
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    Function.Injective
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) (colimit F)).app (op U)) := by
  exact filteredColimit_app_injective_of_locallyInjective F hF
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (colimit F)) U hU

/-- On a space with a compact-open basis and compact intersections of
compact opens, local bijectivity onto a sheaf supplies all sections over
compact opens from the presheaf filtered colimit. -/
theorem filteredColimit_app_surjective_of_locallyBijective
    [PrespectralSpace X] [QuasiSeparatedSpace X]
    (F : I ⥤ X.Presheaf (Type u))
    (hF : ∀ i : I, (F.obj i).IsSheaf)
    {G : X.Sheaf (Type u)} (φ : colimit F ⟶ G.obj)
    [CategoryTheory.Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) φ]
    [CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) φ]
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    Function.Surjective (φ.app (op U)) := by
  classical
  intro s
  let P : X.Presheaf (Type u) := colimit F
  have hlocal := CategoryTheory.Presheaf.imageSieve_mem
    (Opens.grothendieckTopology X) φ s
  have hlifts : ∀ x : U, ∃ V : Opens X, IsCompact (V : Set X) ∧
      x.1 ∈ V ∧ ∃ iVU : V ⟶ U, ∃ t : P.obj (op V),
        φ.app (op V) t = G.obj.map iVU.op s := by
    intro x
    obtain ⟨V, iVU, ⟨t, ht⟩, hxV⟩ := hlocal x.1 x.2
    obtain ⟨W, hW, hxW, hWV⟩ :=
      (Opens.isBasis_iff_nbhd.mp (PrespectralSpace.isBasis_opens X)) hxV
    refine ⟨W, hW, hxW, homOfLE hWV ≫ iVU, P.map (homOfLE hWV).op t, ?_⟩
    calc
      φ.app (op W) (P.map (homOfLE hWV).op t) =
          G.obj.map (homOfLE hWV).op (φ.app (op V) t) :=
        φ.naturality_apply (homOfLE hWV).op t
      _ = G.obj.map (homOfLE hWV).op (G.obj.map iVU.op s) :=
        congrArg (G.obj.map (homOfLE hWV).op) ht
      _ = G.obj.map (homOfLE hWV ≫ iVU).op s := by
        rw [op_comp, G.obj.map_comp, types_comp_apply]
  choose V hcompactV hxV iVU t ht using hlifts
  have hcover : (U : Set X) ⊆ ⋃ x : U, (V x : Set X) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨T, hT⟩ := hU.elim_finite_subcover
    (fun x : U => (V x : Set X)) (fun x => (V x).isOpen) hcover
  let W : T → Opens X := fun i => V i.1
  let sf : ∀ i : T, P.obj (op (W i)) := fun i => t i.1
  have hW : U ≤ iSup W := by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (hT hx)
    exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩
  have hcompatible : IsCompatible P W sf := by
    intro i j
    have hcompact : IsCompact ((W i ⊓ W j : Opens X) : Set X) :=
      QuasiSeparatedSpace.inter_isCompact (W i : Set X) (W j : Set X)
        (W i).isOpen (hcompactV i.1) (W j).isOpen (hcompactV j.1)
    apply filteredColimit_app_injective_of_locallyInjective F hF φ (W i ⊓ W j) hcompact
    change φ.app _ (P.map (Opens.infLELeft (W i) (W j)).op (t i.1)) =
      φ.app _ (P.map (Opens.infLERight (W i) (W j)).op (t j.1))
    rw [φ.naturality_apply, φ.naturality_apply, ht i.1, ht j.1,
      ← types_comp_apply, ← types_comp_apply, ← G.obj.map_comp, ← G.obj.map_comp]
    exact congrArg (fun f : op U ⟶ op (W i ⊓ W j) => G.obj.map f s)
      (Subsingleton.elim _ _)
  have hp : PreservesLimit (Pairwise.diagram W).op P :=
    filteredColimit_preservesLimit_pairwise F hF W
  have hlim : Nonempty (IsLimit (P.mapCone (Pairwise.cocone W).op)) :=
    ⟨isLimitOfPreserves P (Pairwise.coconeIsColimit W).op⟩
  have hgluing : ∃! gl : P.obj (op (iSup W)), IsGluing P W sf gl := by
    obtain ⟨gl, hgl, hunique⟩ := (Types.isLimit_iff _).mp hlim
      (objPairwiseOfFamily sf) hcompatible.sectionPairwise.prop
    refine ⟨gl, isGluing_iff_pairwise.mpr hgl, ?_⟩
    intro gl' hgl'
    exact hunique gl' (isGluing_iff_pairwise.mp hgl')
  obtain ⟨gl, hglue, _⟩ := hgluing
  have hUeq : U = iSup W := le_antisymm hW (iSup_le (fun i => (iVU i.1).le))
  let r : P.obj (op U) := P.map (eqToHom hUeq).op gl
  have hr : ∀ i : T, P.map (iVU i.1).op r = sf i := by
    intro i
    change P.map (iVU i.1).op (P.map (eqToHom hUeq).op gl) = sf i
    rw [← types_comp_apply, ← P.map_comp]
    exact hglue i
  refine ⟨r, ?_⟩
  apply G.eq_of_locally_eq' W U (fun i => iVU i.1) hW
  intro i
  calc
    G.obj.map (iVU i.1).op (φ.app (op U) r) =
        φ.app (op (W i)) (P.map (iVU i.1).op r) :=
      (φ.naturality_apply (iVU i.1).op r).symm
    _ = φ.app (op (W i)) (sf i) := congrArg (φ.app (op (W i))) (hr i)
    _ = G.obj.map (iVU i.1).op s := ht i.1

/-- For a filtered diagram of topological sheaves on a prespectral,
quasi-separated space, sheafification of its presheaf colimit leaves
sections over every compact open unchanged. -/
theorem filteredColimit_toSheafify_app_bijective
    [PrespectralSpace X] [QuasiSeparatedSpace X]
    (F : I ⥤ X.Presheaf (Type u))
    (hF : ∀ i : I, (F.obj i).IsSheaf)
    (U : Opens X) (hU : IsCompact (U : Set X)) :
    Function.Bijective
      ((CategoryTheory.toSheafify (Opens.grothendieckTopology X) (colimit F)).app (op U)) := by
  refine ⟨filteredColimit_toSheafify_app_injective F hF U hU, ?_⟩
  exact filteredColimit_app_surjective_of_locallyBijective F hF
    (G := (presheafToSheaf (Opens.grothendieckTopology X) (Type u)).obj (colimit F))
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (colimit F)) U hU

end TopCat.Presheaf
