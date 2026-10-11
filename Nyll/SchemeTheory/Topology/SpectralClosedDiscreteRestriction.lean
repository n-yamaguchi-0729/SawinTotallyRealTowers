/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Topology.Sheaves.Functors
import Nyll.SchemeTheory.Topology.ClosedDiscreteSheaf
import Nyll.SchemeTheory.Topology.ClosedDiscreteRestriction
import Nyll.SchemeTheory.Topology.ClosedDiscreteRestrictionMono
import Nyll.SchemeTheory.Topology.SpectralClosedSubspaceRestriction

/-!
# Extending discrete-valued sections on a closed support

The actual restriction of supported continuous functions is surjective
on global sections under the original hypotheses of Stacks 09ZG. The
proof applies the locally constant extension theorem on the closed
support; the two orders of taking the intersection are exchanged by
their explicit subtype coordinates.

Reference: https://stacks.math.columbia.edu/tag/09ZG.
The Lean proofs are original.
-/

noncomputable section

universe u

open CategoryTheory TopCat TopologicalSpace Topology Opposite

namespace SchemeTheory

variable {X : TopCat.{u}} [SpectralSpace X]

/-- The concrete restriction of supported discrete-valued functions is
surjective on global sections under the original point-closure hypothesis. -/
theorem closedDiscreteRestriction_top_surjective {Z C : Set X}
    (hZ : IsClosed Z) (hC : IsClosed C)
    (hconnected : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X))) (A : Type u) :
    Function.Surjective
      ((closedDiscreteRestriction
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(TopCat.of Z, X)))
        C A).hom.app (op (⊤ : Opens X))) := by
  let Y : TopCat.{u} := TopCat.of Z
  let i : Y ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let D : Set Y := i ⁻¹' C
  let E : Set C := Subtype.val ⁻¹' Z
  let k : C(E, D) :=
    ⟨fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩,
      ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk
        (fun x => x.2)).subtype_mk (fun x => x.1.2)⟩
  let r : closedDiscreteSheaf C A ⟶ (TopCat.Sheaf.pushforward (Type u) i).obj
      (closedDiscreteSheaf D A) := closedDiscreteRestriction i C A
  change Function.Surjective (r.hom.app (op (⊤ : Opens X)))
  intro t
  let t' : TopCat.of {z : D // z.1 ∈ (⊤ : Opens Y)} ⟶ TopCat.discrete.obj A := t
  let d : C(D, {z : D // z.1 ∈ (⊤ : Opens Y)}) :=
    ⟨fun z => ⟨z, True.intro⟩, continuous_id.subtype_mk
      (fun z : D => (show z.1 ∈ (⊤ : Opens Y) from True.intro))⟩
  let tLC : LocallyConstant D (TopCat.discrete.obj A) :=
    ⟨fun z => t' (d z), (IsLocallyConstant.iff_continuous _).mpr
      (t'.hom.continuous.comp d.continuous)⟩
  let g : LocallyConstant E (TopCat.discrete.obj A) := LocallyConstant.comap k tLC
  obtain ⟨sLC, hsLC⟩ :=
    (locallyConstant_closedSupport_restriction_bijective hZ hC hconnected
      (TopCat.discrete.obj A)).surjective g
  let s' : TopCat.of {c : C // c.1 ∈ (⊤ : Opens X)} ⟶ TopCat.discrete.obj A :=
    (TopCat.Hom.equivContinuousMap (TopCat.of {c : C // c.1 ∈ (⊤ : Opens X)})
      (TopCat.discrete.obj A)).symm
      ⟨fun c => sLC c.1, sLC.continuous.comp continuous_subtype_val⟩
  let s : (closedDiscreteSheaf C A).obj.obj (op (⊤ : Opens X)) := s'
  refine ⟨s, ?_⟩
  apply TopCat.hom_ext
  apply ContinuousMap.ext
  intro z
  let e : E := ⟨⟨z.1.1.1, z.1.2⟩, z.1.1.2⟩
  exact congrArg (fun a : LocallyConstant E (TopCat.discrete.obj A) => a e) hsLC

/-- For a closed discrete-function support, global restriction through
the actual inverse-image unit is surjective under the original hypotheses. -/
theorem closedDiscreteSheaf_globalSections_surjective {Z C : Set X}
    (hZ : IsClosed Z) (hC : IsClosed C)
    (hconnected : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X))) (A : Type u) :
    Function.Surjective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
        (TopCat.ofHom (⟨Subtype.val, continuous_subtype_val⟩ : C(TopCat.of Z, X)))).unit.app
          (closedDiscreteSheaf C A)).hom.app (op (⊤ : Opens X))) := by
  let Y : TopCat.{u} := TopCat.of Z
  let i : Y ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let JY : GrothendieckTopology (Opens Y) := Opens.grothendieckTopology Y
  let L : CategoryTheory.Sheaf JX (Type u) ⥤ CategoryTheory.Sheaf JY (Type u) :=
    TopCat.Sheaf.pullback (Type u) i
  let R : CategoryTheory.Sheaf JY (Type u) ⥤ CategoryTheory.Sheaf JX (Type u) :=
    TopCat.Sheaf.pushforward (Type u) i
  let adj : L ⊣ R := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i
  let F : CategoryTheory.Sheaf JX (Type u) := closedDiscreteSheaf C A
  let G : CategoryTheory.Sheaf JY (Type u) := closedDiscreteSheaf (i ⁻¹' C : Set Y) A
  let δ : L.obj F ⟶ G := closedDiscretePullbackMap i C A
  let r : F ⟶ R.obj G := closedDiscreteRestriction i C A
  let P : X.Presheaf (Type u) := F.obj
  let Q : Y.Presheaf (Type u) := G.obj
  let H : Y.Presheaf (Type u) := (L.obj F).obj
  let U : Opens Y := (Opens.map i).obj ⊤
  let η : P.obj (op (⊤ : Opens X)) ⟶ H.obj (op U) := (adj.unit.app F).hom.app (op ⊤)
  let δU : H.obj (op U) ⟶ Q.obj (op U) := δ.hom.app (op U)
  let rU : P.obj (op (⊤ : Opens X)) ⟶ Q.obj (op U) := r.hom.app (op ⊤)
  have hδ : Mono δ := mono_closedDiscretePullbackMap i C hC A
  have hδP : Mono δ.hom := (sheafToPresheaf JY (Type u)).map_mono δ
  have hδU : Mono δU := (NatTrans.mono_iff_mono_app δ.hom).mp hδP (op U)
  have hr : Function.Surjective rU := closedDiscreteRestriction_top_surjective hZ hC hconnected A
  change Function.Surjective η
  intro t
  obtain ⟨s, hs⟩ := hr (δU t)
  refine ⟨s, ?_⟩
  apply (CategoryTheory.mono_iff_injective δU).mp hδU
  have hAdj : adj.unit.app F ≫ R.map δ = r :=
    (adj.homEquiv_unit F G δ).symm.trans ((adj.homEquiv F G).apply_symm_apply r)
  have hU : η ≫ δU = rU :=
    congrArg (fun k : F ⟶ R.obj G => k.hom.app (op (⊤ : Opens X))) hAdj
  have hUs : δU (η s) = rU s :=
    congrArg (fun k : P.obj (op (⊤ : Opens X)) ⟶ Q.obj (op U) => k s) hU
  exact hUs.trans hs

end SchemeTheory
