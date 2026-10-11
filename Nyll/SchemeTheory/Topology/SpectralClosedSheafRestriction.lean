/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Spectral.Basic
import Nyll.SchemeTheory.Topology.ClosedDiscreteSheaf
import Nyll.SchemeTheory.Topology.CompactOpenFiniteModels
import Nyll.SchemeTheory.Topology.FiniteModelSheafColimit
import Nyll.SchemeTheory.Topology.FiniteModelSheafDiagram
import Nyll.SchemeTheory.Topology.FiniteProductRestriction
import Nyll.SchemeTheory.Topology.FiniteSkyscraperEmbedding
import Nyll.SchemeTheory.Topology.FilteredColimitRestriction
import Nyll.SchemeTheory.Topology.PullbackFiniteSkyscraperEmbedding
import Nyll.SchemeTheory.Topology.PullbackSkyscraperClosedDiscrete
import Nyll.SchemeTheory.Topology.SpecializationCofinalRestriction
import Nyll.SchemeTheory.Topology.SpectralClosedDiscreteRestriction
import Nyll.SchemeTheory.Topology.SpectralClosedSubspaceRestriction

/-!
# Global sections restrict bijectively along the spectral closed subset

Let `Z` be closed in a spectral space `X`, and suppose every point closure
meets `Z` in a connected nonempty set. The actual inverse-image unit gives
a bijection from sections of any sheaf on `X` to its sections on `Z`.

The proof uses the actual filtered colimit of finite-model approximations.
Each approximation embeds in a finite product of pulled-back skyscrapers,
which are actual discrete-function sheaves on closed supports. The closed
support extension theorem supplies surjectivity for these factors; finite
products, subobjects, and filtered colimits transfer it to the given sheaf.
Specialization-cofinality gives injectivity directly.

Reference: Stacks Project, tag 09ZG,
https://stacks.math.columbia.edu/tag/09ZG.
The Lean proof is original.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace Topology Opposite

namespace SchemeTheory

/-- Under the original spectral, closed, and connected point-closure
hypotheses, the actual sheaf restriction map on global sections is bijective. -/
@[stacks 09ZG]
theorem sheaf_globalSections_restriction_bijective
    {X : TopCat.{u}} [SpectralSpace X] {Z : Set X} (hZ : IsClosed Z)
    (hconnected : ∀ x : X, IsConnected (Z ∩ closure ({x} : Set X)))
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u)) :
    Function.Bijective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u)
        (TopCat.ofHom
          (⟨Subtype.val, continuous_subtype_val⟩ : C(TopCat.of Z, X)))).unit.app F).hom.app
        (op (⊤ : Opens X))) := by
  classical
  let Y : TopCat.{u} := TopCat.of Z
  let i : Y ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  have hcofinal : ∀ x : X, ∃ z : Y, x ⤳ i z := by
    intro x
    obtain ⟨z, hzZ, hxz⟩ := (hconnected x).nonempty
    exact ⟨⟨z, hzZ⟩, specializes_iff_mem_closure.mpr hxz⟩
  refine ⟨sheafPullback_globalSections_injective i hcofinal F, ?_⟩
  have hY : SpectralSpace Y := spectralSpace_closedSubtype hZ
  let D := CompactOpenFiniteModel.sheafDiagram F
  refine sheafPullback_globalSections_surjective_of_isColimit i D
    (CompactOpenFiniteModel.sheafCocone F)
    (CompactOpenFiniteModel.sheafCoconeIsColimit F) ?_
  intro S
  let T : TopCat.{u} := CompactOpenFiniteModel.Space S
  have hT : Finite T := CompactOpenFiniteModel.finite_space S
  let q : X ⟶ T := CompactOpenFiniteModel.quotient S
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let JT : GrothendieckTopology (Opens T) := Opens.grothendieckTopology T
  let G : CategoryTheory.Sheaf JT (Type u) := (TopCat.Sheaf.pushforward (Type u) q).obj F
  let L : CategoryTheory.Sheaf JT (Type u) ⥤ CategoryTheory.Sheaf JX (Type u) :=
    TopCat.Sheaf.pullback (Type u) q
  let P : T.Presheaf (Type u) := G.obj
  let K : T → CategoryTheory.Sheaf JX (Type u) := fun y => L.obj (stalkSkyscraper G y)
  have hK : ∀ y : T, Function.Surjective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) i).unit.app (K y)).hom.app
        (op (⊤ : Opens X))) := by
    intro y
    let A : Type u := P.stalk y
    let C : Set X := q ⁻¹' closure ({y} : Set T)
    have hC : IsClosed C := isClosed_closure.preimage q.hom.continuous
    let e : K y ≅ closedDiscreteSheaf C A := pullbackSkyscraperClosedDiscreteIso q y A
    exact sheafPullback_globalSections_surjective_of_mono i hcofinal e.hom
      (closedDiscreteSheaf_globalSections_surjective hZ hC hconnected A)
  let m : D.obj S ⟶ ∏ᶜ K := pullbackToStalkSkyscrapers q G
  have hm : Mono m := mono_pullbackToStalkSkyscrapers q G
  exact sheafPullback_globalSections_surjective_of_mono i hcofinal m
    (sheafPullback_globalSections_surjective_pi i K hK)

end SchemeTheory
