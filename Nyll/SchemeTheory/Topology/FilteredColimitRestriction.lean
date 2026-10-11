/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Topology.CompactOpenSections
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.Topology.Sheaves.Functors

/-!
# Surjective global restriction and filtered colimits

If global restriction is surjective at every stage of a filtered diagram,
then it is surjective for any colimit cocone. Only the restriction domain
needs to be compact, prespectral, and quasi-separated: its global-section
functor preserves filtered colimits, and actual sheaf pullback preserves
colimits as a left adjoint. A target section therefore comes from a stage,
where it lifts; naturality of the actual adjunction unit gives the result.

The Lean proof is original.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SchemeTheory

variable {X Y : TopCat.{u}}

/-- Surjectivity of the actual global restriction map is stable under
filtered colimits when global sections on the restriction domain preserve
filtered colimits. Here that preservation follows from compactness and
the prespectral, quasi-separated topology. -/
theorem sheafPullback_globalSections_surjective_of_isColimit
    [PrespectralSpace X] [QuasiSeparatedSpace X] [CompactSpace X]
    (f : X ⟶ Y) {I : Type u} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u))
    (c : Cocone D) (hc : IsColimit c)
    (hD : ∀ i : I, Function.Surjective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app (D.obj i)).hom.app
        (op (⊤ : Opens Y)))) :
    Function.Surjective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app c.pt).hom.app
        (op (⊤ : Opens Y))) := by
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let JY : GrothendieckTopology (Opens Y) := Opens.grothendieckTopology Y
  let L : CategoryTheory.Sheaf JY (Type u) ⥤ CategoryTheory.Sheaf JX (Type u) :=
    TopCat.Sheaf.pullback (Type u) f
  let R : CategoryTheory.Sheaf JX (Type u) ⥤ CategoryTheory.Sheaf JY (Type u) :=
    TopCat.Sheaf.pushforward (Type u) f
  let adj : L ⊣ R := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f
  let ΓX : CategoryTheory.Sheaf JX (Type u) ⥤ Type u :=
    (sheafSections JX (Type u)).obj (op (⊤ : Opens X))
  let ΓY : CategoryTheory.Sheaf JY (Type u) ⥤ Type u :=
    (sheafSections JY (Type u)).obj (op (⊤ : Opens Y))
  have hL : PreservesColimitsOfSize.{u, u} L := adj.leftAdjoint_preservesColimits
  have hΓX : PreservesColimit (D ⋙ L) ΓX :=
    TopCat.Sheaf.preservesColimit_sheafSections_of_isCompact ⊤ isCompact_univ (D ⋙ L)
  let cL : Cocone (D ⋙ L) := L.mapCocone c
  have hcL : IsColimit cL := isColimitOfPreserves L hc
  let cΓ : Cocone ((D ⋙ L) ⋙ ΓX) := ΓX.mapCocone cL
  have hcΓ : IsColimit cΓ := isColimitOfPreserves ΓX hcL
  let ηc : ΓY.obj c.pt ⟶ ΓX.obj (L.obj c.pt) := (adj.unit.app c.pt).hom.app (op ⊤)
  change Function.Surjective ηc
  intro t
  have hrep : ∃ (i : I) (a : ΓX.obj (L.obj (D.obj i))),
      ΓX.map (L.map (c.ι.app i)) a = t :=
    Types.jointly_surjective_of_isColimit hcΓ t
  obtain ⟨i, a, ha⟩ := hrep
  let ηi : ΓY.obj (D.obj i) ⟶ ΓX.obj (L.obj (D.obj i)) :=
    (adj.unit.app (D.obj i)).hom.app (op ⊤)
  have hDi : Function.Surjective ηi := hD i
  obtain ⟨s, hs⟩ := hDi a
  let m : D.obj i ⟶ c.pt := c.ι.app i
  let mY : ΓY.obj (D.obj i) ⟶ ΓY.obj c.pt := ΓY.map m
  let mX : ΓX.obj (L.obj (D.obj i)) ⟶ ΓX.obj (L.obj c.pt) := ΓX.map (L.map m)
  refine ⟨mY s, ?_⟩
  have hn : mY ≫ ηc = ηi ≫ mX :=
    congrArg (fun k : D.obj i ⟶ R.obj (L.obj c.pt) => k.hom.app (op (⊤ : Opens Y)))
      (adj.unit.naturality m)
  have hns : ηc (mY s) = mX (ηi s) :=
    congrArg (fun k : ΓY.obj (D.obj i) ⟶ ΓX.obj (L.obj c.pt) => k s) hn
  exact hns.trans ((congrArg mX hs).trans ha)

end SchemeTheory
