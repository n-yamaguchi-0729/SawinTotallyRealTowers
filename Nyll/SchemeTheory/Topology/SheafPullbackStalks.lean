/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Unique
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Sheafify
import Mathlib.Topology.Sheaves.Stalks

/-!
# Stalks of the actual inverse-image sheaf

The chosen left adjoint defining topological sheaf pullback is compared
with sheafification of presheaf pullback. The adjunction units are related
using uniqueness of the left adjoint and the unit formula for restricting
an adjunction to a full subcategory. The stalk comparison is then built
from presheaf pullback and invariance of stalks under sheafification.

The Lean proofs are original.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SchemeTheory

variable {X Y : TopCat.{u}}

/-- The actual sheaf pullback unit becomes the composed presheaf-pullback
and sheafification unit under the canonical comparison isomorphism. -/
theorem sheafPullback_unit_comparison (f : X ⟶ Y)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u)) :
    ((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app F).hom ≫
        (TopCat.Presheaf.pushforward (Type u) f).map
          (((TopCat.Sheaf.pullbackIso (Type u) f).hom.app F).hom) =
      (TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).unit.app F.obj ≫
        (TopCat.Presheaf.pushforward (Type u) f).map
          (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
            ((TopCat.Presheaf.pullback (Type u) f).obj F.obj)) := by
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let JY : GrothendieckTopology (Opens Y) := Opens.grothendieckTopology Y
  let adj := (Opens.map f).sheafAdjunctionContinuous (Type u) JY JX
  let adj' := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Opens.map f) (Type u) JY JX
  have hu := Adjunction.unit_leftAdjointUniq_hom_app adj adj' F
  have hforget := congrArg
    (fun a : F ⟶ (TopCat.Sheaf.pushforward (Type u) f).obj
      ((Functor.sheafPullbackConstruction.sheafPullback
        (Opens.map f) (Type u) JY JX).obj F) => a.hom) hu
  let adjP := (TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f).comp
    (sheafificationAdjunction JX (Type u))
  have hrestrict := Adjunction.map_restrictFullyFaithful_unit_app
    (L := Functor.sheafPullbackConstruction.sheafPullback
      (Opens.map f) (Type u) JY JX)
    (R := (Opens.map f).sheafPushforwardContinuous (Type u) JY JX) adjP
    (fullyFaithfulSheafToPresheaf JY (Type u))
    (Functor.FullyFaithful.id _) (Iso.refl _) (Iso.refl _) F
  have hcomp := Adjunction.comp_unit_app
    (TopCat.Presheaf.pullbackPushforwardAdjunction (Type u) f)
    (sheafificationAdjunction JX (Type u)) F.obj
  let Q : CategoryTheory.Sheaf JX (Type u) :=
    ((TopCat.Presheaf.pullback (Type u) f ⋙ presheafToSheaf JX (Type u)).obj F.obj)
  let R₀ : CategoryTheory.Sheaf JX (Type u) ⥤ (Opens Y)ᵒᵖ ⥤ Type u :=
    sheafToPresheaf JX (Type u) ⋙ (TopCat.Presheaf.pushforward (Type u) f)
  let η : F.obj ⟶ R₀.obj Q := adjP.unit.app F.obj
  let η' : F.obj ⟶ R₀.obj Q := (adj'.unit.app F).hom
  have hconstructed : η' = η := by
    have hu' : η' = η ≫ R₀.map (𝟙 Q) ≫ 𝟙 (R₀.obj Q) := hrestrict
    exact hu'.trans (by rw [R₀.map_id Q, Category.comp_id, Category.comp_id])
  exact hforget.trans (hconstructed.trans hcomp)

/-- The stalk of the actual inverse-image sheaf at `x` is canonically
isomorphic to the original stalk at `f x`. -/
def sheafStalkPullbackIso (f : X ⟶ Y)
    (F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u)) (x : X) :
    TopCat.Presheaf.stalk F.obj (f x) ≅
      TopCat.Presheaf.stalk ((TopCat.Sheaf.pullback (Type u) f).obj F).obj x := by
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let P : X.Presheaf (Type u) := (TopCat.Presheaf.pullback (Type u) f).obj F.obj
  let H : X.Presheaf (Type u) := CategoryTheory.sheafify JX P
  let τ : P ⟶ H := CategoryTheory.toSheafify JX P
  let T : X.Presheaf (Type u) ⥤ Type u := TopCat.Presheaf.stalkFunctor (Type u) x
  let mτ : P.stalk x ⟶ H.stalk x := T.map τ
  have hτ : IsIso mτ :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x (Type u) P
  let eτ : P.stalk x ≅ H.stalk x := asIso mτ
  let e : CategoryTheory.sheafify JX P ≅
      ((TopCat.Sheaf.pullback (Type u) f).obj F).obj :=
    (sheafToPresheaf JX (Type u)).mapIso
      ((TopCat.Sheaf.pullbackIso (Type u) f).app F).symm
  exact TopCat.Presheaf.stalkPullbackIso (Type u) f F.obj x ≪≫ eτ ≪≫ T.mapIso e

end SchemeTheory
