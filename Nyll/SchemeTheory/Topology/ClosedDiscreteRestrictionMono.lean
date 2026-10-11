/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
import Mathlib.Topology.Sheaves.Stalks
import Nyll.SchemeTheory.Topology.ClosedDiscreteSheaf
import Nyll.SchemeTheory.Topology.ClosedDiscreteRestriction
import Nyll.SchemeTheory.Topology.ClosedDiscreteStalkOutside
import Nyll.SchemeTheory.Topology.SheafPullbackStalks

/-!
# The supported-function pullback comparison is a monomorphism

On the closed support the actual comparison identifies stalk evaluations.
Outside the support its source stalk is terminal, so its stalk map is
automatically a monomorphism. Stalks then detect that the actual sheaf
comparison is a monomorphism. This is enough to transfer the concrete
function-extension result to the actual inverse-image unit.
The Lean proof is original.
-/

noncomputable section

universe u

open CategoryTheory Limits TopologicalSpace

namespace SchemeTheory

/-- The actual adjoint of restriction on a closed discrete-function
support is a monomorphism; no geometric base-change hypothesis is assumed. -/
theorem mono_closedDiscretePullbackMap {X Y : TopCat.{u}}
    (f : X ⟶ Y) (C : Set Y) (hC : IsClosed C) (A : Type u) :
    Mono (closedDiscretePullbackMap f C A) := by
  let F : CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u) :=
    closedDiscreteSheaf C A
  let G : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) :=
    closedDiscreteSheaf (f ⁻¹' C : Set X) A
  let H : CategoryTheory.Sheaf (Opens.grothendieckTopology X) (Type u) :=
    (TopCat.Sheaf.pullback (Type u) f).obj F
  let δ : H ⟶ G := closedDiscretePullbackMap f C A
  let FP : Y.Presheaf (Type u) := F.obj
  let GP : X.Presheaf (Type u) := G.obj
  let HP : X.Presheaf (Type u) := H.obj
  change Mono δ
  apply (TopCat.Presheaf.mono_iff_stalk_mono δ).mpr
  intro x
  let e : FP.stalk (f x) ≅ HP.stalk x := sheafStalkPullbackIso f F x
  let m : HP.stalk x ⟶ GP.stalk x :=
    (TopCat.Presheaf.stalkFunctor (Type u) x).map δ.hom
  change Mono m
  by_cases hx : f x ∈ C
  · let evF : FP.stalk (f x) ≅ A := closedDiscreteStalkIso C A ⟨f x, hx⟩
    let evG : GP.stalk x ≅ A := closedDiscreteStalkIso (f ⁻¹' C : Set X) A ⟨x, hx⟩
    have he : e.hom ≫ m ≫ evG.hom = evF.hom :=
      closedDiscretePullbackMap_stalk_onSupport f C A ⟨x, hx⟩
    have hc : IsIso (e.hom ≫ m ≫ evG.hom) := he.symm ▸ evF.isIso_hom
    have hm : IsIso m := (isIso_comp_right_iff m evG.hom).mp
      ((isIso_comp_left_iff e.hom (m ≫ evG.hom)).mp hc)
    infer_instance
  · have hFP : IsTerminal (FP.stalk (f x)) := closedDiscreteStalkIsTerminal C hC A (f x) hx
    have hHP : IsTerminal (HP.stalk x) := hFP.ofIso e
    exact hHP.mono_from m

end SchemeTheory
