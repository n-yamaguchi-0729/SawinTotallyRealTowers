/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteTypeSubopen
import Nyll.SchemeTheory.Modules.SubmoduleGluingFiniteType
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Finite-type quasicoherent gluing on a union of opens

The two actual opens cover their union in its slice site. Consequently,
the actual glued submodule restricts to a finite-type quasicoherent
module on that union whenever the prescribed local submodules have those
properties and their embedded section submodules agree on the overlap.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace SheafOfModules.Submodule

private theorem coversTop_union {X : Scheme.{u}} (U V : X.Opens) :
    ((Opens.grothendieckTopology X).over (U ⊔ V)).CoversTop
      (fun b : ULift.{u} Bool => cond b.down
        (Over.mk (homOfLE (le_sup_left : U ≤ U ⊔ V)))
        (Over.mk (homOfLE (le_sup_right : V ≤ U ⊔ V)))) := by
  intro W
  apply ((Opens.grothendieckTopology X).mem_over_iff _).mpr
  intro x hx
  have hxUV : x ∈ U ⊔ V := (leOfHom W.hom) hx
  rcases hxUV with hxU | hxV
  · refine ⟨W.left ⊓ U, homOfLE inf_le_left, ?_, ⟨hx, hxU⟩⟩
    apply (Sieve.overEquiv_iff _ _).mpr
    exact ⟨⟨true⟩, ⟨Over.homMk (homOfLE inf_le_right)⟩⟩
  · refine ⟨W.left ⊓ V, homOfLE inf_le_left, ?_, ⟨hx, hxV⟩⟩
    apply (Sieve.overEquiv_iff _ _).mpr
    exact ⟨⟨false⟩, ⟨Over.homMk (homOfLE inf_le_right)⟩⟩

/-- The actual glued submodule has finite type on the union of its two prescribed opens. -/
theorem isFiniteType_glueOn_over_sup {X : Scheme.{u}}
    {M : SheafOfModules.{u} X.ringCatSheaf} (N P : M.Submodule) (U V : X.Opens)
    (h : ∀ (Z : X.Opens) (_a : Z ⟶ U) (_b : Z ⟶ V),
      N.toSubmodule.obj (op Z) = P.toSubmodule.obj (op Z))
    (hN : (N.toSheafOfModules.over U).IsFiniteType)
    (hP : (P.toSheafOfModules.over V).IsFiniteType) :
    ((glueOn N P U V).toSheafOfModules.over (U ⊔ V)).IsFiniteType := by
  apply IsFiniteType.of_coversTop
    ((glueOn N P U V).toSheafOfModules.over (U ⊔ V))
    (fun b : ULift.{u} Bool => cond b.down
      (Over.mk (homOfLE (le_sup_left : U ≤ U ⊔ V)))
      (Over.mk (homOfLE (le_sup_right : V ≤ U ⊔ V)))) (coversTop_union U V)
  intro b
  rcases b with ⟨b⟩
  cases b
  · exact IsFiniteType.iterated_over (glueOn N P U V).toSheafOfModules le_sup_right
      (IsFiniteType.of_iso (C := Over V) (R := X.ringCatSheaf.over V)
        (M := P.toSheafOfModules.over V)
        (N := (glueOn N P U V).toSheafOfModules.over V)
        (glueOnOverIsoRight N P U V h).symm hP)
  · exact IsFiniteType.iterated_over (glueOn N P U V).toSheafOfModules le_sup_left
      (IsFiniteType.of_iso (C := Over U) (R := X.ringCatSheaf.over U)
        (M := N.toSheafOfModules.over U)
        (N := (glueOn N P U V).toSheafOfModules.over U)
        (glueOnOverIsoLeft N P U V h).symm hN)

/-- The actual glued submodule is quasicoherent on the union of its prescribed opens. -/
theorem isQuasicoherent_glueOn_over_sup {X : Scheme.{u}}
    {M : SheafOfModules.{u} X.ringCatSheaf} (N P : M.Submodule) (U V : X.Opens)
    (h : ∀ (Z : X.Opens) (_a : Z ⟶ U) (_b : Z ⟶ V),
      N.toSubmodule.obj (op Z) = P.toSubmodule.obj (op Z))
    (hN : (N.toSheafOfModules.over U).IsQuasicoherent)
    (hP : (P.toSheafOfModules.over V).IsQuasicoherent) :
    ((glueOn N P U V).toSheafOfModules.over (U ⊔ V)).IsQuasicoherent := by
  let C : ULift.{u} Bool → Over (U ⊔ V) := fun b => cond b.down
    (Over.mk (homOfLE (le_sup_left : U ≤ U ⊔ V)))
    (Over.mk (homOfLE (le_sup_right : V ≤ U ⊔ V)))
  have hLocal : ∀ b, (((glueOn N P U V).toSheafOfModules.over (U ⊔ V)).over
      (C b)).IsQuasicoherent := by
    intro b
    rcases b with ⟨b⟩
    cases b
    · exact isQuasicoherent_iterated_over (glueOn N P U V).toSheafOfModules le_sup_right
        ((SheafOfModules.isQuasicoherent (X.ringCatSheaf.over V)).prop_of_iso
          (glueOnOverIsoRight N P U V h).symm hP)
    · exact isQuasicoherent_iterated_over (glueOn N P U V).toSheafOfModules le_sup_left
        ((SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso
          (glueOnOverIsoLeft N P U V h).symm hN)
  exact IsQuasicoherent.of_coversTop
    ((glueOn N P U V).toSheafOfModules.over (U ⊔ V)) C (coversTop_union U V)

end SheafOfModules.Submodule
