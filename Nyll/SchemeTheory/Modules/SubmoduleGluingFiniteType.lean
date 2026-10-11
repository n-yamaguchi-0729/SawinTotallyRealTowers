/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.FiniteTypeLocality
import Nyll.SchemeTheory.Modules.FiniteTypeRestriction
import Nyll.SchemeTheory.Modules.SubmoduleGluingQuasicoherent

/-!
# Finite type of the actual gluing of submodules

Actual finite-type submodules on the two covering slice sites glue to a
finite-type submodule. The finite-type proof uses only their generating
families; it imposes no finite-presentation or Noetherian hypothesis.
-/

noncomputable section

universe u v₁ u₁

open CategoryTheory Opposite

namespace SheafOfModules.Submodule

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The actual glued submodule is finite type if its two prescribed local modules are. -/
theorem isFiniteType_glueOn {M : SheafOfModules.{u} R}
    (N P : M.Submodule) (U V : C)
    (hCover : J.CoversTop (fun b : ULift.{u} Bool => cond b.down U V))
    (h : ∀ (Z : C) (_a : Z ⟶ U) (_b : Z ⟶ V),
      N.toSubmodule.obj (op Z) = P.toSubmodule.obj (op Z))
    (hN : (N.toSheafOfModules.over U).IsFiniteType)
    (hP : (P.toSheafOfModules.over V).IsFiniteType) :
    (glueOn N P U V).toSheafOfModules.IsFiniteType := by
  apply SheafOfModules.IsFiniteType.of_coversTop
    (glueOn N P U V).toSheafOfModules
    (fun b : ULift.{u} Bool => cond b.down U V) hCover
  intro b
  rcases b with ⟨b⟩
  cases b
  · exact SheafOfModules.IsFiniteType.of_iso
      (glueOnOverIsoRight N P U V h).symm hP
  · exact SheafOfModules.IsFiniteType.of_iso
      (glueOnOverIsoLeft N P U V h).symm hN

/-- The native restricted submodule is finite type whenever the original one is. -/
theorem isFiniteType_over [CategoryTheory.Limits.HasPullbacks C] {M : SheafOfModules.{u} R}
    (N : M.Submodule) (U : C) (hN : N.toSheafOfModules.IsFiniteType) :
    (N.over U).toSheafOfModules.IsFiniteType :=
  SheafOfModules.IsFiniteType.of_iso (overSheafIso N U).symm
    (SheafOfModules.IsFiniteType.over N.toSheafOfModules U hN)

end SheafOfModules.Submodule
