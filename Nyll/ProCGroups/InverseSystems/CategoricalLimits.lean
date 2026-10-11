/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.InverseSystems.Basic
import Mathlib.Topology.Category.TopCat.Limits.Basic
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# Categorical inverse limits

This file connects the concrete compatible-family inverse limit used by `ProCGroups` with
mathlib's categorical limit API.  Since the index and the stages may live in unrelated universes,
each stage is moved to their common universe with `ULift`; the public comparison formulas make
that lift explicit.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Topology

namespace ProCGroups
namespace InverseSystems
namespace InverseSystem

universe u v

variable {I : Type u} [Preorder I] (S : InverseSystem.{u, v} (I := I))

/-! ## Topological spaces -/

/-- A transition map after moving both stages to the common index/stage universe. -/
def topCatTransition {i j : I} (hij : i ≤ j) :
    TopCat.of (ULift.{u} (S.X j)) ⟶ TopCat.of (ULift.{u} (S.X i)) :=
  TopCat.ofHom
    { toFun := fun x => ULift.up (S.map hij x.down)
      continuous_toFun :=
        continuous_uliftUp.comp ((S.continuous_map hij).comp continuous_uliftDown) }

/-- The contravariant diagram of topological spaces associated to an inverse system. -/
def topCatDiagram : Iᵒᵖ ⥤ TopCat.{max u v} where
  obj i := TopCat.of (ULift.{u} (S.X (unop i)))
  map f := S.topCatTransition (leOfHom f.unop)
  map_id i := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact S.map_id_apply (unop i) x.down
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact (S.map_comp_apply (leOfHom g.unop) (leOfHom f.unop) x.down).symm

/-- A concrete projection, with its codomain moved to the common universe. -/
def topCatProjection (i : I) :
    TopCat.of S.inverseLimit ⟶ TopCat.of (ULift.{u} (S.X i)) :=
  TopCat.ofHom
    { toFun := fun x => ULift.up (S.projection i x)
      continuous_toFun := continuous_uliftUp.comp (S.continuous_projection i) }

/-- The concrete compatible-family inverse limit as a cone in `TopCat`. -/
def topCatCone : Cone S.topCatDiagram where
  pt := TopCat.of S.inverseLimit
  π :=
    { app := fun i => S.topCatProjection (unop i)
      naturality := by
        intro i j f
        apply ConcreteCategory.hom_ext
        intro x
        apply ULift.ext
        exact (S.projection_compatible x (unop j) (unop i) (leOfHom f.unop)).symm }

/-- A categorical cone supplies a compatible family of maps into the original, unlifted stages. -/
private theorem compatibleMapsOfTopCatCone (c : Cone S.topCatDiagram) :
    S.CompatibleMaps (fun i (x : c.pt) => (c.π.app (op i) x).down) := by
  intro i j hij
  funext x
  exact congrArg ULift.down (ConcreteCategory.congr_hom (c.w (homOfLE hij).op) x)

/-- The concrete compatible-family cone is a limit cone in `TopCat`. -/
def topCatConeIsLimit : IsLimit S.topCatCone where
  lift c := TopCat.ofHom
    { toFun := S.inverseLimitLift
        (fun i (x : c.pt) => (c.π.app (op i) x).down)
        (S.compatibleMapsOfTopCatCone c)
      continuous_toFun := S.continuous_inverseLimitLift
        (fun i (x : c.pt) => (c.π.app (op i) x).down)
        (fun i => by
          change Continuous (fun x : c.pt => (c.π.app (op i) x).down)
          exact continuous_uliftDown.comp (c.π.app (op i)).hom.continuous)
        (S.compatibleMapsOfTopCatCone c) }
  fac c i := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    rfl
  uniq c f hf := by
    apply ConcreteCategory.hom_ext
    intro x
    apply S.ext
    intro i
    exact congrArg ULift.down (ConcreteCategory.congr_hom (hf (op i)) x)

/-- The canonical categorical isomorphism from the concrete inverse limit to mathlib's chosen
limit object in `TopCat`. -/
noncomputable def topCatIsoLimit :
    S.topCatCone.pt ≅ limit S.topCatDiagram :=
  S.topCatConeIsLimit.conePointUniqueUpToIso (limit.isLimit _)

/-- The concrete inverse limit is canonically homeomorphic to mathlib's categorical limit in
`TopCat`. -/
noncomputable def homeomorphTopCatLimit :
    S.inverseLimit ≃ₜ (limit S.topCatDiagram : TopCat.{max u v}) :=
  TopCat.homeoOfIso S.topCatIsoLimit

/-- The canonical homeomorphism commutes with every lifted inverse-limit projection. -/
@[simp] theorem limitπ_homeomorphTopCatLimit_apply (i : I) (x : S.inverseLimit) :
    limit.π S.topCatDiagram (op i) (S.homeomorphTopCatLimit x) =
      ULift.up (S.projection i x) := by
  exact ConcreteCategory.congr_hom
    (S.topCatConeIsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (op i)) x

/-! ## Profinite groups -/

section ProfiniteGroups

variable [∀ i, Group (S.X i)] [IsGroupSystem S]
variable [∀ i, IsTopologicalGroup (S.X i)]
variable [∀ i, CompactSpace (S.X i)] [∀ i, TotallyDisconnectedSpace (S.X i)]

local instance (i : I) : TotallyDisconnectedSpace (ULift.{u} (S.X i)) :=
  Homeomorph.ulift.symm.totallyDisconnectedSpace

/-- A transition map of a profinite group inverse system, lifted to the common universe. -/
def transitionContinuousMonoidHom {i j : I} (hij : i ≤ j) :
    ULift.{u} (S.X j) →ₜ* ULift.{u} (S.X i) where
  toFun := fun x => ULift.up (S.map hij x.down)
  map_one' := by
    apply ULift.ext
    exact IsGroupSystem.map_one (S := S) hij
  map_mul' := by
    intro x y
    apply ULift.ext
    exact IsGroupSystem.map_mul (S := S) hij x.down y.down
  continuous_toFun :=
    continuous_uliftUp.comp ((S.continuous_map hij).comp continuous_uliftDown)

/-- A projection of a profinite group inverse limit, lifted to the common universe. -/
def projectionContinuousMonoidHom (i : I) :
    S.inverseLimit →ₜ* ULift.{u} (S.X i) where
  toFun := fun x => ULift.up (S.projection i x)
  map_one' := by
    apply ULift.ext
    exact projection_one (S := S) i
  map_mul' := by
    intro x y
    apply ULift.ext
    exact projection_mul (S := S) i x y
  continuous_toFun := continuous_uliftUp.comp (S.continuous_projection i)

/-- The contravariant diagram in `ProfiniteGrp` associated to a profinite group inverse system. -/
def profiniteGrpDiagram : Iᵒᵖ ⥤ ProfiniteGrp.{max u v} where
  obj i := ProfiniteGrp.of (ULift.{u} (S.X (unop i)))
  map f := ProfiniteGrp.ofHom (S.transitionContinuousMonoidHom (leOfHom f.unop))
  map_id i := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact S.map_id_apply (unop i) x.down
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    exact (S.map_comp_apply (leOfHom g.unop) (leOfHom f.unop) x.down).symm

/-- The concrete compatible-family inverse limit as a cone in `ProfiniteGrp`. -/
def profiniteGrpCone : Cone S.profiniteGrpDiagram where
  pt := ProfiniteGrp.of S.inverseLimit
  π :=
    { app := fun i => ProfiniteGrp.ofHom (S.projectionContinuousMonoidHom (unop i))
      naturality := by
        intro i j f
        apply ConcreteCategory.hom_ext
        intro x
        apply ULift.ext
        exact (S.projection_compatible x (unop j) (unop i) (leOfHom f.unop)).symm }

/-- A cone in `ProfiniteGrp` supplies compatible maps into the original, unlifted stages. -/
private theorem compatibleMapsOfProfiniteGrpCone (c : Cone S.profiniteGrpDiagram) :
    S.CompatibleMaps (fun i (x : c.pt) => (c.π.app (op i) x).down) := by
  intro i j hij
  funext x
  exact congrArg ULift.down (ConcreteCategory.congr_hom (c.w (homOfLE hij).op) x)

/-- The concrete compatible-family cone is a limit cone in `ProfiniteGrp`. -/
def profiniteGrpConeIsLimit : IsLimit S.profiniteGrpCone where
  lift c := ProfiniteGrp.ofHom
    { toFun := S.inverseLimitLift
        (fun i (x : c.pt) => (c.π.app (op i) x).down)
        (S.compatibleMapsOfProfiniteGrpCone c)
      map_one' := by
        apply S.ext
        intro i
        change (c.π.app (op i) 1).down = 1
        exact congrArg ULift.down (c.π.app (op i)).hom.map_one
      map_mul' := by
        intro x y
        apply S.ext
        intro i
        change (c.π.app (op i) (x * y)).down =
          (c.π.app (op i) x).down * (c.π.app (op i) y).down
        exact congrArg ULift.down ((c.π.app (op i)).hom.map_mul x y)
      continuous_toFun := S.continuous_inverseLimitLift
        (fun i (x : c.pt) => (c.π.app (op i) x).down)
        (fun i => by
          change Continuous (fun x : c.pt => (c.π.app (op i) x).down)
          exact continuous_uliftDown.comp (c.π.app (op i)).hom.continuous_toFun)
        (S.compatibleMapsOfProfiniteGrpCone c) }
  fac c i := by
    apply ConcreteCategory.hom_ext
    intro x
    apply ULift.ext
    rfl
  uniq c f hf := by
    apply ConcreteCategory.hom_ext
    intro x
    apply S.ext
    intro i
    exact congrArg ULift.down (ConcreteCategory.congr_hom (hf (op i)) x)

/-- The canonical isomorphism in `ProfiniteGrp` from the concrete inverse limit to mathlib's
chosen categorical limit. -/
noncomputable def profiniteGrpIsoLimit :
    S.profiniteGrpCone.pt ≅ limit S.profiniteGrpDiagram :=
  S.profiniteGrpConeIsLimit.conePointUniqueUpToIso (limit.isLimit _)

/-- The concrete inverse limit is canonically continuously and multiplicatively equivalent to
mathlib's categorical limit in `ProfiniteGrp`. -/
noncomputable def continuousMulEquivProfiniteGrpLimit :
    S.inverseLimit ≃ₜ* (limit S.profiniteGrpDiagram : ProfiniteGrp.{max u v}) :=
  { CompHausLike.homeoOfIso
      ((forget₂ ProfiniteGrp Profinite).mapIso S.profiniteGrpIsoLimit) with
    map_mul' := S.profiniteGrpIsoLimit.hom.hom.map_mul }

/-- The canonical continuous multiplicative equivalence commutes with every lifted projection. -/
@[simp] theorem limitπ_continuousMulEquivProfiniteGrpLimit_apply
    (i : I) (x : S.inverseLimit) :
    limit.π S.profiniteGrpDiagram (op i)
        (S.continuousMulEquivProfiniteGrpLimit x) = ULift.up (S.projection i x) := by
  exact ConcreteCategory.congr_hom
    (S.profiniteGrpConeIsLimit.conePointUniqueUpToIso_hom_comp (limit.isLimit _) (op i)) x

end ProfiniteGroups

end InverseSystem
end InverseSystems
end ProCGroups
