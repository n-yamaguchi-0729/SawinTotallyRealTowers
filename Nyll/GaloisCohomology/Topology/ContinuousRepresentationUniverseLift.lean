/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.GroupTheory.Index

/-!
# Continuous representations with independent input universes

The original action on `X` is transported by the actual continuous linear equivalence
`ULift X ≃L[R] X`. Both the group and the coefficient carrier then lie in `max u v`,
as required by the iterated continuous resolution. The scalar ring is unchanged.
In a common universe the original and lifted homogeneous complexes are explicitly
isomorphic, using the usual cochain maps and the inverse group and coefficient lifts.
-/

@[expose] public section

noncomputable section

universe r u v

open CategoryTheory ContRepresentation

/-- A universe lift preserves the continuity of scalar multiplication on the coefficient type. -/
theorem ULift.continuousSMul
    {R : Type r} {A : Type v} [TopologicalSpace R] [TopologicalSpace A]
    [SMul R A] [ContinuousSMul R A] : ContinuousSMul R (ULift.{u} A) :=
  ⟨continuous_uliftUp.comp
    (continuous_fst.smul (continuous_uliftDown.comp continuous_snd))⟩

namespace TopRep

/-- The integral module supplied by a topological representation, for local instance scopes. -/
@[instance_reducible]
def integralModuleOfRepresentation {G : Type u} [Monoid G] (X : TopRep.{v} ℤ G) :
    Module ℤ X := X.hV2

variable {R : Type r} [Ring R] [TopologicalSpace R]
variable {G : Type u} [Group G]

local instance universeLiftIsTopologicalAddGroup
    {A : Type v} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] :
    IsTopologicalAddGroup (ULift.{u} A) := {}

attribute [local instance] ULift.continuousSMul

/-- The actual coefficient action on the lifted carrier and lifted group. -/
def universeLift (X : TopRep.{v} R G) : TopRep.{max u v} R (ULift.{v} G) := by
  let e : ULift.{u} X ≃L[R] X := ContinuousLinearEquiv.ulift
  exact TopRep.of (k := R) (G := ULift.{v} G) (X := ULift.{u} X) ⟨{
    toFun := fun g => e.symm.toContinuousLinearMap.comp
      ((X.ρ g.down).comp e.toContinuousLinearMap)
    map_one' := by
      apply ContinuousLinearMap.ext
      intro x
      change ULift.up (X.ρ 1 x.down) = x
      exact congrArg (fun f : X →L[R] X => ULift.up (f x.down)) (map_one X.ρ)
    map_mul' := by
      intro g h
      apply ContinuousLinearMap.ext
      intro x
      change ULift.up (X.ρ (g.down * h.down) x.down) =
        ULift.up (X.ρ g.down (X.ρ h.down x.down))
      exact congrArg (fun f : X →L[R] X => ULift.up (f x.down))
        (map_mul X.ρ g.down h.down) }⟩

/-- The lifted carrier has exactly the original elements under `ULift`. -/
theorem universeLift_V (X : TopRep.{v} R G) : (universeLift X).V = ULift.{u} X := rfl

/-- Removing the lifts recovers the original action, without changing coefficients. -/
theorem universeLift_ρ_down (X : TopRep.{v} R G) (g : G) (x : X) :
    ((universeLift X).ρ (ULift.up g) (ULift.up x)).down = X.ρ g x := rfl

/-- A coefficient morphism is lifted by conjugation with the same carrier equivalences. -/
def universeLiftMap {X Y : TopRep.{v} R G} (f : X ⟶ Y) :
    universeLift X ⟶ universeLift Y :=
  TopRep.ofHom {
    toContinuousLinearMap :=
      (ContinuousLinearEquiv.ulift : ULift.{u} Y ≃L[R] Y).symm.toContinuousLinearMap.comp
        (f.hom.toContinuousLinearMap.comp
          (ContinuousLinearEquiv.ulift : ULift.{u} X ≃L[R] X).toContinuousLinearMap)
    isIntertwining' := by
      intro g
      apply ContinuousLinearMap.ext
      intro x
      exact congrArg ULift.up (f.hom.isIntertwining g.down x.down) }

/-- The lifted morphism evaluates to the original coefficient morphism. -/
theorem universeLiftMap_down {X Y : TopRep.{v} R G} (f : X ⟶ Y) (x : X) :
    (universeLiftMap f (ULift.up x)).down = f x := rfl

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The original group element, viewed in the lifted topological group. -/
def universeLiftGroupUp : G →ₜ* ULift.{v} G :=
  ⟨(MulEquiv.ulift : ULift.{v} G ≃* G).symm.toMonoidHom, continuous_uliftUp⟩

/-- The lifted group has the original topology and multiplication under `ULift.down`. -/
def universeLiftGroupDown : ULift.{v} G →ₜ* G :=
  ⟨(MulEquiv.ulift : ULift.{v} G ≃* G).toMonoidHom, continuous_uliftDown⟩

omit [IsTopologicalGroup G] in
/-- Joint continuity of the action is preserved by the actual lift. -/
theorem universeLift_action_continuous (X : TopRep.{v} R G)
    (hX : Continuous (fun gx : G × X => X.ρ gx.1 gx.2)) :
    Continuous (fun gx : ULift.{v} G × universeLift X =>
      (universeLift X).ρ gx.1 gx.2) :=
  continuous_uliftUp.comp
    (hX.comp ((continuous_uliftDown.comp continuous_fst).prodMk
      (continuous_uliftDown.comp continuous_snd)))

/-- The actual original open subgroup inside the lifted group. -/
def universeLiftOpenSubgroup (H : OpenSubgroup G) : OpenSubgroup (ULift.{v} G) :=
  H.comap universeLiftGroupDown.toMonoidHom universeLiftGroupDown.continuous_toFun

omit [IsTopologicalGroup G] in
/-- Lifting an open subgroup preserves its actual finite or infinite index. -/
theorem universeLiftOpenSubgroup_index (H : OpenSubgroup G) :
    (universeLiftOpenSubgroup.{u, v} H).toSubgroup.index = H.toSubgroup.index :=
  Subgroup.index_comap_of_surjective H.toSubgroup
    (MulEquiv.ulift : ULift.{v} G ≃* G).surjective

/-- Continuous cohomology of the original input, using its actual lifted homogeneous complex. -/
abbrev universeLiftCohomology (X : TopRep.{v} R G) (n : ℕ) :
    TopModuleCat.{max u v} R := continuousCohomology n (universeLift X)

/-- A degree-one homogeneous primitive retains its original alternating boundary. -/
theorem universeLift_degreeOne_boundary_down (X : TopRep.{v} R G)
    (b : resolutionX (universeLift X) 2) (g h k : G) :
    ((d (universeLift X) 2).hom b (ULift.up g) (ULift.up h) (ULift.up k)).down =
      (b (ULift.up h) (ULift.up k)).down -
        ((b (ULift.up g) (ULift.up k)).down -
          (b (ULift.up g) (ULift.up h)).down) := rfl

private theorem cochainsMap_eq_of_apply_eq
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    {X : TopRep.{u} R G} {Y : TopRep.{u} R H}
    (φ ψ : H →ₜ* G)
    (f : TopRep.res φ.toMonoidHom X ⟶ Y)
    (g : TopRep.res ψ.toMonoidHom X ⟶ Y)
    (hφ : ∀ h, φ h = ψ h) (hfg : ∀ x : X, f x = g x) :
    ContinuousCohomology.cochainsMap (X := X) (Y := Y) φ f =
      ContinuousCohomology.cochainsMap (X := X) (Y := Y) ψ g := by
  have hgroup : φ = ψ := ContinuousMonoidHom.ext hφ
  subst ψ
  have hcoeff : f = g := by
    apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    exact hfg
  exact congrArg
    (fun a : TopRep.res φ.toMonoidHom X ⟶ Y =>
      ContinuousCohomology.cochainsMap (X := X) (Y := Y) φ a) hcoeff

section Common

variable (X : TopRep.{u} R G)

/-- In a common universe the lifted coefficient morphism down is the original carrier map. -/
def universeLiftCommonDown :
    TopRep.res (universeLiftGroupUp.{u, u} (G := G)).toMonoidHom (universeLift X) ⟶ X :=
  TopRep.ofHom {
    toContinuousLinearMap :=
      (ContinuousLinearEquiv.ulift : ULift.{u} X ≃L[R] X).toContinuousLinearMap
    isIntertwining' := fun _ => rfl }

/-- The inverse coefficient morphism inserts only the original carrier lift. -/
def universeLiftCommonUp :
    TopRep.res (universeLiftGroupDown.{u, u} (G := G)).toMonoidHom X ⟶ universeLift X :=
  TopRep.ofHom {
    toContinuousLinearMap :=
      (ContinuousLinearEquiv.ulift : ULift.{u} X ≃L[R] X).symm.toContinuousLinearMap
    isIntertwining' := fun _ => rfl }

/-- The actual cochain comparison with the original common-universe homogeneous complex. -/
def universeLiftCommonCochainIso :
    homogeneousCochains (universeLift X) ≅ homogeneousCochains X where
  hom := ContinuousCohomology.cochainsMap (X := universeLift X) (Y := X)
    (universeLiftGroupUp.{u, u} (G := G)) (universeLiftCommonDown X)
  inv := ContinuousCohomology.cochainsMap (X := X) (Y := universeLift X)
    (universeLiftGroupDown.{u, u} (G := G)) (universeLiftCommonUp X)
  hom_inv_id := by
    rw [← ContinuousCohomology.cochainsMap_comp]
    refine (cochainsMap_eq_of_apply_eq
      (X := universeLift X) (Y := universeLift X)
      ((universeLiftGroupUp.{u, u} (G := G)).comp
        (universeLiftGroupDown.{u, u} (G := G)))
      (ContinuousMonoidHom.id (ULift.{u} G))
      ((TopRep.resFunctor (universeLiftGroupDown.{u, u} (G := G)).toMonoidHom).map
          (universeLiftCommonDown X) ≫ universeLiftCommonUp X)
      (𝟙 (universeLift X)) ?_ ?_).trans
        (ContinuousCohomology.cochainsMap_id (universeLift X))
    · intro g
      rfl
    · intro x
      rfl
  inv_hom_id := by
    rw [← ContinuousCohomology.cochainsMap_comp]
    refine (cochainsMap_eq_of_apply_eq (X := X) (Y := X)
      ((universeLiftGroupDown.{u, u} (G := G)).comp
        (universeLiftGroupUp.{u, u} (G := G)))
      (ContinuousMonoidHom.id G)
      ((TopRep.resFunctor (universeLiftGroupUp.{u, u} (G := G)).toMonoidHom).map
          (universeLiftCommonUp X) ≫ universeLiftCommonDown X)
      (𝟙 X) ?_ ?_).trans (ContinuousCohomology.cochainsMap_id X)
    · intro g
      rfl
    · intro x
      rfl

/-- The cochain comparison evaluates at the same original group elements and coefficient. -/
theorem universeLiftCommonCochainIso_hom_degreeTwo
    (z : (homogeneousCochains (universeLift X)).X 2) (g h k : G) :
    (((universeLiftCommonCochainIso X).hom.f 2) z).1 g h k =
      (z.1 (ULift.up g) (ULift.up h) (ULift.up k)).down := rfl

/-- The actual common-universe cochain comparison commutes with coefficient morphisms. -/
theorem universeLiftCommonCochainIso_natural {X Y : TopRep.{u} R G} (f : X ⟶ Y) :
    ContinuousCohomology.cochainsMap (X := universeLift X) (Y := universeLift Y)
        (ContinuousMonoidHom.id (ULift.{u} G)) (universeLiftMap f) ≫
          (universeLiftCommonCochainIso Y).hom =
      (universeLiftCommonCochainIso X).hom ≫
        ContinuousCohomology.cochainsMap (X := X) (Y := Y) (ContinuousMonoidHom.id G) f := by
  change ContinuousCohomology.cochainsMap (X := universeLift X) (Y := universeLift Y)
      (ContinuousMonoidHom.id (ULift.{u} G)) (universeLiftMap f) ≫
      ContinuousCohomology.cochainsMap (X := universeLift Y) (Y := Y)
        (universeLiftGroupUp.{u, u} (G := G)) (universeLiftCommonDown Y) =
    ContinuousCohomology.cochainsMap (X := universeLift X) (Y := X)
        (universeLiftGroupUp.{u, u} (G := G)) (universeLiftCommonDown X) ≫
      ContinuousCohomology.cochainsMap (X := X) (Y := Y) (ContinuousMonoidHom.id G) f
  have hleft := ContinuousCohomology.cochainsMap_comp
    (X := universeLift X) (Y := universeLift Y) (Z := Y)
    (ContinuousMonoidHom.id (ULift.{u} G))
    (universeLiftGroupUp.{u, u} (G := G))
    (universeLiftMap f) (universeLiftCommonDown Y)
  have hright := ContinuousCohomology.cochainsMap_comp
    (X := universeLift X) (Y := X) (Z := Y)
    (universeLiftGroupUp.{u, u} (G := G)) (ContinuousMonoidHom.id G)
    (universeLiftCommonDown X) f
  exact hleft.symm.trans
    ((cochainsMap_eq_of_apply_eq (X := universeLift X) (Y := Y)
      ((ContinuousMonoidHom.id (ULift.{u} G)).comp
        (universeLiftGroupUp.{u, u} (G := G)))
      ((universeLiftGroupUp.{u, u} (G := G)).comp (ContinuousMonoidHom.id G))
      ((TopRep.resFunctor (universeLiftGroupUp.{u, u} (G := G)).toMonoidHom).map
          (universeLiftMap f) ≫ universeLiftCommonDown Y)
      ((TopRep.resFunctor (ContinuousMonoidHom.id G).toMonoidHom).map
          (universeLiftCommonDown X) ≫ f)
      (fun _ => rfl) (fun _ => rfl)).trans hright)

/-- The lifted cohomology recovers the original cohomology via the actual cochain comparison. -/
def universeLiftCommonCohomologyIso (n : ℕ) :
    universeLiftCohomology X n ≅ continuousCohomology n X :=
  (HomologicalComplex.homologyFunctor (TopModuleCat.{u} R) (ComplexShape.up ℕ) n).mapIso
    (universeLiftCommonCochainIso X)

end Common

end TopRep
