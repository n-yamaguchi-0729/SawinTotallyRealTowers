/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.Rep.Res
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Nyll.GaloisCohomology.Cyclic.IntegralUniverseCohomology

/-!
# Actual coinduction and Shapiro with independent universes

The coinduced carrier consists of the original equivariant functions. Lifting such a function
is identified with the function on the lifted group obtained by evaluation after `ULift.down`
and lifting its value. The subgroup used by native Shapiro is the inverse image of the original
subgroup under that same group lift. Its explicit equivalence with the lifted original subgroup
then identifies the target with the existing independent-universe cohomology owner.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace IntegralGroupCohomology.Universe

variable {G : Type u} [Group G]

/-- The actual original subgroup inside the lifted ambient group. -/
def coindLiftSubgroup (S : Subgroup G) : Subgroup (ULift.{v} G) :=
  S.comap (MulEquiv.ulift : ULift.{v} G ≃* G).toMonoidHom

/-- A lifted subgroup element is the same element of the lifted original subgroup. -/
def coindLiftSubgroupEquiv (S : Subgroup G) :
    (coindLiftSubgroup S : Subgroup (ULift.{max u v} G)) ≃* ULift.{v} S where
  toFun g := ULift.up ⟨g.1.down, g.2⟩
  invFun g := ⟨ULift.up g.down.1, g.down.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

variable {S : Subgroup G}

/-- The original native lifted action restricted along the actual subgroup equivalence. -/
def coindLiftRepresentation (A : Rep.{v} ℤ S) :
    Rep.{max u v} (ULift.{max u v} ℤ)
      (coindLiftSubgroup S : Subgroup (ULift.{max u v} G)) :=
  Rep.res (coindLiftSubgroupEquiv S).toMonoidHom ((nativeFunctor S).obj A)

/-- Lifting coinduction retains the original equivariant function and right-translation action. -/
def nativeCoindIso (A : Rep.{v} ℤ S) :
    (nativeFunctor G).obj (Rep.coind S.subtype A) ≅
      Rep.coind (coindLiftSubgroup S : Subgroup (ULift.{max u v} G)).subtype
        (coindLiftRepresentation A) := by
  let X := (nativeFunctor G).obj (Rep.coind S.subtype A)
  let Y := Rep.coind (coindLiftSubgroup S : Subgroup (ULift.{max u v} G)).subtype
    (coindLiftRepresentation A)
  let : AddCommGroup X.V := X.hV1
  let : Module (ULift.{max u v} ℤ) X.V := X.hV2
  let : AddCommGroup Y.V := Y.hV1
  let : Module (ULift.{max u v} ℤ) Y.V := Y.hV2
  let l : X ≃ₗ[ULift.{max u v} ℤ] Y := {
    toFun := fun f => ⟨fun g => ULift.up (f.down.1 g.down), by
      intro s g
      exact congrArg ULift.up (f.down.2 ⟨s.1.down, s.2⟩ g.down)⟩
    invFun := fun f => ULift.up ⟨fun g => (f.1 (ULift.up g)).down, by
      intro s g
      exact congrArg ULift.down (f.2 ⟨ULift.up s.1, s.2⟩ (ULift.up g))⟩
    left_inv := by
      intro f
      apply ULift.ext
      apply Subtype.ext
      rfl
    right_inv := by
      intro f
      apply Subtype.ext
      rfl
    map_add' := by
      intro f g
      apply Subtype.ext
      rfl
    map_smul' := by
      intro r f
      apply Subtype.ext
      rfl }
  exact Rep.mkIso (Representation.Equiv.mk l (by
    intro g
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    rfl))

/-- The comparison evaluates the same original function at the original group element. -/
theorem nativeCoindIso_hom_apply (A : Rep.{v} ℤ S)
    (f : (nativeFunctor G).obj (Rep.coind S.subtype A)) (g : G) :
    ((nativeCoindIso A).hom f).1 (ULift.up g) = ULift.up (f.down.1 g) := rfl

/-- The inverse comparison removes only the explicit group and carrier lifts. -/
theorem nativeCoindIso_inv_apply (A : Rep.{v} ℤ S)
    (f : Rep.coind (coindLiftSubgroup S : Subgroup (ULift.{max u v} G)).subtype
      (coindLiftRepresentation A)) (g : G) :
    ((nativeCoindIso A).inv f).down.1 g = (f.1 (ULift.up g)).down := rfl

/-- Shapiro for the original coinduced representation with independent group and carrier. -/
def coindIso (A : Rep.{v} ℤ S) (n : ℕ) :
    cohomology (Rep.coind S.subtype A) n ≅ cohomology A n :=
  IntegralGroupCohomology.integerScalars.mapIso
    ((groupCohomology.functor (ULift.{max u v} ℤ) (ULift.{max u v} G) n).mapIso
        (nativeCoindIso A) ≪≫
      groupCohomology.coindIso
        (S := (coindLiftSubgroup S : Subgroup (ULift.{max u v} G)))
        (coindLiftRepresentation A) n ≪≫
        groupCohomology.mapIso
          (A := (nativeFunctor S).obj A) (B := coindLiftRepresentation A)
          (coindLiftSubgroupEquiv S)
          (LinearEquiv.refl (ULift.{max u v} ℤ) ((nativeFunctor S).obj A).V)
          (by
            intro g
            apply LinearMap.ext
            intro a
            rfl) n)

/-- Vanishing transfers through the actual independently lifted coinduction and native Shapiro. -/
theorem coind_subsingleton (A : Rep.{v} ℤ S) (n : ℕ)
    [Subsingleton (cohomology A n)] : Subsingleton (cohomology (Rep.coind S.subtype A) n) :=
  Function.Injective.subsingleton (coindIso A n).toLinearEquiv.injective

end IntegralGroupCohomology.Universe
