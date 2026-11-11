/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Group.ULift
public import Mathlib.Algebra.Module.ULift
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.CategoryTheory.Action.Limits
public import Mathlib.RepresentationTheory.Rep.Basic
public import Mathlib.RepresentationTheory.Rep.Res

/-!
# One actual universe lift for a representation

The acting group and the coefficient carrier may start in independent universes. The existing
module-category lift and restriction along `MulEquiv.ulift` put both in their maximum universe.
The action, morphisms and finite norm are the original maps under `ULift.up` and `ULift.down`.
No smallness premise or replacement action is used.
-/

@[expose] public section

noncomputable section

universe uR uG uA

open CategoryTheory

namespace Rep

variable (R : Type uR) [Ring R] (G : Type uG) [Monoid G]

/-- Lift the original carrier and acting group to their maximum universe. -/
def universeLiftFunctor :
    Rep.{uA} R G ⥤ Rep.{max uG uA} R (ULift.{uA} G) :=
  RepToAction R G ⋙ (ModuleCat.uliftFunctor.{uG, uA} R).mapAction G ⋙
    ActionToRep R G ⋙ resFunctor (MulEquiv.ulift : ULift.{uA} G ≃* G).toMonoidHom

/-- The carrier is exactly the lift of the original coefficient carrier. -/
theorem universeLiftFunctor_obj_V (A : Rep.{uA} R G) :
    ((universeLiftFunctor R G).obj A).V = ULift.{uG} A := rfl

/-- The lifted action is the original action, with only the explicit type lifts. -/
theorem universeLiftFunctor_obj_ρ_apply (A : Rep.{uA} R G) (g : G) (a : A) :
    ((universeLiftFunctor R G).obj A).ρ (ULift.up g) (ULift.up a) =
      ULift.up (A.ρ g a) := rfl

/-- Each lifted morphism is the original coefficient map under the same type lifts. -/
theorem universeLiftFunctor_map_apply {A B : Rep.{uA} R G} (f : A ⟶ B) (a : A) :
    (universeLiftFunctor R G).map f (ULift.up a) = ULift.up (f a) := rfl

instance universeLiftFunctor_additive : (universeLiftFunctor R G :
      Rep.{uA} R G ⥤ Rep.{max uG uA} R (ULift.{uA} G)).Additive where
  map_add := by
    intro A B f g
    ext a
    rfl

instance universeLiftFunctor_preservesFiniteLimits :
    Limits.PreservesFiniteLimits (universeLiftFunctor R G :
      Rep.{uA} R G ⥤ Rep.{max uG uA} R (ULift.{uA} G)) := by
  dsimp only [universeLiftFunctor]
  infer_instance

instance universeLiftFunctor_preservesFiniteColimits :
    Limits.PreservesFiniteColimits (universeLiftFunctor R G :
      Rep.{uA} R G ⥤ Rep.{max uG uA} R (ULift.{uA} G)) := by
  dsimp only [universeLiftFunctor]
  infer_instance

/-- Short exact sequences retain their actual lifted maps and exactness. -/
theorem universeLiftFunctor_shortExact {S : ShortComplex (Rep.{uA} R G)}
    (hS : S.ShortExact) : (S.map (universeLiftFunctor R G)).ShortExact :=
  hS.map_of_exact (universeLiftFunctor R G)

variable {R G}

/-- Scalar multiplication on the lifted carrier is the original multiplication. -/
theorem universeLiftFunctor_smul_down (A : Rep.{uA} R G) (r : R)
    (a : (universeLiftFunctor R G).obj A) :
    (r • a).down = r • a.down := rfl

section Group

variable {K : Type uG} [Group K] [Fintype K]

/-- The finite norm is the original norm after removing the type lift. -/
theorem universeLiftFunctor_norm_down (A : Rep.{uA} R K) (a : A) :
    (((universeLiftFunctor R K).obj A).norm.asHom.hom (ULift.up a)).down =
      A.norm.asHom.hom a := by
  let B := (universeLiftFunctor R K).obj A
  let down : B →ₗ[R] A := (ULift.moduleEquiv : ULift.{uG} A ≃ₗ[R] A).toLinearMap
  change down (B.ρ.norm (ULift.up a)) = A.ρ.norm a
  have hB : B.ρ.norm (ULift.up a) =
      ∑ g : ULift.{uA} K, B.ρ g (ULift.up a) :=
    LinearMap.sum_apply Finset.univ (fun g : ULift.{uA} K => B.ρ g) (ULift.up a)
  have hA : A.ρ.norm a = ∑ g : K, A.ρ g a :=
    LinearMap.sum_apply Finset.univ (fun g : K => A.ρ g) a
  have hdown : down (∑ g : ULift.{uA} K, B.ρ g (ULift.up a)) =
      ∑ g : ULift.{uA} K, down (B.ρ g (ULift.up a)) :=
    map_sum down (fun g : ULift.{uA} K => B.ρ g (ULift.up a)) Finset.univ
  have haction : (∑ g : ULift.{uA} K, down (B.ρ g (ULift.up a))) =
      ∑ g : ULift.{uA} K, A.ρ g.down a := by
    apply Finset.sum_congr rfl
    intro g _hg
    obtain ⟨g⟩ := g
    exact congrArg (fun z : B => down z) (universeLiftFunctor_obj_ρ_apply R K A g a)
  have hreindex : (∑ g : ULift.{uA} K, A.ρ g.down a) = ∑ g : K, A.ρ g a :=
    (Equiv.ulift : ULift.{uA} K ≃ K).sum_comp (fun g => A.ρ g a)
  exact (congrArg down hB).trans (hdown.trans (haction.trans (hreindex.trans hA.symm)))

end Group

end Rep
