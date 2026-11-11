/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Dynamics.FixedPoints.Basic
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Powers and fixed points of an integer representation

These two pure action laws depend only on the actual representation, independently of the
universes of its acting group and coefficient carrier. Their existing public names are retained
in this lower owner, without any class-field or cohomology import or duplicate alias.
-/

@[expose] public section

universe u v

namespace ClassFormation

/-- Powers in a representation are the iterates of the corresponding
action map. -/
theorem rep_action_pow_eq_iterate {R : Type u} [Group R]
    (B : Rep.{v} ℤ R) (g : R) (n : ℕ) (x : B.V) :
    B.ρ (g ^ n) x = ((B.ρ g)^[n]) x := by
  let : Module ℤ B.V := B.hV2
  rw [map_pow, Module.End.coe_pow]

/-- Every nonnegative power fixes an element fixed by the original group
element. -/
theorem rep_action_pow_fixed {R : Type u} [Group R]
    (B : Rep.{v} ℤ R) (g : R) (x : B.V) (hx : B.ρ g x = x) (n : ℕ) :
    B.ρ (g ^ n) x = x := by
  rw [rep_action_pow_eq_iterate]
  exact Function.IsFixedPt.iterate hx n

end ClassFormation
