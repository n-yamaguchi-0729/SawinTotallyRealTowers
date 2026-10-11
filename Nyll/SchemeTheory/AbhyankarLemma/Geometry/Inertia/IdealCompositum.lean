/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.GroupTheory.CyclicProjection
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.IdealTower

/-!
# Ideal inertia on a compositum

This file combines the ideal-theoretic restriction map with the cyclic group
calculation in Abhyankar's lemma.  The field-specific construction of the two
restriction homomorphisms is deliberately kept separate.
-/

noncomputable section

universe uR uL uR' uT uG uL' uR''

namespace TameAbhyankar.SGA1

variable {R : Type uR} {SLeft : Type uL} {SRight : Type uR'} {T : Type uT}
variable [CommRing R] [CommRing SLeft] [CommRing SRight] [CommRing T]
variable [Algebra R SLeft] [Algebra SLeft T] [Algebra R T]
  [IsScalarTower R SLeft T]
variable [Algebra R SRight] [Algebra SRight T]
  [IsScalarTower R SRight T]
variable {G : Type uG} {GLeft : Type uL'} {GRight : Type uR''}
variable [Group G] [Group GLeft] [Group GRight]
variable [MulSemiringAction G T]
  [MulSemiringAction GLeft SLeft] [MulSemiringAction GRight SRight]

variable (resLeft : G →* GLeft) (resRight : G →* GRight)
variable (PLeft : Ideal SLeft) (PRight : Ideal SRight) (Q : Ideal T)
variable [Q.LiesOver PLeft] [Q.LiesOver PRight]

/-- If the two homomorphisms on the ambient acting groups are jointly
injective, their restrictions to ideal inertia are jointly injective. -/
theorem idealInertiaRestriction_prod_injective
    (hresLeft : ∀ sigma : G, ∀ x : SLeft,
      algebraMap SLeft T (resLeft sigma • x) = sigma • algebraMap SLeft T x)
    (hresRight : ∀ sigma : G, ∀ x : SRight,
      algebraMap SRight T (resRight sigma • x) = sigma • algebraMap SRight T x)
    (hpair : Function.Injective (resLeft.prod resRight)) :
    Function.Injective
      ((idealInertiaRestriction resLeft PLeft Q hresLeft).prod
        (idealInertiaRestriction resRight PRight Q hresRight)) := by
  intro sigma tau h
  have hleft : resLeft (sigma : G) = resLeft (tau : G) := by
    have := congrArg
      (fun z : PLeft.toAddSubgroup.inertia GLeft ×
          PRight.toAddSubgroup.inertia GRight ↦ ((z.1 : GLeft))) h
    exact this
  have hright : resRight (sigma : G) = resRight (tau : G) := by
    have := congrArg
      (fun z : PLeft.toAddSubgroup.inertia GLeft ×
          PRight.toAddSubgroup.inertia GRight ↦ ((z.2 : GRight))) h
    exact this
  apply Subtype.ext
  exact hpair (Prod.ext hleft hright)

/-- The cyclic group step of Abhyankar's lemma for ideal inertia.

The conclusion includes both injectivity of the right restriction and the
cardinality-one statement for relative inertia, identified with its kernel. -/
theorem idealRelativeInertia_card_eq_one_of_cyclic_of_card_dvd
    [Finite (Q.toAddSubgroup.inertia G)]
    [Finite (PRight.toAddSubgroup.inertia GRight)]
    [IsCyclic (Q.toAddSubgroup.inertia G)]
    [IsCyclic (PLeft.toAddSubgroup.inertia GLeft)]
    (hresLeft : ∀ sigma : G, ∀ x : SLeft,
      algebraMap SLeft T (resLeft sigma • x) = sigma • algebraMap SLeft T x)
    (hresRight : ∀ sigma : G, ∀ x : SRight,
      algebraMap SRight T (resRight sigma • x) = sigma • algebraMap SRight T x)
    (hpair : Function.Injective (resLeft.prod resRight))
    (hright : Function.Surjective
      (idealInertiaRestriction resRight PRight Q hresRight))
    (hcard : Nat.card (PLeft.toAddSubgroup.inertia GLeft) ∣
      Nat.card (PRight.toAddSubgroup.inertia GRight)) :
    Function.Injective
        (idealInertiaRestriction resRight PRight Q hresRight) ∧
      Nat.card (Q.toAddSubgroup.inertia resRight.ker) = 1 := by
  let toLeft := idealInertiaRestriction resLeft PLeft Q hresLeft
  let toRight := idealInertiaRestriction resRight PRight Q hresRight
  have hjoint : Function.Injective (toLeft.prod toRight) :=
    idealInertiaRestriction_prod_injective
      resLeft resRight PLeft PRight Q hresLeft hresRight hpair
  have hinjective : Function.Injective toRight :=
    cyclic_right_projection_injective_of_card_dvd
      toLeft toRight hjoint hright hcard
  refine ⟨hinjective, ?_⟩
  let inclusion := idealRelativeInertiaInclusion (Q := Q) resRight
  have hker : MonoidHom.ker toRight = inclusion.range :=
    idealInertiaRestriction_ker_eq_range_relative
      resRight PRight Q hresRight
  have hkerBot : MonoidHom.ker toRight = ⊥ :=
    (MonoidHom.ker_eq_bot_iff toRight).mpr hinjective
  have hrangeBot : inclusion.range = ⊥ := hker.symm.trans hkerBot
  calc
    Nat.card (Q.toAddSubgroup.inertia resRight.ker) =
        Nat.card inclusion.range :=
      Nat.card_congr
        (Equiv.ofInjective inclusion
          (idealRelativeInertiaInclusion_injective (Q := Q) resRight))
    _ = 1 := by rw [hrangeBot]; simp

end TameAbhyankar.SGA1
