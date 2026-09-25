/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H2CocycleExtension
import GaloisCohomology.ProP.QuotientRestriction

set_option autoImplicit false
/-!
# Differences of lifts to a central cocycle extension

Two continuous lifts of the same group map differ by a continuous coefficient
character.  The cocycle terms cancel because their base coordinates agree.
The construction takes values in `ZMod p` itself, so it can be restricted to
inertia and used directly with arithmetic degree-one character APIs.
-/

open scoped Topology

namespace ClassFieldTower.ProP.H2CocycleExtension

open ClassFieldTower.Cohomology FreeProPH2Cocycle

noncomputable section

universe u v

variable {p : ℕ}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H]
variable (z : trivialZModPCocyclesLifted p G 2)
variable (s t : H →ₜ* H2CocycleExtension z)
variable (hst : (projection z).comp s = (projection z).comp t)

/-- The coefficient character measuring the difference between two lifts of
one base-group map. -/
def liftDifference : H →ₜ* Multiplicative (ZMod p) where
  toFun h := Multiplicative.ofAdd ((s h).left.down - (t h).left.down)
  map_one' := by
    change (s 1).left.down - (t 1).left.down = 0
    rw [map_one s, map_one t]
    exact sub_self _
  map_mul' a b := by
    have ha : (s a).right = (t a).right := DFunLike.congr_fun hst a
    have hb : (s b).right = (t b).right := DFunLike.congr_fun hst b
    change (s (a * b)).left.down - (t (a * b)).left.down =
      ((s a).left.down - (t a).left.down) +
        ((s b).left.down - (t b).left.down)
    rw [map_mul s, map_mul t]
    change ((s a).left.down + (s b).left.down +
        (normalizedCocycle z (s a).right (s b).right).down) -
      ((t a).left.down + (t b).left.down +
        (normalizedCocycle z (t a).right (t b).right).down) = _
    rw [ha, hb]
    abel
  continuous_toFun := by
    change Continuous fun h => (s h).left.down - (t h).left.down
    have hleft : Continuous fun e : H2CocycleExtension z => e.left :=
      continuous_fst.comp (toProdHomeomorph z).continuous
    exact (continuous_uliftDown.comp (hleft.comp s.continuous_toFun)).sub
      (continuous_uliftDown.comp (hleft.comp t.continuous_toFun))

/-- Evaluation uses the difference of the lifted coefficient coordinates. -/
@[simp]
theorem liftDifference_apply (h : H) :
    liftDifference z s t hst h =
      Multiplicative.ofAdd ((s h).left.down - (t h).left.down) := rfl

/-- The difference vanishes at an element precisely when the lifts agree there. -/
theorem liftDifference_apply_eq_one_iff (h : H) :
    liftDifference z s t hst h = 1 ↔ s h = t h := by
  change ((s h).left.down - (t h).left.down = 0) ↔ s h = t h
  rw [sub_eq_zero]
  constructor
  · intro hleft
    exact H2CocycleExtension.ext z (ULift.ext _ _ hleft) (DFunLike.congr_fun hst h)
  · intro hst'
    exact congrArg (fun e : H2CocycleExtension z => e.left.down) hst'

/-- The difference character is trivial precisely when the two lifts coincide. -/
theorem liftDifference_eq_one_iff :
    liftDifference z s t hst = 1 ↔ s = t := by
  constructor
  · intro hd
    apply ContinuousMonoidHom.ext
    intro h
    exact (liftDifference_apply_eq_one_iff z s t hst h).mp
      (DFunLike.congr_fun hd h)
  · intro hst'
    apply ContinuousMonoidHom.ext
    intro h
    exact (liftDifference_apply_eq_one_iff z s t hst h).mpr
      (DFunLike.congr_fun hst' h)

/-- Relative to a lift killing a subgroup, the difference character restricts
trivially exactly when the other lift also kills that subgroup. -/
theorem liftDifference_restrict_eq_one_iff (N : Subgroup H)
    (ht : N ≤ t.toMonoidHom.ker) :
    (liftDifference z s t hst).comp (subgroupInclusion N) = 1 ↔
      N ≤ s.toMonoidHom.ker := by
  constructor
  · intro hd h hN
    have he := (liftDifference_apply_eq_one_iff z s t hst h).mp
      (DFunLike.congr_fun hd ⟨h, hN⟩)
    exact he.trans (ht hN)
  · intro hs
    apply ContinuousMonoidHom.ext
    intro h
    exact (liftDifference_apply_eq_one_iff z s t hst h.1).mpr
      ((hs h.2).trans (ht h.2).symm)

end

end ClassFieldTower.ProP.H2CocycleExtension

