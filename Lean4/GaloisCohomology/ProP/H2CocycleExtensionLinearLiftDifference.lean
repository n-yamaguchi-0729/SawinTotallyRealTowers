/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H2CocycleExtensionLinearLifts
import GaloisCohomology.ProP.H2CocycleExtensionLiftDifference

set_option autoImplicit false
/-!
# Difference calculations for linear and character-corrected lifts

These formulas use the actual coefficient coordinates of the existing lifts.
In particular, agreement of a correction character with the lift difference on
a subgroup is exactly the condition for the corrected lift to kill that subgroup.
-/

open scoped Topology

noncomputable section

namespace ClassFieldTower.ProP

open ClassFieldTower.Cohomology FreeProPH2Cocycle

universe u v w

variable {p : ℕ} [Fact p.Prime]
variable {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable {H : Type v} [Group H] [TopologicalSpace H]

namespace H2CocycleExtension

/-- Differences of three lifts add, with multiplicative notation for characters. -/
theorem liftDifference_trans
    (z : trivialZModPCocyclesLifted p Q 2)
    (s t r : H →ₜ* H2CocycleExtension z)
    (hst : (projection z).comp s = (projection z).comp t)
    (htr : (projection z).comp t = (projection z).comp r) :
    liftDifference z s r (hst.trans htr) =
      liftDifference z s t hst * liftDifference z t r htr := by
  ext h
  apply Multiplicative.toAdd.injective
  change (s h).left.down - (r h).left.down =
    ((s h).left.down - (t h).left.down) + ((t h).left.down - (r h).left.down)
  abel

omit [Fact p.Prime] in
/-- Lift differences commute with actual restriction along a continuous homomorphism. -/
theorem liftDifference_comp
    {J : Type w} [Group J] [TopologicalSpace J]
    (z : trivialZModPCocyclesLifted p Q 2)
    (s t : H →ₜ* H2CocycleExtension z)
    (hst : (projection z).comp s = (projection z).comp t)
    (f : J →ₜ* H) :
    (liftDifference z s t hst).comp f =
      liftDifference z (s.comp f) (t.comp f)
        (by ext h; exact DFunLike.congr_fun hst (f h)) := by
  ext h
  rfl

/-- Character correction subtracts that character from the lift difference. -/
theorem twistByCharacter_liftDifference
    (z : trivialZModPCocyclesLifted p Q 2)
    (s t : H →ₜ* H2CocycleExtension z)
    (hst : (projection z).comp s = (projection z).comp t)
    (chi : H →ₜ* Multiplicative (ZMod p)) :
    liftDifference z (twistByCharacter z s chi) t
        ((twistByCharacter_projection z s chi).trans hst) =
      liftDifference z s t hst / chi := by
  ext h
  apply Multiplicative.toAdd.injective
  change ((s h).left.down - (chi h).toAdd) - (t h).left.down =
    ((s h).left.down - (t h).left.down) - (chi h).toAdd
  abel

/-- Relative to a lift killing `N`, a character correction kills `N` exactly
when its restriction agrees with the original difference character. -/
theorem twistByCharacter_kills_subgroup_iff
    (z : trivialZModPCocyclesLifted p Q 2)
    (s t : H →ₜ* H2CocycleExtension z)
    (hst : (projection z).comp s = (projection z).comp t)
    (chi : H →ₜ* Multiplicative (ZMod p))
    (N : Subgroup H) (ht : N ≤ t.toMonoidHom.ker) :
    N ≤ (twistByCharacter z s chi).toMonoidHom.ker ↔
      (liftDifference z s t hst).comp (subgroupInclusion N) =
        chi.comp (subgroupInclusion N) := by
  rw [← liftDifference_restrict_eq_one_iff z (twistByCharacter z s chi) t
    ((twistByCharacter_projection z s chi).trans hst) N ht,
    twistByCharacter_liftDifference z s t hst chi]
  constructor
  · intro hd
    apply ContinuousMonoidHom.ext
    intro h
    apply div_eq_one.mp
    exact DFunLike.congr_fun hd h
  · intro hd
    apply ContinuousMonoidHom.ext
    intro h
    apply div_eq_one.mpr
    exact DFunLike.congr_fun hd h

end H2CocycleExtension

/-- Differences of added lifts are the sums of the two original differences. -/
theorem degreeTwoAddLift_liftDifference
    (x y : continuousCohomologyZModPLifted p Q 2)
    (s s' : H →ₜ* DegreeTwoCentralExtension x)
    (t t' : H →ₜ* DegreeTwoCentralExtension y)
    (hs : (H2CocycleExtension.projection (degreeTwoCocycleRepresentative x)).comp s =
      (H2CocycleExtension.projection (degreeTwoCocycleRepresentative x)).comp s')
    (ht : (H2CocycleExtension.projection (degreeTwoCocycleRepresentative y)).comp t =
      (H2CocycleExtension.projection (degreeTwoCocycleRepresentative y)).comp t')
    (hst : (H2CocycleExtension.projection (degreeTwoCocycleRepresentative x)).comp s =
      (H2CocycleExtension.projection (degreeTwoCocycleRepresentative y)).comp t) :
    H2CocycleExtension.liftDifference (degreeTwoCocycleRepresentative (x + y))
        (degreeTwoAddLift x y s t hst)
        (degreeTwoAddLift x y s' t' (hs.symm.trans (hst.trans ht)))
        (by rw [degreeTwoAddLift_projection, degreeTwoAddLift_projection]; exact hs) =
      H2CocycleExtension.liftDifference (degreeTwoCocycleRepresentative x) s s' hs *
        H2CocycleExtension.liftDifference (degreeTwoCocycleRepresentative y) t t' ht := by
  ext h
  apply Multiplicative.toAdd.injective
  change ((s h).left.down + (t h).left.down) - ((s' h).left.down + (t' h).left.down) =
    ((s h).left.down - (s' h).left.down) + ((t h).left.down - (t' h).left.down)
  abel

/-- An added lift kills every subgroup killed by both summands. -/
theorem degreeTwoAddLift_kills_subgroup
    (x y : continuousCohomologyZModPLifted p Q 2)
    (s : H →ₜ* DegreeTwoCentralExtension x) (t : H →ₜ* DegreeTwoCentralExtension y)
    (hst : (H2CocycleExtension.projection (degreeTwoCocycleRepresentative x)).comp s =
      (H2CocycleExtension.projection (degreeTwoCocycleRepresentative y)).comp t)
    (N : Subgroup H) (hs : N ≤ s.toMonoidHom.ker) (ht : N ≤ t.toMonoidHom.ker) :
    N ≤ (degreeTwoAddLift x y s t hst).toMonoidHom.ker := by
  intro h hh
  apply H2CocycleExtension.ext
  · change (s h).left + (t h).left = 0
    rw [show s h = 1 from hs hh, show t h = 1 from ht hh]
    exact add_zero _
  · change (s h).right = 1
    rw [show s h = 1 from hs hh]
    rfl

/-- The zero-coordinate lift kills exactly the kernel of its base map. -/
theorem degreeTwoZeroLift_ker (q : H →ₜ* Q) :
    (degreeTwoZeroLift (p := p) q).toMonoidHom.ker = q.toMonoidHom.ker := by
  ext h
  constructor
  · intro hh
    exact congrArg (fun e : DegreeTwoCentralExtension
      (0 : continuousCohomologyZModPLifted p Q 2) ↦ e.right) hh
  · intro hh
    apply H2CocycleExtension.ext
    · rfl
    · exact hh

end ClassFieldTower.ProP
