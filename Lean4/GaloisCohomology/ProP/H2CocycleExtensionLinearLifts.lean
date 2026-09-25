/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H2CentralExtensionClass

set_option autoImplicit false
/-!
# Linear operations and character corrections on cocycle lifts

The chosen degree-two representatives are linear. Their normalized cocycles therefore
respect addition and scalar multiplication. These identities construct actual sums and
scalar multiples of lifts, while subtracting a continuous coefficient character corrects
a lift without changing its projection.
-/

open scoped Topology

noncomputable section

namespace ClassFieldTower.ProP

open ClassFieldTower.Cohomology FreeProPH2Cocycle

universe u v

variable {p : ℕ} [Fact p.Prime]
variable {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable {H : Type v} [Group H] [TopologicalSpace H]

/-- The fixed representative section respects addition. -/
theorem degreeTwoCocycleRepresentative_add
    (x y : continuousCohomologyZModPLifted p Q 2) :
    degreeTwoCocycleRepresentative (x + y) =
      degreeTwoCocycleRepresentative x + degreeTwoCocycleRepresentative y :=
  map_add (PresentationH2Aux.homologyRepresentativeSection (trivialZModPLifted p Q) 2) x y

/-- The fixed representative section respects coefficient scalars. -/
theorem degreeTwoCocycleRepresentative_smul
    (c : ZMod p) (x : continuousCohomologyZModPLifted p Q 2) :
    degreeTwoCocycleRepresentative (c • x) = c • degreeTwoCocycleRepresentative x :=
  map_smul (PresentationH2Aux.homologyRepresentativeSection (trivialZModPLifted p Q) 2) c x

/-- The fixed representative of zero is zero. -/
theorem degreeTwoCocycleRepresentative_zero :
    degreeTwoCocycleRepresentative (0 : continuousCohomologyZModPLifted p Q 2) = 0 :=
  map_zero (PresentationH2Aux.homologyRepresentativeSection (trivialZModPLifted p Q) 2)

/-- Normalizing a homogeneous cocycle is additive. -/
theorem FreeProPH2Cocycle.normalizedCocycle_add
    (z w : trivialZModPCocyclesLifted p Q 2) (g h : Q) :
    normalizedCocycle (z + w) g h = normalizedCocycle z g h + normalizedCocycle w g h := by
  let C := trivialZModPCochainsLifted p Q
  change ((C.iCycles 2).hom (z + w)).1 1 g (g * h) -
      ((C.iCycles 2).hom (z + w)).1 1 1 1 = _
  rw [map_add]
  change (((C.iCycles 2).hom z).1 1 g (g * h) +
      ((C.iCycles 2).hom w).1 1 g (g * h)) -
      (((C.iCycles 2).hom z).1 1 1 1 + ((C.iCycles 2).hom w).1 1 1 1) =
    (((C.iCycles 2).hom z).1 1 g (g * h) - ((C.iCycles 2).hom z).1 1 1 1) +
      (((C.iCycles 2).hom w).1 1 g (g * h) - ((C.iCycles 2).hom w).1 1 1 1)
  abel

/-- Normalizing a homogeneous cocycle respects coefficient scalars. -/
theorem FreeProPH2Cocycle.normalizedCocycle_smul
    (c : ZMod p) (z : trivialZModPCocyclesLifted p Q 2) (g h : Q) :
    normalizedCocycle (c • z) g h = c • normalizedCocycle z g h := by
  let C := trivialZModPCochainsLifted p Q
  change ((C.iCycles 2).hom (c • z)).1 1 g (g * h) -
      ((C.iCycles 2).hom (c • z)).1 1 1 1 = _
  rw [map_smul]
  exact (smul_sub c _ _).symm

/-- The normalized zero cocycle is zero. -/
theorem FreeProPH2Cocycle.normalizedCocycle_zero (g h : Q) :
    normalizedCocycle (0 : trivialZModPCocyclesLifted p Q 2) g h = 0 := by
  let C := trivialZModPCochainsLifted p Q
  change ((C.iCycles 2).hom 0).1 1 g (g * h) - ((C.iCycles 2).hom 0).1 1 1 1 = 0
  rw [map_zero]
  exact sub_self _

/-- Subtracting a continuous coefficient character corrects a lift's coefficient coordinate. -/
def H2CocycleExtension.twistByCharacter
    (z : trivialZModPCocyclesLifted p Q 2) (s : H →ₜ* H2CocycleExtension z)
    (chi : H →ₜ* Multiplicative (ZMod p)) : H →ₜ* H2CocycleExtension z where
  toFun h := ⟨(s h).left - ULift.up (chi h).toAdd, (s h).right⟩
  map_one' := by
    apply H2CocycleExtension.ext
    · change (s 1).left - ULift.up (chi 1).toAdd = 0
      rw [map_one s, map_one chi]
      exact sub_self _
    · change (s 1).right = 1
      rw [map_one s]
      rfl
  map_mul' a b := by
    apply H2CocycleExtension.ext
    · change (s (a * b)).left - ULift.up (chi (a * b)).toAdd =
        ((s a).left - ULift.up (chi a).toAdd) +
        ((s b).left - ULift.up (chi b).toAdd) +
        normalizedCocycle z (s a).right (s b).right
      rw [map_mul s, map_mul chi]
      apply ULift.ext
      change ((s a).left.down + (s b).left.down +
        (normalizedCocycle z (s a).right (s b).right).down) -
        ((chi a).toAdd + (chi b).toAdd) = _
      change _ = ((s a).left.down - (chi a).toAdd) +
        ((s b).left.down - (chi b).toAdd) +
        (normalizedCocycle z (s a).right (s b).right).down
      abel
    · change (s (a * b)).right = (s a).right * (s b).right
      exact congrArg (fun e : H2CocycleExtension z => e.right) (s.map_mul a b)
  continuous_toFun := by
    rw [continuous_induced_rng]
    have hs := (H2CocycleExtension.toProdHomeomorph z).continuous.comp s.continuous_toFun
    exact (hs.fst.sub (continuous_uliftUp.comp chi.continuous_toFun)).prodMk hs.snd

/-- Character correction preserves the projected group map. -/
theorem H2CocycleExtension.twistByCharacter_projection
    (z : trivialZModPCocyclesLifted p Q 2) (s : H →ₜ* H2CocycleExtension z)
    (chi : H →ₜ* Multiplicative (ZMod p)) :
    (H2CocycleExtension.projection z).comp (H2CocycleExtension.twistByCharacter z s chi) =
      (H2CocycleExtension.projection z).comp s := by
  ext h
  rfl

/-- Add the coefficient coordinates of two lifts with the same base projection. -/
def degreeTwoAddLift
    (x y : continuousCohomologyZModPLifted p Q 2)
    (s : H →ₜ* DegreeTwoCentralExtension x) (t : H →ₜ* DegreeTwoCentralExtension y)
    (hst : (H2CocycleExtension.projection (degreeTwoCocycleRepresentative x)).comp s =
      (H2CocycleExtension.projection (degreeTwoCocycleRepresentative y)).comp t) :
    H →ₜ* DegreeTwoCentralExtension (x + y) where
  toFun h := ⟨(s h).left + (t h).left, (s h).right⟩
  map_one' := by
    apply H2CocycleExtension.ext
    · change (s 1).left + (t 1).left = 0
      rw [map_one s, map_one t]
      exact add_zero _
    · change (s 1).right = 1
      rw [map_one s]
      rfl
  map_mul' a b := by
    have ha : (s a).right = (t a).right := DFunLike.congr_fun hst a
    have hb : (s b).right = (t b).right := DFunLike.congr_fun hst b
    apply H2CocycleExtension.ext
    · change (s (a * b)).left + (t (a * b)).left =
        ((s a).left + (t a).left) + ((s b).left + (t b).left) +
          normalizedCocycle (degreeTwoCocycleRepresentative (x + y)) (s a).right (s b).right
      rw [map_mul s, map_mul t, degreeTwoCocycleRepresentative_add, normalizedCocycle_add]
      change ((s a).left + (s b).left +
          normalizedCocycle (degreeTwoCocycleRepresentative x) (s a).right (s b).right) +
        ((t a).left + (t b).left +
          normalizedCocycle (degreeTwoCocycleRepresentative y) (t a).right (t b).right) = _
      rw [← ha, ← hb]
      abel
    · change (s (a * b)).right = (s a).right * (s b).right
      exact congrArg (fun e : DegreeTwoCentralExtension x => e.right) (s.map_mul a b)
  continuous_toFun := by
    rw [continuous_induced_rng]
    have hs := (H2CocycleExtension.toProdHomeomorph
      (degreeTwoCocycleRepresentative x)).continuous.comp s.continuous_toFun
    have ht := (H2CocycleExtension.toProdHomeomorph
      (degreeTwoCocycleRepresentative y)).continuous.comp t.continuous_toFun
    exact (hs.fst.add ht.fst).prodMk hs.snd

/-- The added lift keeps the common base projection. -/
theorem degreeTwoAddLift_projection
    (x y : continuousCohomologyZModPLifted p Q 2)
    (s : H →ₜ* DegreeTwoCentralExtension x) (t : H →ₜ* DegreeTwoCentralExtension y)
    (hst : (H2CocycleExtension.projection (degreeTwoCocycleRepresentative x)).comp s =
      (H2CocycleExtension.projection (degreeTwoCocycleRepresentative y)).comp t) :
    (H2CocycleExtension.projection (degreeTwoCocycleRepresentative (x + y))).comp
      (degreeTwoAddLift x y s t hst) =
      (H2CocycleExtension.projection (degreeTwoCocycleRepresentative x)).comp s := by
  ext h
  rfl

/-- Scaling the coefficient coordinate lifts the scaled degree-two class. -/
def degreeTwoSmulLift (c : ZMod p) (x : continuousCohomologyZModPLifted p Q 2)
    (s : H →ₜ* DegreeTwoCentralExtension x) : H →ₜ* DegreeTwoCentralExtension (c • x) where
  toFun h := ⟨c • (s h).left, (s h).right⟩
  map_one' := by
    apply H2CocycleExtension.ext
    · change c • (s 1).left = 0
      rw [map_one s]
      exact smul_zero c
    · change (s 1).right = 1
      rw [map_one s]
      rfl
  map_mul' a b := by
    apply H2CocycleExtension.ext
    · change c • (s (a * b)).left =
        c • (s a).left + c • (s b).left +
          normalizedCocycle (degreeTwoCocycleRepresentative (c • x)) (s a).right (s b).right
      rw [map_mul s, degreeTwoCocycleRepresentative_smul, normalizedCocycle_smul]
      change c • ((s a).left + (s b).left +
        normalizedCocycle (degreeTwoCocycleRepresentative x) (s a).right (s b).right) = _
      rw [smul_add, smul_add]
    · change (s (a * b)).right = (s a).right * (s b).right
      exact congrArg (fun e : DegreeTwoCentralExtension x => e.right) (s.map_mul a b)
  continuous_toFun := by
    rw [continuous_induced_rng]
    have hs := (H2CocycleExtension.toProdHomeomorph
      (degreeTwoCocycleRepresentative x)).continuous.comp s.continuous_toFun
    exact (hs.fst.const_smul c).prodMk hs.snd

/-- The scaled lift has the same base projection. -/
theorem degreeTwoSmulLift_projection
    (c : ZMod p) (x : continuousCohomologyZModPLifted p Q 2)
    (s : H →ₜ* DegreeTwoCentralExtension x) :
    (H2CocycleExtension.projection (degreeTwoCocycleRepresentative (c • x))).comp
      (degreeTwoSmulLift c x s) =
      (H2CocycleExtension.projection (degreeTwoCocycleRepresentative x)).comp s := by
  ext h
  rfl

/-- The zero degree-two class has a zero-coordinate lift of every base group map. -/
def degreeTwoZeroLift (q : H →ₜ* Q) :
    H →ₜ* DegreeTwoCentralExtension (0 : continuousCohomologyZModPLifted p Q 2) where
  toFun h := ⟨0, q h⟩
  map_one' := by
    apply H2CocycleExtension.ext
    · rfl
    · exact map_one q
  map_mul' a b := by
    apply H2CocycleExtension.ext
    · change 0 = 0 + 0 + normalizedCocycle
        (degreeTwoCocycleRepresentative (0 : continuousCohomologyZModPLifted p Q 2)) (q a) (q b)
      rw [degreeTwoCocycleRepresentative_zero, normalizedCocycle_zero, add_zero, add_zero]
    · exact map_mul q a b
  continuous_toFun := by
    rw [continuous_induced_rng]
    exact continuous_const.prodMk q.continuous_toFun

/-- The zero-coordinate lift projects to the input map. -/
theorem degreeTwoZeroLift_projection (q : H →ₜ* Q) :
    (H2CocycleExtension.projection
      (degreeTwoCocycleRepresentative (0 : continuousCohomologyZModPLifted p Q 2))).comp
      (degreeTwoZeroLift q) = q := by
  ext h
  rfl

end ClassFieldTower.ProP
