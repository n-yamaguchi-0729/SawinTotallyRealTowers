/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnitPadicAction.PadicReductionContinuous
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The topological inverse limit of prime-power residue rings

The actual p-adic integers, with their metric topology, are the ring of
compatible residues. Reduction gives the forward map. Its inverse is
constructed by the universal property of the p-adic completion, and is
continuous because reduction is a continuous bijection from a compact space
to a Hausdorff space. No limit comparison is assumed.
-/

noncomputable section

namespace LocalFieldTheory.PadicResidues

variable (p : ℕ)

/-- The subring of all compatible prime-power residues, including level zero. -/
def compatibleResidues : Subring (∀ n : ℕ, ZMod (p ^ n)) where
  carrier := {a | ∀ m n (h : m ≤ n), ZMod.castHom (pow_dvd_pow p h) _ (a n) = a m}
  zero_mem' := fun m n h => (ZMod.castHom (pow_dvd_pow p h) _).map_zero
  one_mem' := fun m n h => (ZMod.castHom (pow_dvd_pow p h) _).map_one
  add_mem' := by
    intro a b ha hb m n h
    exact ((ZMod.castHom (pow_dvd_pow p h) _).map_add (a n) (b n)).trans
      (congrArg₂ (· + ·) (ha m n h) (hb m n h))
  mul_mem' := by
    intro a b ha hb m n h
    exact ((ZMod.castHom (pow_dvd_pow p h) _).map_mul (a n) (b n)).trans
      (congrArg₂ (· * ·) (ha m n h) (hb m n h))
  neg_mem' := by
    intro a ha m n h
    exact ((ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).map_neg (a n)).trans
      (congrArg (fun z : ZMod (p ^ m) => -z) (ha m n h))

/-- Compatibility of adjacent residues implies compatibility at all levels. -/
theorem compatibleResidues_of_adjacent (a : ∀ n : ℕ, ZMod (p ^ n))
    (ha : ∀ n, ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) _ (a (n + 1)) = a n) :
    a ∈ compatibleResidues p := by
  intro m n h
  induction n, h using Nat.le_induction with
  | base =>
    exact congrArg (fun f : ZMod (p ^ m) →+* ZMod (p ^ m) => f (a m))
      (Subsingleton.elim _ (RingHom.id _))
  | succ n h ih =>
    have hc : (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))).comp
        (ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) _) =
        ZMod.castHom (pow_dvd_pow p (h.trans (Nat.le_succ n))) _ :=
      Subsingleton.elim _ _
    exact (congrArg (fun f : ZMod (p ^ (n + 1)) →+* ZMod (p ^ m) =>
      f (a (n + 1))) hc).symm.trans
      ((congrArg (ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ m))) (ha n)).trans ih)

/-- Projection to an actual finite residue ring. -/
def residueProjection (n : ℕ) : compatibleResidues p →+* ZMod (p ^ n) where
  toFun a := a.val n
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem residueProjection_compatible (m n : ℕ) (h : m ≤ n) :
    (ZMod.castHom (pow_dvd_pow p h) _).comp (residueProjection p n) =
      residueProjection p m := by
  apply RingHom.ext
  intro a
  exact a.property m n h

variable [Fact p.Prime]

/-- Simultaneous reduction of a p-adic integer. -/
def residueFamily : ℤ_[p] →+* compatibleResidues p where
  toFun z := ⟨fun n => PadicInt.toZModPow n z, fun m n h =>
    congrArg (fun f : ℤ_[p] →+* ZMod (p ^ m) => f z)
      (PadicInt.zmod_cast_comp_toZModPow m n h)⟩
  map_one' := Subtype.ext (funext fun n => (PadicInt.toZModPow n).map_one)
  map_mul' x y := Subtype.ext (funext fun n => (PadicInt.toZModPow n).map_mul x y)
  map_zero' := Subtype.ext (funext fun n => (PadicInt.toZModPow n).map_zero)
  map_add' x y := Subtype.ext (funext fun n => (PadicInt.toZModPow n).map_add x y)

/-- The actual p-adic integer represented by a compatible residue family. -/
def residueLimit : compatibleResidues p →+* ℤ_[p] :=
  PadicInt.lift (residueProjection_compatible p)

/-- The constructed limit has exactly the prescribed residues. -/
theorem residueLimit_spec (a : compatibleResidues p) (n : ℕ) :
    PadicInt.toZModPow n (residueLimit p a) = a.val n :=
  congrArg (fun f : compatibleResidues p →+* ZMod (p ^ n) => f a)
    (PadicInt.lift_spec (residueProjection_compatible p) n)

/-- Reduction identifies the p-adic integer ring with compatible residues. -/
def residueFamilyRingEquiv : ℤ_[p] ≃+* compatibleResidues p where
  __ := residueFamily p
  invFun := residueLimit p
  left_inv z := PadicInt.ext_of_toZModPow.mp fun n => residueLimit_spec p (residueFamily p z) n
  right_inv a := Subtype.ext (funext fun n => residueLimit_spec p a n)

local instance residueTopology (n : ℕ) : TopologicalSpace (ZMod (p ^ n)) := ⊥
local instance residueDiscreteTopology (n : ℕ) : DiscreteTopology (ZMod (p ^ n)) := ⟨rfl⟩

open DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal

/-- Reduction to the inverse limit is continuous for its subspace product topology. -/
theorem continuous_residueFamily : Continuous (residueFamily p) := by
  apply Continuous.subtype_mk
  apply continuous_pi
  intro n
  exact continuous_padicIntToZModPow p n

/-- The metric p-adic topology agrees with the inverse-limit topology. -/
theorem residueFamily_isHomeomorph : IsHomeomorph (residueFamilyRingEquiv p) := by
  apply (isHomeomorph_iff_continuous_bijective).mpr
  exact ⟨continuous_residueFamily p, (residueFamilyRingEquiv p).bijective⟩

/-- A map to the p-adic integers is continuous exactly when every residue is continuous. -/
theorem continuous_iff_residues {Y : Type*} [TopologicalSpace Y] (f : Y → ℤ_[p]) :
    Continuous f ↔ ∀ n, Continuous (fun y => PadicInt.toZModPow n (f y)) := by
  constructor
  · intro hf n
    exact (continuous_padicIntToZModPow p n).comp hf
  · intro hf
    apply (residueFamily_isHomeomorph p).isEmbedding.continuous_iff.mpr
    exact (continuous_pi hf).subtype_mk _

end LocalFieldTheory.PadicResidues
