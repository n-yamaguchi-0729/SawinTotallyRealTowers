import ProCGroups.ProP.FrattiniPowers
import Mathlib.Algebra.Module.ZMod
import ProCGroups.Topologies.ContinuousMonoidHom

set_option autoImplicit false
/-!
# Continuous degree-one `ZMod p` classes

For the trivial action, continuous degree-one cohomology is represented by
continuous additive characters into the discrete group `ZMod p`.  This file
also proves that every such character kills the closed power--commutator
subgroup.  No general cohomology package is imported: that dependency is much
larger than the degree-one statement needed by the tower argument.
-/

open scoped Topology commutatorElement

namespace ClassFieldTower.ProP

universe u

variable {p : ℕ} {G : Type u}
variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

local instance : TopologicalSpace (ZMod p) := ⊥
local instance : DiscreteTopology (ZMod p) := discreteTopology_bot _

/-- Continuous degree-one classes for the trivial `ZMod p` action. -/
abbrev ContinuousH1ZMod :=
  ContinuousAddMonoidHom (Additive G) (ZMod p)

/-- The canonical `ZMod p`-module structure on continuous degree-one classes.

It is deliberately a named definition rather than a global data instance;
downstream files activate it once per section. -/
@[reducible] def continuousH1ZModModule :
    Module (ZMod p) (ContinuousH1ZMod (p := p) (G := G)) :=
  AddCommGroup.zmodModule fun f => by
    ext g
    simp

local instance : Module (ZMod p) (ContinuousH1ZMod (p := p) (G := G)) :=
  continuousH1ZModModule

/-- Reinterpret an additive degree-one class as a multiplicative character. -/
def characterOfH1 (f : ContinuousH1ZMod (p := p) (G := G)) :
    G →ₜ* Multiplicative (ZMod p) where
  toFun g := Multiplicative.ofAdd (f (Additive.ofMul g))
  map_one' := f.map_zero
  map_mul' g h := f.map_add (Additive.ofMul g) (Additive.ofMul h)
  continuous_toFun := f.continuous_toFun

/-- Reinterpret a multiplicative `ZMod p` character as an additive degree-one class. -/
def h1OfCharacter (f : G →ₜ* Multiplicative (ZMod p)) :
    ContinuousH1ZMod (p := p) (G := G) where
  toFun g := Multiplicative.toAdd (f (Additive.toMul g))
  map_zero' := f.map_one
  map_add' g h := f.map_mul (Additive.toMul g) (Additive.toMul h)
  continuous_toFun := f.continuous_toFun

/-- Additive degree-one classes and multiplicative characters are equivalent. -/
def h1CharacterEquiv :
    ContinuousH1ZMod (p := p) (G := G) ≃ (G →ₜ* Multiplicative (ZMod p)) where
  toFun := characterOfH1
  invFun := h1OfCharacter
  left_inv f := by ext g; rfl
  right_inv f := by ext g; rfl

/-- A continuous `ZMod p` character kills both `p`-th powers and commutators,
and hence their closed generated subgroup. -/
theorem closedPowerCommutator_le_character_ker
    (f : G →ₜ* Multiplicative (ZMod p)) :
    closedPowerCommutator p G ≤ f.toMonoidHom.ker := by
  apply Subgroup.topologicalClosure_minimal
  · apply sup_le
    · rw [powerSubgroup, Subgroup.closure_le]
      rintro _ ⟨g, rfl⟩
      change f (g ^ p) = 1
      rw [map_pow]
      change Multiplicative.ofAdd (p • Multiplicative.toAdd (f g)) = 1
      simp
    · rw [commutator_def, Subgroup.commutator_le]
      intro g _ h _
      change f ⁅g, h⁆ = 1
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  · exact ProCGroups.ContinuousMonoidHom.isClosed_ker f

end ClassFieldTower.ProP
