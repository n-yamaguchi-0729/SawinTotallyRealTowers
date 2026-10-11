/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProP.ContinuousH1
import Nyll.ProCGroups.ProP.FrattiniQuotient
import Nyll.ProCGroups.Topologies.QuotientMaps

/-!
# Factoring continuous degree-one classes through the elementary quotient

Every continuous `ZMod p` character factors uniquely through the closed
power--commutator quotient.  The resulting equivalence is linear and is kept
separate from the later finite-dimensional duality argument.
-/

open scoped Topology

namespace ClassFieldTower.ProP

universe u

variable {p : ℕ} {G : Type u}
variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

local instance : TopologicalSpace (ZMod p) := ⊥
local instance : DiscreteTopology (ZMod p) := discreteTopology_bot _
local instance : Module (ZMod p) (ContinuousH1ZMod (p := p) (G := G)) :=
  continuousH1ZModModule
local instance : (closedPowerCommutator p G).Normal :=
  closedPowerCommutator_normal p G

/-- Factor a character through the closed power--commutator quotient. -/
def characterOnPowerCommutatorQuotient
    (f : G →ₜ* Multiplicative (ZMod p)) :
    powerCommutatorQuotient p G →ₜ* Multiplicative (ZMod p) :=
  ProCGroups.QuotientGroup.liftₜ (closedPowerCommutator p G) f
    (closedPowerCommutator_le_character_ker f)

@[simp] theorem characterOnPowerCommutatorQuotient_mk
    (f : G →ₜ* Multiplicative (ZMod p)) (g : G) :
    characterOnPowerCommutatorQuotient f (powerCommutatorQuotientMk p G g) = f g := by
  rfl

/-- Pull a quotient character back along the quotient map. -/
def characterFromPowerCommutatorQuotient
    (f : powerCommutatorQuotient p G →ₜ* Multiplicative (ZMod p)) :
    G →ₜ* Multiplicative (ZMod p) :=
  f.comp (powerCommutatorQuotientMk p G)

/-- Factor a degree-one class through the closed power--commutator quotient. -/
def h1OnPowerCommutatorQuotient
    (f : ContinuousH1ZMod (p := p) (G := G)) :
    ContinuousH1ZMod (p := p) (G := powerCommutatorQuotient p G) :=
  h1OfCharacter
    (characterOnPowerCommutatorQuotient (characterOfH1 f))

/-- Pull a quotient degree-one class back to the original group. -/
def h1FromPowerCommutatorQuotient
    (f : ContinuousH1ZMod (p := p) (G := powerCommutatorQuotient p G)) :
    ContinuousH1ZMod (p := p) (G := G) :=
  h1OfCharacter
    (characterFromPowerCommutatorQuotient (characterOfH1 f))

/-- Continuous degree-one classes are unchanged after passing to the closed
power--commutator quotient. -/
def h1PowerCommutatorQuotientLinearEquiv :
    ContinuousH1ZMod (p := p) (G := G) ≃ₗ[ZMod p]
      ContinuousH1ZMod (p := p) (G := powerCommutatorQuotient p G) where
  toFun := h1OnPowerCommutatorQuotient
  invFun := h1FromPowerCommutatorQuotient
  left_inv f := by ext g; rfl
  right_inv f := by
    ext q
    obtain ⟨g, rfl⟩ := powerCommutatorQuotientMk_surjective p G q
    rfl
  map_add' f g := by
    ext q
    obtain ⟨x, rfl⟩ := powerCommutatorQuotientMk_surjective p G q
    rfl
  map_smul' c f := by
    ext q
    obtain ⟨x, rfl⟩ := powerCommutatorQuotientMk_surjective p G q
    let evG : ContinuousH1ZMod (p := p) (G := G) →+ ZMod p :=
      { toFun := fun h => h (Additive.ofMul x)
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    let evQ :
        ContinuousH1ZMod (p := p) (G := powerCommutatorQuotient p G) →+ ZMod p :=
      { toFun := fun h => h (Additive.ofMul (powerCommutatorQuotientMk p G x))
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    exact (ZMod.map_smul evG c f).trans
      (ZMod.map_smul evQ c (h1OnPowerCommutatorQuotient f)).symm

/-- The multiplicative form of the same quotient universal property. -/
def characterPowerCommutatorQuotientEquiv :
    (G →ₜ* Multiplicative (ZMod p)) ≃
      (powerCommutatorQuotient p G →ₜ* Multiplicative (ZMod p)) where
  toFun := characterOnPowerCommutatorQuotient
  invFun := characterFromPowerCommutatorQuotient
  left_inv f := by
    ext g
    exact characterOnPowerCommutatorQuotient_mk f g
  right_inv f := by
    ext q
    obtain ⟨g, rfl⟩ := powerCommutatorQuotientMk_surjective p G q
    rfl

end ClassFieldTower.ProP
