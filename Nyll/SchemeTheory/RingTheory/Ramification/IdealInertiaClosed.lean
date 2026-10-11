/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.RingTheory.Ideal.Defs
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Order

/-!
# Closed ideal inertia from open coefficient stabilizers

The original ring action supplies the subgroup. Its coefficient stabilizers
give a continuous action on the discrete ring, and inertia is the intersection
of the closed coefficient-difference conditions.
-/

namespace SchemeTheory

universe u v

/-- Open coefficient stabilizers make the actual ideal inertia closed in
the given group topology. No compactness or closedness premise is added. -/
theorem idealInertia_isClosed_of_openFixedSets
    (B : CommRingCat.{u}) (G : GrpCat.{v}) [TopologicalSpace G.carrier]
    [IsTopologicalGroup G.carrier] (a : MulSemiringAction G.carrier B.carrier)
    (Q : Ideal B.carrier)
    (hopen :
      let : MulSemiringAction G.carrier B.carrier := a
      ∀ b : B.carrier, IsOpen (fun g : G.carrier => g • b = b)) :
    let : MulSemiringAction G.carrier B.carrier := a
    IsClosed (Q.inertia G.carrier).carrier := by
  intro ringAction
  let : TopologicalSpace B.carrier := ⊥
  have : DiscreteTopology B.carrier := ⟨rfl⟩
  have : ContinuousSMul G.carrier B.carrier :=
    continuousSMul_iff_stabilizer_isOpen.mpr hopen
  have hset : (Q.inertia G.carrier).carrier =
      ⋂ b : B.carrier, {g : G.carrier | g • b - b ∈ Q} := by
    ext g
    rw [Set.mem_iInter]
    exact Ideal.mem_inertia (I := Q) (G := G.carrier) (σ := g)
  rw [hset]
  apply isClosed_iInter
  intro b
  have hcont : Continuous (fun g : G.carrier => g • b) :=
    continuous_id.smul continuous_const
  exact (isClosed_discrete {c : B.carrier | c - b ∈ Q}).preimage hcont

end SchemeTheory
