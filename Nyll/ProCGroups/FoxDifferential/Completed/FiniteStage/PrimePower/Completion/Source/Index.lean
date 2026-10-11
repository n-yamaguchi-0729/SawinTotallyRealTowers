/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Completed.FiniteStage.PrimePower.Completion.Target

/-!
# Fox differential: prime power — completion — source — index

The principal declarations in this module are:

- `foxCommutatorPowerOpenNormalSubgroup`
  The open normal subgroup associated to the finite Fox commutator-power quotient.
- `foxAlgebraicStagePrimePowerSourceCompletedIndex`
  The completed group-algebra index corresponding to the finite Fox commutator-power source quotient
  at the prime-power stage \(a\).
- `foxCommutatorPowerOpenNormalSubgroup_subgroup`
  The underlying subgroup of \(\mathrm{finiteFoxCommutatorPowerOpenNormalSubgroup}\) is the
  corresponding commutator-power subgroup.
- `foxAlgebraicStagePrimePowerSourceCompletedIndex_subgroup`
  The source completed index has the expected underlying commutator-power subgroup.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ)
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


/-- The open normal subgroup associated to the finite Fox commutator-power quotient. -/
def foxCommutatorPowerOpenNormalSubgroup
    [TopologicalSpace (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) (n : ℕ) :
    OpenNormalSubgroup (FreeGroup X) where
  toOpenSubgroup :=
    { toSubgroup := foxCommutatorPowerSubgroup (F := FreeGroup X) N n
      isOpen' := isOpen_discrete _ }
  isNormal' := by
    change (foxCommutatorPowerSubgroup (F := FreeGroup X) N n).Normal
    infer_instance

omit [DecidableEq X] in
/--
The underlying subgroup of \(\mathrm{finiteFoxCommutatorPowerOpenNormalSubgroup}\) is the
corresponding commutator-power subgroup.
-/
@[simp]
theorem foxCommutatorPowerOpenNormalSubgroup_subgroup
    [TopologicalSpace (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X)) (n : ℕ) :
    ((foxCommutatorPowerOpenNormalSubgroup (X := X) N n :
        OpenNormalSubgroup (FreeGroup X)) : Subgroup (FreeGroup X)) =
      foxCommutatorPowerSubgroup (F := FreeGroup X) N n := rfl

/--
The completed group-algebra index corresponding to the finite Fox commutator-power source
quotient at the prime-power stage \(a\).
-/
def foxAlgebraicStagePrimePowerSourceCompletedIndex
    [TopologicalSpace (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (a : ℕ) : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex (FreeGroup X) :=
  OrderDual.toDual
    (⟨foxCommutatorPowerOpenNormalSubgroup (X := X) N (ℓ ^ a),
      hfinite a⟩ :
      OpenNormalSubgroupInClass ProCGroups.FiniteGroupClass.allFinite (FreeGroup X))

omit [DecidableEq X] in
/-- The source completed index has the expected underlying commutator-power subgroup. -/
@[simp]
theorem foxAlgebraicStagePrimePowerSourceCompletedIndex_subgroup
    [TopologicalSpace (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    (a : ℕ) :
    (((OrderDual.ofDual
        (foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X)
          N hfinite a)).1 : OpenNormalSubgroup (FreeGroup X)) :
        Subgroup (FreeGroup X)) =
      foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a) := rfl

omit [DecidableEq X] in
/-- The source completed indices are monotone along prime-power stages. -/
theorem foxAlgebraicStagePrimePowerSourceCompletedIndex_mono
    [TopologicalSpace (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    (N : Subgroup (FreeGroup X))
    (hfinite : ∀ a : ℕ,
      Finite (FreeGroup X ⧸
        foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)))
    {a b : ℕ} (hab : a ≤ b) :
    foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite a ≤
      foxAlgebraicStagePrimePowerSourceCompletedIndex (ℓ := ℓ) (X := X) N hfinite b := by
  change foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ b) ≤
    foxCommutatorPowerSubgroup (F := FreeGroup X) N (ℓ ^ a)
  exact foxCommutatorPowerSubgroup_dvd (X := X) N
    (primePow_dvd_primePow (ℓ := ℓ) hab)



end

end FoxDifferential
