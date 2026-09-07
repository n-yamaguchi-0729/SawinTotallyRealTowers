import ProCGroups.ProP.FiniteFrattini
import ProCGroups.ProP.Zassenhaus.FiniteAugmentationSquare
import Mathlib.LinearAlgebra.Dual.Lemmas

set_option autoImplicit false
/-!
# Degree-one augmentation criterion for finite `p`-groups

Linear functionals on the elementary power--commutator quotient separate a
nonzero class.  Combined with dual-number linearization, this proves that
`[q]-1 ∈ I²` forces `q` into the closed power--commutator subgroup.  In a
finite `p`-group, P03 identifies that subgroup with Frattini.
-/

open scoped IsMulCommutative

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra

noncomputable section

universe u

variable (p : ℕ) [Fact p.Prime]
variable (Q : Type u) [Group Q]

section Separation

variable [TopologicalSpace Q] [IsTopologicalGroup Q]

local instance finiteDegreeOneClosedPowerCommutatorNormal :
    (closedPowerCommutator p Q).Normal :=
  closedPowerCommutator_normal p Q

local instance finiteDegreeOnePowerCommutatorComm :
    IsMulCommutative (powerCommutatorQuotient p Q) :=
  powerCommutatorQuotient_isMulCommutative p Q

local instance finiteDegreeOnePowerCommutatorModule :
    Module (ZMod p) (Additive (powerCommutatorQuotient p Q)) :=
  AddCommGroup.zmodModule fun x => by
    change (Additive.toMul x) ^ p = 1
    exact powerCommutatorQuotient_pow_eq_one p Q (Additive.toMul x)

/-- Membership of a standard augmentation generator in `I²` forces the group
element into the closed power--commutator subgroup. -/
theorem mem_closedPowerCommutator_of_generator_mem_augmentationIdeal_sq
    (q : Q)
    (hq : groupAlgebraAugmentationGenerator (ZMod p) Q q ∈
      (groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2) :
    q ∈ closedPowerCommutator p Q := by
  by_contra hqcore
  have hx : Additive.ofMul (powerCommutatorQuotientMk p Q q) ≠ 0 := by
    intro hx0
    apply hqcore
    apply (QuotientGroup.eq_one_iff (N := closedPowerCommutator p Q) q).mp
    change powerCommutatorQuotientMk p Q q = 1
    exact hx0
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one (ZMod p) hx
  let πadd : Additive Q →+ Additive (powerCommutatorQuotient p Q) :=
    (powerCommutatorQuotientMk p Q).toMonoidHom.toAdditive
  let χ : Additive Q →+ ZMod p := f.toAddMonoidHom.comp πadd
  have hzero : χ (Additive.ofMul q) = 0 :=
    character_eq_zero_of_generator_mem_augmentationIdeal_sq p Q χ q hq
  have hone : χ (Additive.ofMul q) = 1 := by
    change f (Additive.ofMul (powerCommutatorQuotientMk p Q q)) = 1
    exact hf
  rw [hone] at hzero
  exact one_ne_zero hzero

end Separation

section FiniteComparison

variable [TopologicalSpace Q] [IsTopologicalGroup Q] [T1Space Q] [Finite Q]

/-- In a finite T₁ group, every element of the closed power--commutator
subgroup has its standard augmentation generator in `I²`. -/
theorem closedPowerCommutator_le_augmentationSquareSubgroup :
    closedPowerCommutator p Q ≤ augmentationSquareSubgroup p Q := by
  rw [closedPowerCommutator]
  apply Subgroup.topologicalClosure_minimal
  · exact sup_le (powerSubgroup_le_augmentationSquareSubgroup p Q)
      (commutator_le_augmentationSquareSubgroup p Q)
  · exact (augmentationSquareSubgroup p Q : Set Q).toFinite.isClosed

/-- The degree-one augmentation criterion for a finite T₁ `p`-group. -/
theorem groupAlgebraAugmentationGenerator_mem_sq_iff_mem_frattini
    (hQ : IsPGroup p Q) (q : Q) :
    groupAlgebraAugmentationGenerator (ZMod p) Q q ∈
        (groupAlgebraAugmentationIdeal (ZMod p) Q) ^ 2 ↔
      q ∈ frattini Q := by
  constructor
  · intro hq
    have hcore := mem_closedPowerCommutator_of_generator_mem_augmentationIdeal_sq p Q q hq
    rwa [← frattini_eq_closedPowerCommutator_of_isPGroup hQ] at hcore
  · intro hq
    rw [frattini_eq_closedPowerCommutator_of_isPGroup hQ] at hq
    exact closedPowerCommutator_le_augmentationSquareSubgroup p Q hq

end FiniteComparison

end


end ClassFieldTower.ProP
