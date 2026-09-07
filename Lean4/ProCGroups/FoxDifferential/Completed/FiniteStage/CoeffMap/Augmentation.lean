import ProCGroups.FoxDifferential.Completed.FiniteStage.CoeffMap.Source

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — coeff map — augmentation

The principal declarations in this module are:

- `foxCommutatorPowerSourceGAAugmentation_powerSourceGAMap`
  Source augmentation commutes with finite-stage coefficient/source reduction.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)


variable {n₀ m₀ : ℕ} [Fact (0 < n₀)] [Fact (0 < m₀)]
omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Source augmentation commutes with finite-stage coefficient/source reduction. -/
theorem foxCommutatorPowerSourceGAAugmentation_powerSourceGAMap
    (N : Subgroup (FreeGroup X)) (hnm : n₀ ∣ m₀)
    (x : foxAlgebraicStageSourceGroupAlgebra (X := X) N m₀) :
    foxCommutatorPowerSourceGroupAlgebraAugmentation
        (F := FreeGroup X) N n₀
        (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm x) =
      modNCompletedCoeffMap (n := n₀) (m := m₀) hnm
        (foxCommutatorPowerSourceGroupAlgebraAugmentation
          (F := FreeGroup X) N m₀ x) := by
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      foxCommutatorPowerSourceGroupAlgebraAugmentation
          (F := FreeGroup X) N n₀
          (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm x) =
        modNCompletedCoeffMap (n := n₀) (m := m₀) hnm
          (foxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N m₀ x))
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) q with ⟨w, rfl⟩
    rw [foxAlgebraicStagePowerSourceGroupAlgebraMap_of,
      foxCommutatorPowerSourceGroupAlgebraAugmentation_of_quotient,
      foxCommutatorPowerSourceGroupAlgebraAugmentation_of_quotient]
    exact (map_one (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm)).symm
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def]
    change
      ((foxCommutatorPowerSourceGroupAlgebraAugmentation
          (F := FreeGroup X) N n₀).toRingHom.comp
          (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm))
          (algebraMap (ModNCompletedCoeff m₀)
              (foxAlgebraicStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀) * x) =
        ((modNCompletedCoeffMap (n := n₀) (m := m₀) hnm).comp
          (foxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N m₀).toRingHom)
          (algebraMap (ModNCompletedCoeff m₀)
              (foxAlgebraicStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀) * x)
    rw [RingHom.map_mul, RingHom.map_mul]
    have hx' :
        ((foxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n₀).toRingHom.comp
          (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm)) x =
          ((modNCompletedCoeffMap (n := n₀) (m := m₀) hnm).comp
            (foxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N m₀).toRingHom) x := by
      simpa [RingHom.comp_apply] using hx
    rw [hx']
    have hcoeff :
        ((foxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n₀).toRingHom.comp
          (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm))
            (algebraMap (ModNCompletedCoeff m₀)
              (foxAlgebraicStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀)) =
          ((modNCompletedCoeffMap (n := n₀) (m := m₀) hnm).comp
            (foxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N m₀).toRingHom)
            (algebraMap (ModNCompletedCoeff m₀)
              (foxAlgebraicStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀)) := by
      simp only [foxCommutatorPowerSourceGroupAlgebraAugmentation, AlgHom.toRingHom_eq_coe,
  foxAlgebraicStagePowerSourceGroupAlgebraMap, foxAlgebraicStageSameSourceGroupAlgebraCoeffMap,
  modNCompletedGroupRingCoeffMap, MonoidAlgebra.mapDomainRingHom,
      foxAlgebraicStagePowerSourceQuotientMap, map_intCast,
  modNCompletedCoeffMap]
    rw [hcoeff]




end

end FoxDifferential
