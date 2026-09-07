import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.AugmentationIdeal
import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Basic.StageCoeffMap.AllFinite

set_option autoImplicit false

/-!
# Fox differential: coefficient rings — prime-power completed group algebra — basic — augmentation

The principal declarations in this module are:

- `modNCompletedGroupAlgebraCoeffMap`
  The modulus-direction map on residue-coefficient completed group algebras.
- `modNCompletedGroupAlgebraAugmentationKernelCoeffMap`
  Coefficient change is performed stagewise: supports are unchanged and coefficients are transported
  by the given ring homomorphism.
- `modNCompletedGroupAlgebraProjection_coeffMap`
  The mod-\(n\) completed group-algebra projection commutes with the coefficient map.
- `modNCompletedGroupAlgebraStageAugmentation_comp_coeffMap`
  Finite-stage augmentation commutes with coefficient reduction.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u


variable {n m k : ℕ}
variable [Fact (0 < n)] [Fact (0 < m)] [Fact (0 < k)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The modulus-direction map on residue-coefficient completed group algebras. -/
def modNCompletedGroupAlgebraCoeffMap (hnm : n ∣ m) :
    ModNCompletedGroupAlgebra m G → ModNCompletedGroupAlgebra n G := by
  intro x
  refine ⟨fun U =>
      modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm (x.1 U), ?_⟩
  intro U V hUV
  calc
    modNCompletedGroupAlgebraTransition n G hUV
        (modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) V hnm (x.1 V))
      =
    modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm
      (modNCompletedGroupAlgebraTransition m G hUV (x.1 V)) := by
        symm
        exact congrFun
          (congrArg DFunLike.coe
            (modNCompletedGroupAlgebraStageCoeffMap_compatible
              (n := n) (m := m) (G := G) hUV hnm)) (x.1 V)
    _ =
      modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm (x.1 U) := by
        exact congrArg
          (modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm)
          (x.2 U V hUV)

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- The mod-\(n\) completed group-algebra projection commutes with the coefficient map. -/
@[simp]
theorem modNCompletedGroupAlgebraProjection_coeffMap
    (hnm : n ∣ m) (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G)
    (x : ModNCompletedGroupAlgebra m G) :
    modNCompletedGroupAlgebraProjection n G U
        (modNCompletedGroupAlgebraCoeffMap (n := n) (m := m) (G := G) hnm x) =
      modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm
        (modNCompletedGroupAlgebraProjection m G U x) := by
  unfold modNCompletedGroupAlgebraProjection modNCompletedGroupAlgebraCoeffMap
  rfl

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- Finite-stage augmentation commutes with coefficient reduction. -/
@[simp 900]
theorem modNCompletedGroupAlgebraStageAugmentation_comp_coeffMap
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) (hnm : n ∣ m) :
    (modNCompletedGroupAlgebraStageAugmentation n G U).comp
        (modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm) =
      (modNCompletedCoeffMap (n := n) (m := m) hnm).comp
        (modNCompletedGroupAlgebraStageAugmentation m G U) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
          (modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm)) x =
        ((modNCompletedCoeffMap (n := n) (m := m) hnm).comp
          (modNCompletedGroupAlgebraStageAugmentation m G U)) x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, RingHom.comp_apply, modNCompletedGroupAlgebraStageCoeffMap_of,
      modNCompletedGroupAlgebraStageAugmentation_of,
      modNCompletedGroupAlgebraStageAugmentation_of]
    simpa [modNCompletedCoeffMap] using
      (map_one (modNCompletedCoeffMap (n := n) (m := m) hnm)).symm
  · intro x y hx hy
    simp only [RingHom.map_add, hx, RingHom.coe_comp, Function.comp_apply, hy]
  · intro a x hx
    let : Algebra (ModNCompletedCoeff m) (ModNCompletedCoeff n) :=
      ZMod.algebra' (R := ModNCompletedCoeff n) (m := n) (n := m) hnm
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    have hcoeff :
        ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
            (modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm))
            (algebraMap (ModNCompletedCoeff m) (ModNCompletedGroupAlgebraStage m G U) a) =
          ((modNCompletedCoeffMap (n := n) (m := m) hnm).comp
            (modNCompletedGroupAlgebraStageAugmentation m G U))
            (algebraMap (ModNCompletedCoeff m) (ModNCompletedGroupAlgebraStage m G U) a) := by
      have hleft :
          ((modNCompletedGroupAlgebraStageAugmentation n G U).comp
              (modNCompletedGroupAlgebraStageCoeffMap (n := n) (m := m) (G := G) U hnm))
              (algebraMap (ModNCompletedCoeff m) (ModNCompletedGroupAlgebraStage m G U) a) =
            algebraMap (ModNCompletedCoeff m) (ModNCompletedCoeff n) a := by
        simp only [modNCompletedGroupAlgebraStageAugmentation,
            modNCompletedGroupAlgebraStageCoeffMap,
  modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe, MonoidAlgebra.coe_algebraMap,
      Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, RingHom.comp_apply, RingHom.coe_coe,
      MonoidAlgebra.lift_single,
  MonoidAlgebra.of_apply, Algebra.smul_def, MonoidAlgebra.single_mul_single, mul_one,
  MonoidHom.one_apply]
      have hright :
          ((modNCompletedCoeffMap (n := n) (m := m) hnm).comp
              (modNCompletedGroupAlgebraStageAugmentation m G U))
              (algebraMap (ModNCompletedCoeff m) (ModNCompletedGroupAlgebraStage m G U) a) =
            algebraMap (ModNCompletedCoeff m) (ModNCompletedCoeff n) a := by
        simp only [modNCompletedGroupAlgebraStageAugmentation, MonoidAlgebra.coe_algebraMap,
            Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, RingHom.comp_apply, RingHom.coe_coe,
      MonoidAlgebra.lift_single,
  MonoidHom.one_apply, smul_eq_mul, mul_one]
        rfl
      exact hleft.trans hright.symm
    rw [hcoeff]

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- Class-indexed finite-stage augmentation commutes with coefficient reduction. -/
@[simp 900]
theorem modNCompletedGroupAlgebraStageAugmentationInClass_comp_coeffMap
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) (hnm : n ∣
        m) :
    (modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
        (modNCompletedGroupAlgebraStageCoeffMapInClass
          (n := n) (m := m) (G := G) C U hnm) =
      (modNCompletedCoeffMap (n := n) (m := m) hnm).comp
        (modNCompletedGroupAlgebraStageAugmentationInClass m G C U) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
          (modNCompletedGroupAlgebraStageCoeffMapInClass
            (n := n) (m := m) (G := G) C U hnm)) x =
        ((modNCompletedCoeffMap (n := n) (m := m) hnm).comp
          (modNCompletedGroupAlgebraStageAugmentationInClass m G C U)) x)
    x ?_ ?_ ?_
  · intro q
    rw [RingHom.comp_apply, RingHom.comp_apply, modNCompletedGroupAlgebraStageCoeffMapInClass_of,
      modNCompletedGroupAlgebraStageAugmentationInClass_of,
      modNCompletedGroupAlgebraStageAugmentationInClass_of]
    simpa [modNCompletedCoeffMap] using
      (map_one (modNCompletedCoeffMap (n := n) (m := m) hnm)).symm
  · intro x y hx hy
    simp only [RingHom.map_add, hx, RingHom.coe_comp, Function.comp_apply, hy]
  · intro a x hx
    let : Algebra (ModNCompletedCoeff m) (ModNCompletedCoeff n) :=
      ZMod.algebra' (R := ModNCompletedCoeff n) (m := n) (n := m) hnm
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    have hcoeff :
        ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
            (modNCompletedGroupAlgebraStageCoeffMapInClass
              (n := n) (m := m) (G := G) C U hnm))
            (algebraMap (ModNCompletedCoeff m)
              (ModNCompletedGroupAlgebraStageInClass m G C U) a) =
          ((modNCompletedCoeffMap (n := n) (m := m) hnm).comp
            (modNCompletedGroupAlgebraStageAugmentationInClass m G C U))
            (algebraMap (ModNCompletedCoeff m)
              (ModNCompletedGroupAlgebraStageInClass m G C U) a) := by
      have hleft :
          ((modNCompletedGroupAlgebraStageAugmentationInClass n G C U).comp
              (modNCompletedGroupAlgebraStageCoeffMapInClass
                (n := n) (m := m) (G := G) C U hnm))
              (algebraMap (ModNCompletedCoeff m)
                (ModNCompletedGroupAlgebraStageInClass m G C U) a) =
            algebraMap (ModNCompletedCoeff m) (ModNCompletedCoeff n) a := by
        simp only [modNCompletedGroupAlgebraStageAugmentationInClass,
            modNCompletedGroupAlgebraStageCoeffMapInClass,
  modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe, MonoidAlgebra.coe_algebraMap,
      Algebra.algebraMap_self,
  RingHom.coe_id, Function.comp_apply, id_eq, RingHom.comp_apply, RingHom.coe_coe,
      MonoidAlgebra.lift_single,
  MonoidAlgebra.of_apply, Algebra.smul_def, MonoidAlgebra.single_mul_single, mul_one,
  MonoidHom.one_apply]
      have hright :
          ((modNCompletedCoeffMap (n := n) (m := m) hnm).comp
              (modNCompletedGroupAlgebraStageAugmentationInClass m G C U))
              (algebraMap (ModNCompletedCoeff m)
                (ModNCompletedGroupAlgebraStageInClass m G C U) a) =
            algebraMap (ModNCompletedCoeff m) (ModNCompletedCoeff n) a := by
        simp only [modNCompletedGroupAlgebraStageAugmentationInClass, MonoidAlgebra.coe_algebraMap,
  Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq, RingHom.comp_apply,
      RingHom.coe_coe,
  MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]
        rfl
      exact hleft.trans hright.symm
    rw [hcoeff]

omit [Fact (0 < n)] [Fact (0 < m)] in
/-- Completed augmentation commutes with the coefficient-reduction map between moduli. -/
@[simp]
theorem modNCompletedGroupAlgebraAugmentation_coeffMap
    (hnm : n ∣ m) (x : ModNCompletedGroupAlgebra m G) :
    modNCompletedGroupAlgebraAugmentation n G
        (modNCompletedGroupAlgebraCoeffMap (n := n) (m := m) (G := G) hnm x) =
      modNCompletedCoeffMap (n := n) (m := m) hnm
        (modNCompletedGroupAlgebraAugmentation m G x) := by
  unfold modNCompletedGroupAlgebraAugmentation modNCompletedGroupAlgebraAugmentationAt
  rw [modNCompletedGroupAlgebraProjection_coeffMap]
  exact congrFun
    (congrArg DFunLike.coe
      (modNCompletedGroupAlgebraStageAugmentation_comp_coeffMap
        (n := n) (m := m) (G := G)
            (_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G) hnm))
    (modNCompletedGroupAlgebraProjection m G
        (_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G) x)

/--
Coefficient change is performed stagewise: supports are unchanged and coefficients are
transported by the given ring homomorphism.
-/
def modNCompletedGroupAlgebraAugmentationKernelCoeffMap
    (hnm : n ∣ m) :
    ModNCompletedGroupAlgebraAugmentationKernel m G →
      ModNCompletedGroupAlgebraAugmentationKernel n G := by
  intro x
  refine ⟨modNCompletedGroupAlgebraCoeffMap (n := n) (m := m) (G := G) hnm x.1, ?_⟩
  rw [mem_modNCompletedGroupAlgebraAugmentationKernel_iff,
    modNCompletedGroupAlgebraAugmentation_coeffMap]
  simpa [map_zero, modNCompletedCoeffMap] using
    congrArg (modNCompletedCoeffMap (n := n) (m := m) hnm) x.2

/-- The standard divisibility relation between prime powers with the same base. -/
theorem primePow_dvd_primePow
    (ℓ : ℕ) {a b : ℕ} (hab : a ≤ b) :
    ℓ ^ a ∣ ℓ ^ b := by
  exact Nat.pow_dvd_pow ℓ hab

/-- The modulus-direction completed map specialized to prime-power stages. -/
def primePowCompletedGroupAlgebraCoeffMap
    (ℓ : ℕ) {a b : ℕ}
    (hab : a ≤ b) :
    ModNCompletedGroupAlgebra (ℓ ^ b) G → ModNCompletedGroupAlgebra (ℓ ^ a) G :=
  modNCompletedGroupAlgebraCoeffMap (n := ℓ ^ a) (m := ℓ ^ b) (G := G)
    (primePow_dvd_primePow (ℓ := ℓ) hab)

/-- The coefficient map between prime-power stages restricts to a map on augmentation kernels. -/
def primePowCompletedGroupAlgebraAugmentationKernelCoeffMap
    (ℓ : ℕ) {a b : ℕ}
    (hab : a ≤ b) :
    ModNCompletedGroupAlgebraAugmentationKernel (ℓ ^ b) G →
      ModNCompletedGroupAlgebraAugmentationKernel (ℓ ^ a) G :=
  modNCompletedGroupAlgebraAugmentationKernelCoeffMap
    (n := ℓ ^ a) (m := ℓ ^ b) (G := G)
    (primePow_dvd_primePow (ℓ := ℓ) hab)


variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The two-parameter index \((a,U)\) for the prime-power residue-coefficient stages. -/
abbrev PrimePowerCompletedGroupAlgebraIndex :=
  ℕ × _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G

/-- The two-parameter index \((a,U)\) for prime-power stages over a quotient class \(C\). -/
abbrev PrimePowerCompletedGroupAlgebraIndexInClass (C : ProCGroups.FiniteGroupClass.{u}) :=
  ℕ × CompletedGroupAlgebraIndexInClass G C
end

end FoxDifferential
