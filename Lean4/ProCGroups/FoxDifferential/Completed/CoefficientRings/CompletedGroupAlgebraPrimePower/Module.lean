import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Coeff.Projection

set_option autoImplicit false

/-!
# Fox differential: completed — coefficient rings — prime-power completed group algebra — module

The principal declarations in this module are:

- `primePowerCompletedCoeffToGroupAlgebra`
  The coefficient inverse limit maps canonically into the completed group algebra by taking the
  stagewise scalar units.
- `primePowerCompletedGroupAlgebraTransition_algebraMap`
  Finite-stage transitions send scalar coefficients through the reduced coefficient algebra map.
- `primePowerCompletedGroupAlgebraStageAugmentation_algebraMap`
  The finite-stage prime-power augmentation agrees with the scalar algebra map on coefficients.
- `primePowerCompletedGroupAlgebraProjection_coeffToGroupAlgebra`
  The prime-power completed group-algebra projection on coefficients is computed by the
  corresponding group-algebra coordinate map.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] instAddCommGroupPrimePowerCompletedGroupAlgebraStage
attribute [local instance] instAddCommGroupPrimePowerCompletedGroupAlgebraFamily
attribute [local instance] instAddCommGroupPrimePowerCompletedCoeffStage
attribute [local instance] instAddCommGroupPrimePowerCompletedCoeffFamily

omit [Fact (0 < ℓ)] in
/--
Finite-stage transitions send scalar coefficients through the reduced coefficient algebra map.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraTransition_algebraMap
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j)
    (a : ZMod (ℓ ^ j.1)) :
    primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (algebraMap (ZMod (ℓ ^ j.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G j) a) =
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1) a) := by
  rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
  classical
  rw [primePowerCompletedGroupAlgebraTransition_eq']
  simp only [modNCompletedGroupAlgebraTransition, modNCompletedGroupAlgebraStageCoeffMap,
  modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe, map_intCast]

omit [Fact (0 < ℓ)] in
/-- The finite-stage prime-power augmentation agrees with the scalar algebra map on coefficients. -/
@[simp]
theorem primePowerCompletedGroupAlgebraStageAugmentation_algebraMap
    (i : PrimePowerCompletedGroupAlgebraIndex G) (a : ZMod (ℓ ^ i.1)) :
    modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
        (algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i) a) = a := by
  rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
  classical
  simp only [modNCompletedGroupAlgebraStageAugmentation, map_intCast]

/--
The coefficient inverse limit maps canonically into the completed group algebra by taking the
stagewise scalar units.
-/
def primePowerCompletedCoeffToGroupAlgebra :
    PrimePowerCompletedCoeff ℓ G →+* PrimePowerCompletedGroupAlgebra ℓ G where
  toFun a := ⟨fun i =>
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (algebraMap (ZMod (ℓ ^ j.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G j)
          (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) j a)) =
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a)
    rw [primePowerCompletedGroupAlgebraTransition_algebraMap]
    exact congrArg
      (algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i))
      (a.2 i j hij)⟩
  map_one' := by
    apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
    intro i
    change algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (1 : PrimePowerCompletedCoeff ℓ G))
      = 1
    rw [primePowerCompletedCoeffProjection_one]
    exact map_one (algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i))
  map_mul' := by
    intro a b
    apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
    intro i
    change algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (a * b)) =
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) *
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b)
    rw [primePowerCompletedCoeffProjection_mul]
    exact
      map_mul
        (algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i))
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b)
  map_zero' := by
    apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
    intro i
    change algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (0 : PrimePowerCompletedCoeff ℓ G))
      = 0
    rw [primePowerCompletedCoeffProjection_zero]
    exact map_zero (algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i))
  map_add' := by
    intro a b
    apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
    intro i
    change algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (a + b)) =
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) +
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b)
    rw [primePowerCompletedCoeffProjection_add]
    exact
      map_add
        (algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i))
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b)

omit [Fact (0 < ℓ)] in
/--
The prime-power completed group-algebra projection on coefficients is computed by the
corresponding group-algebra coordinate map.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_coeffToGroupAlgebra
    (i : PrimePowerCompletedGroupAlgebraIndex G) (a : PrimePowerCompletedCoeff ℓ G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (primePowerCompletedCoeffToGroupAlgebra (ℓ := ℓ) (G := G) a) =
      algebraMap (ZMod (ℓ ^ i.1)) (PrimePowerCompletedGroupAlgebraStage ℓ G i)
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) := by
  rfl

omit [Fact (0 < ℓ)] in
/--
Finite-stage transitions commute with scalar multiplication after reducing the scalar
coefficient.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraTransition_smul
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j)
    (a : ZMod (ℓ ^ j.1))
    (x : PrimePowerCompletedGroupAlgebraStage ℓ G j) :
    primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij (a • x) =
      (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1) a) •
        primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij x := by
  rw [Algebra.smul_def, map_mul, primePowerCompletedGroupAlgebraTransition_algebraMap]
  rw [← Algebra.smul_def]

/--
The ambient family of prime-power group-algebra stages carries pointwise scalar multiplication,
using the projection of a completed coefficient at each index.
-/
instance instSMulPrimePowerCompletedCoeffPrimePowerCompletedGroupAlgebraFamily :
    SMul (PrimePowerCompletedCoeff ℓ G)
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) where
  smul a x := fun i =>
    (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i)

/--
The prime-power completed group-algebra family is a module over the prime-power completed
coefficient ring.
-/
instance instModulePrimePowerCompletedCoeffPrimePowerCompletedGroupAlgebraFamily :
    Module (PrimePowerCompletedCoeff ℓ G)
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) where
  one_smul x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (1 : PrimePowerCompletedCoeff ℓ G)) •
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i) =
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i)
    rw [primePowerCompletedCoeffProjection_one, one_smul]
  mul_smul a b x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (a * b)) •
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        ((primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b) •
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i))
    rw [primePowerCompletedCoeffProjection_mul, mul_smul]
  smul_zero a := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        (0 : PrimePowerCompletedGroupAlgebraStage ℓ G i) = 0
    rw [smul_zero]
  smul_add a x y := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        ((show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i) +
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y i)) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i) +
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y i)
    rw [smul_add]
  add_smul a b x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (a + b)) •
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i) +
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b) •
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i)
    rw [primePowerCompletedCoeffProjection_add, add_smul]
  zero_smul x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (0 : PrimePowerCompletedCoeff ℓ G)) •
          (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x i) = 0
    rw [primePowerCompletedCoeffProjection_zero, zero_smul]

/--
The completed group algebra carries coefficient-ring scalar multiplication by applying the
scalar action at every finite quotient stage.
-/
instance instSMulPrimePowerCompletedCoeffPrimePowerCompletedGroupAlgebra :
    SMul (PrimePowerCompletedCoeff ℓ G)
      (PrimePowerCompletedGroupAlgebra ℓ G) where
  smul a x := ⟨fun i =>
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i), by
    intro i j hij
    calc
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          ((primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) j a) •
            (show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j)) =
      (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)
          (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) j a)) •
        primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          (show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j) := by
            simpa using
              primePowerCompletedGroupAlgebraTransition_smul
                (ℓ := ℓ) (G := G) hij
                (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) j a)
                (show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j)
      _ =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) := by
            exact congrArg₂ HSMul.hSMul (a.2 i j hij) (x.2 i j hij)⟩

omit [Fact (0 < ℓ)] in
/-- The inclusion of the prime-power completed group algebra preserves scalar multiplication. -/
@[simp]
theorem coe_smul_primePowerCompletedGroupAlgebra
    (a : PrimePowerCompletedCoeff ℓ G)
    (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    letI := instSMulPrimePowerCompletedCoeffPrimePowerCompletedGroupAlgebra
      (ℓ := ℓ) (G := G)
    ((a • x : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) =
      a • (x :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  funext i
  change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) =
    (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
  rfl

omit [Fact (0 < ℓ)] in
/-- The finite-stage projection is compatible with scalar multiplication. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_smul
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (a : PrimePowerCompletedCoeff ℓ G)
    (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i (a • x) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x := by
  rfl

/--
The prime-power completed group algebra is a module over the prime-power completed coefficient
ring.
-/
instance instModulePrimePowerCompletedCoeffPrimePowerCompletedGroupAlgebra :
    Module (PrimePowerCompletedCoeff ℓ G)
      (PrimePowerCompletedGroupAlgebra ℓ G) :=
  Function.Injective.module (PrimePowerCompletedCoeff ℓ G)
    { toFun := Subtype.val
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    Subtype.val_injective
    (coe_smul_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))

omit [Fact (0 < ℓ)] in
/--
The prime-power completed augmentation is left inverse to the coefficient-to-group-algebra map.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentation_coeffToGroupAlgebra
    (i : PrimePowerCompletedGroupAlgebraIndex G) (a : PrimePowerCompletedCoeff ℓ G) :
    modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
        (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
          (primePowerCompletedCoeffToGroupAlgebra (ℓ := ℓ) (G := G) a)) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a := by
  rw [primePowerCompletedGroupAlgebraProjection_coeffToGroupAlgebra]
  exact primePowerCompletedGroupAlgebraStageAugmentation_algebraMap (ℓ := ℓ) (G := G) i
    (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a)

end

end FoxDifferential
