import ProCGroups.FoxDifferential.Completed.CoefficientRings.AugmentationIdealPrimePower.Additive

set_option autoImplicit false

/-!
# Fox differential: completed — coefficient rings — prime-power augmentation ideal — module

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraStageAugmentationIdealTransition_smul`
  The transition map between finite-stage augmentation ideals is compatible with scalar
  multiplication.
- `coe_smul_primePowerCompletedGroupAlgebraAugmentationIdeal`
  The inclusion of the completed augmentation ideal preserves scalar multiplication.
- `instSMulPrimePowerCompletedCoeffPrimePowerCompletedGAAugmentationIdealFamily`
  The family-level prime-power completed group-algebra augmentation ideal carries scalar
  multiplication by the prime-power completed coefficient ring.
- `instModulePpCoeffPpGAAugIdealFamily`
  The prime-power completed augmentation-ideal family is a module over the completed coefficient
  ring.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems

universe u


variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] instAddCommGroupPrimePowerCompletedCoeffStage
attribute [local instance] instAddCommGroupPrimePowerCompletedCoeffFamily

@[reducible] private def addCommGroupAugmentationIdealStage
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    AddCommGroup ((primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) := by
  dsimp [primePowerCompletedGroupAlgebraAugmentationIdealSystem]
  infer_instance

attribute [local instance] addCommGroupAugmentationIdealStage

@[reducible] private def addCommGroupAugmentationIdealFamily :
    AddCommGroup
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) :=
  inferInstance

attribute [local instance] addCommGroupAugmentationIdealFamily

omit [Fact (0 < ℓ)] in
/--
The transition map between finite-stage augmentation ideals is compatible with scalar
multiplication.
-/
@[simp 900]
theorem primePowerCompletedGroupAlgebraStageAugmentationIdealTransition_smul
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j)
    (a : ZMod (ℓ ^ j.1))
    (x : primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j) :
    primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
        (ℓ := ℓ) (G := G) hij (a • x) =
      (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1) a) •
        primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
          (ℓ := ℓ) (G := G) hij x := by
  apply Subtype.ext
  change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
      ((a • x : primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j) :
        PrimePowerCompletedGroupAlgebraStage ℓ G j) =
    (((modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1) a) •
      primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
        (ℓ := ℓ) (G := G) hij x :
          primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i) :
        PrimePowerCompletedGroupAlgebraStage ℓ G i)
  simpa using
    primePowerCompletedGroupAlgebraTransition_smul
      (ℓ := ℓ) (G := G) hij a
      ((x : primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j) :
        PrimePowerCompletedGroupAlgebraStage ℓ G j)

/--
The family-level prime-power completed group-algebra augmentation ideal carries scalar
multiplication by the prime-power completed coefficient ring.
-/
instance instSMulPrimePowerCompletedCoeffPrimePowerCompletedGAAugmentationIdealFamily :
    SMul (PrimePowerCompletedCoeff ℓ G)
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) where
  smul a x := fun i =>
    (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
      (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i from x i)

/--
The prime-power completed augmentation-ideal family is a module over the completed coefficient
ring.
-/
instance instModulePpCoeffPpGAAugIdealFamily :
    Module (PrimePowerCompletedCoeff ℓ G)
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) where
  one_smul x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (1 : PrimePowerCompletedCoeff ℓ G)) •
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i from x i) =
      (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
        (ℓ := ℓ) (G := G) i from x i)
    rw [primePowerCompletedCoeffProjection_one, one_smul]
  mul_smul a b x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (a * b)) •
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i from x i) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        ((primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b) •
          (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
            (ℓ := ℓ) (G := G) i from x i))
    rw [primePowerCompletedCoeffProjection_mul, mul_smul]
  smul_zero a := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        (0 : primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i) = 0
    rw [smul_zero]
  smul_add a x y := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        ((show primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i from x i) +
          (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
            (ℓ := ℓ) (G := G) i from y i)) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
          (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
            (ℓ := ℓ) (G := G) i from x i) +
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
          (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
            (ℓ := ℓ) (G := G) i from y i)
    rw [smul_add]
  add_smul a b x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (a + b)) •
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i from x i) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
          (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
            (ℓ := ℓ) (G := G) i from x i) +
        (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i b) •
          (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
            (ℓ := ℓ) (G := G) i from x i)
    rw [primePowerCompletedCoeffProjection_add, add_smul]
  zero_smul x := by
    funext i
    change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (0 : PrimePowerCompletedCoeff ℓ G)) •
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i from x i) = 0
    rw [primePowerCompletedCoeffProjection_zero, zero_smul]

/--
The prime-power completed group-algebra augmentation ideal carries scalar multiplication by the
prime-power completed coefficient ring.
-/
instance instSMulPrimePowerCompletedCoeffPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    SMul (PrimePowerCompletedCoeff ℓ G)
      (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  smul a x := ⟨fun i =>
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i from x.1 i), by
    intro i j hij
    calc
      primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
          (ℓ := ℓ) (G := G) hij
          ((primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) j a) •
            (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
              from x.1 j)) =
      (modNCompletedCoeffMap
          (n := ℓ ^ i.1) (m := ℓ ^ j.1)
          (primePow_dvd_primePow (ℓ := ℓ) hij.1)
          (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) j a)) •
        primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
          (ℓ := ℓ) (G := G) hij
          (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from x.1 j) := by
            exact
              primePowerCompletedGroupAlgebraStageAugmentationIdealTransition_smul
                (ℓ := ℓ) (G := G) hij
                (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) j a)
                (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
                  (ℓ := ℓ) (G := G) j from x.1 j)
      _ =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal
          (ℓ := ℓ) (G := G) i from x.1 i) := by
            exact congrArg₂ HSMul.hSMul (a.2 i j hij) (x.2 i j hij)⟩

omit [Fact (0 < ℓ)] in
/-- The inclusion of the completed augmentation ideal preserves scalar multiplication. -/
@[simp]
theorem coe_smul_primePowerCompletedGroupAlgebraAugmentationIdeal
    (a : PrimePowerCompletedCoeff ℓ G)
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    letI := instSMulPrimePowerCompletedCoeffPrimePowerCompletedGroupAlgebraAugmentationIdeal
      (ℓ := ℓ) (G := G)
    ((a • x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) =
      a • (x :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) := by
  funext i
  change (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
      (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i from x.1 i) =
    (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
      (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i from x.1 i)
  rfl

/-- The prime-power completed augmentation ideal is a module over the completed coefficient ring. -/
instance instModulePpCoeffPpGAAugIdeal :
    Module (PrimePowerCompletedCoeff ℓ G)
      (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :=
  Function.Injective.module (PrimePowerCompletedCoeff ℓ G)
    { toFun := Subtype.val
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
    Subtype.val_injective
    (coe_smul_primePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G))


end

end FoxDifferential
