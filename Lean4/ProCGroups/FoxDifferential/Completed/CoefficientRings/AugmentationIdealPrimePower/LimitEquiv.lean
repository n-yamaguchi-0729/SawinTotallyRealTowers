import ProCGroups.FoxDifferential.Completed.CoefficientRings.AugmentationIdealPrimePower.Module

set_option autoImplicit false

/-!
# Fox differential: completed — coefficient rings — prime-power augmentation ideal — limit equiv

The principal declarations in this module are:

- `toPrimePowerCompletedGroupAlgebraAugmentationIdeal`
  A prime-power augmentation-kernel point determines a compatible family in the finite-stage
  augmentation ideals.
- `ofPrimePowerCompletedGroupAlgebraAugmentationIdeal`
  A compatible family of prime-power finite-stage augmentation-ideal elements determines a
  prime-power augmentation-kernel point.
- `primePowerCompletedGroupAlgebraAugmentationIdealProjection_zero`
  The finite-stage augmentation-ideal projection is compatible with zero.
- `primePowerCompletedGroupAlgebraAugmentationIdealProjection_add`
  The finite-stage augmentation-ideal projection is compatible with addition.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems

universe u


variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < ℓ)] in
/-- The finite-stage augmentation-ideal projection is compatible with zero. -/
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_zero
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i
        (0 : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) = 0 := by
  rfl

omit [Fact (0 < ℓ)] in
/-- The finite-stage augmentation-ideal projection is compatible with addition. -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_add
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i (x + y) =
      primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i x +
        primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i y := by
  rfl

omit [Fact (0 < ℓ)] in
/-- The finite-stage augmentation-ideal projection is compatible with negation. -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_neg
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i (-x) =
      -primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i x := by
  rfl

omit [Fact (0 < ℓ)] in
/-- The finite-stage augmentation-ideal projection is compatible with subtraction. -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_sub
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i (x - y) =
      primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i x -
        primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i y := by
  rfl

omit [Fact (0 < ℓ)] in
/--
The finite-stage augmentation-ideal projection is compatible with natural-number scalar
multiplication.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_nsmul
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (m : ℕ) (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i (m • x) =
      m • primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i x := by
  rfl

omit [Fact (0 < ℓ)] in
/--
The finite-stage augmentation-ideal projection is compatible with integer scalar multiplication.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_zsmul
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (m : ℤ) (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i (m • x) =
      m • primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i x := by
  rfl

omit [Fact (0 < ℓ)] in
/-- The finite-stage augmentation-ideal projection is compatible with scalar multiplication. -/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_smul
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (a : PrimePowerCompletedCoeff ℓ G)
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i (a • x) =
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        primePowerCompletedGroupAlgebraAugmentationIdealProjection (ℓ := ℓ) (G := G) i x := by
  rfl

/--
A prime-power augmentation-kernel point determines a compatible family in the finite-stage
augmentation ideals.
-/
def toPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    PrimePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G) →
      PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G := by
  intro x
  refine ⟨fun i => ⟨primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x.1, ?_⟩, ?_⟩
  · exact (mem_primePowerCompletedGroupAlgebraStageAugmentationIdeal_iff
      (ℓ := ℓ) (G := G) (i := i)
      (x := primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x.1)).2
      ((mem_primePowerCompletedGroupAlgebraAugmentationKernel_iff_forall
        (ℓ := ℓ) (G := G) (x := x.1)).1 x.2 i)
  · intro i j hij
    apply Subtype.ext
    exact (primePowerCompletedGroupAlgebraSystem ℓ G).projection_compatible x.1 i j hij

omit [Fact (0 < ℓ)] in
/--
The projection-to-stage map is one direction of the completed augmentation-ideal stage
equivalence.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealProjection_to
    (x : PrimePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G))
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    ((primePowerCompletedGroupAlgebraAugmentationIdealProjection
        (ℓ := ℓ) (G := G) i
        (toPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) x)) :
      PrimePowerCompletedGroupAlgebraStage ℓ G i) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x.1 := rfl

/--
A compatible family of prime-power finite-stage augmentation-ideal elements determines a
prime-power augmentation-kernel point.
-/
def ofPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G →
      PrimePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G) := by
  intro x
  let y : PrimePowerCompletedGroupAlgebra ℓ G := ⟨fun i => (x.1 i).1, by
    intro i j hij
    exact congrArg Subtype.val (x.2 i j hij)⟩
  refine ⟨y, ?_⟩
  exact (mem_primePowerCompletedGroupAlgebraAugmentationKernel_iff_forall
    (ℓ := ℓ) (G := G) (x := y)).2 (fun i =>
      (mem_primePowerCompletedGroupAlgebraStageAugmentationIdeal_iff
        (ℓ := ℓ) (G := G) (i := i) (x := (x.1 i).1)).1 (x.1 i).2)

omit [Fact (0 < ℓ)] in
/--
Projecting an element of the completed augmentation ideal gives its corresponding finite-stage
augmentation-ideal coordinate.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_ofAugmentationIdeal
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G)
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
          (ℓ := ℓ) (G := G) x).1 =
      ((primePowerCompletedGroupAlgebraAugmentationIdealProjection
          (ℓ := ℓ) (G := G) i x) :
        PrimePowerCompletedGroupAlgebraStage ℓ G i) := rfl

omit [Fact (0 < ℓ)] in
/--
The completion-to-stage map is one direction of the completed augmentation-ideal stage
equivalence.
-/
@[simp]
theorem ofPrimePowerCompletedGroupAlgebraAugmentationIdeal_to
    (x : PrimePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G)) :
    ofPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G)
        (toPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) x) = x := by
  apply Subtype.ext
  apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
  intro i
  rfl

omit [Fact (0 < ℓ)] in
/--
The stage-to-completion map is one direction of the completed augmentation-ideal stage
equivalence.
-/
@[simp]
theorem toPrimePowerCompletedGroupAlgebraAugmentationIdeal_of
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    toPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G)
        (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) x) = x := by
  apply (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).ext
  intro i
  apply Subtype.ext
  rfl

/--
The prime-power completed augmentation kernel is canonically equivalent to the inverse limit of
the prime-power finite-stage augmentation ideals.
-/
def primePowerCompletedGroupAlgebraAugmentationKernelEquivInverseLimit :
    PrimePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G) ≃
      PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G where
  toFun := toPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G)
  invFun := ofPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G)
  left_inv := ofPrimePowerCompletedGroupAlgebraAugmentationIdeal_to (ℓ := ℓ) (G := G)
  right_inv := toPrimePowerCompletedGroupAlgebraAugmentationIdeal_of (ℓ := ℓ) (G := G)

omit [Fact (0 < ℓ)] in
/--
The forward augmentation-kernel equivalence is the canonical map to the inverse-limit augmentation
ideal.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationKernelEquivInverseLimit_apply
    (x : PrimePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G)) :
    primePowerCompletedGroupAlgebraAugmentationKernelEquivInverseLimit
        (ℓ := ℓ) (G := G) x =
      toPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) x := rfl

omit [Fact (0 < ℓ)] in
/--
The inverse augmentation-kernel equivalence reconstructs a kernel element from an inverse-limit
augmentation-ideal element.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationKernelEquivInverseLimit_symm_apply
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    (primePowerCompletedGroupAlgebraAugmentationKernelEquivInverseLimit
        (ℓ := ℓ) (G := G)).symm x =
      ofPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) x := rfl

end

end FoxDifferential
