import ProCGroups.FoxDifferential.Completed.CoefficientRings.AugmentationIdealPrimePower.Augmentation

set_option autoImplicit false

/-!
# Fox differential: completed — coefficient rings — prime-power augmentation ideal — subtype linear

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraAugmentationIdealAddEquivAddSubgroup`
  The inverse-limit augmentation ideal is additively equivalent to the additive kernel of the
  canonical prime-power augmentation.
- `primePowerCompletedGroupAlgebraAugmentationIdealLinearEquivAddSubgroup`
  The inverse-limit augmentation ideal is linearly equivalent to the additive kernel of the
  canonical prime-power augmentation.
- `primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear_apply`
  The integral-linear inclusion of the prime-power augmentation ideal returns the underlying
  completed group-algebra element.
- `primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear_apply`
  The coefficient-linear inclusion of the prime-power augmentation ideal returns the underlying
  completed group-algebra element.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems

universe u


variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
The inverse-limit augmentation ideal is additively equivalent to the additive kernel of the
canonical prime-power augmentation.
-/
def primePowerCompletedGroupAlgebraAugmentationIdealAddEquivAddSubgroup :
    PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G ≃+
      primePowerCompletedGroupAlgebraAugmentationAddSubgroup (ℓ := ℓ) (G := G) where
  toFun x := by
    refine ⟨(ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
      (ℓ := ℓ) (G := G) x).1, ?_⟩
    exact (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
      (ℓ := ℓ) (G := G) x).2
  invFun x :=
    toPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) <|
      ⟨x.1, by
        exact x.2⟩
  left_inv := by
    intro x
    exact toPrimePowerCompletedGroupAlgebraAugmentationIdeal_of
      (ℓ := ℓ) (G := G) x
  right_inv := by
    intro x
    apply Subtype.ext
    let y : PrimePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G) :=
      ⟨x.1, by
        exact x.2⟩
    exact congrArg Subtype.val
      (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal_to
        (ℓ := ℓ) (G := G) y)
  map_add' x y := by
    apply Subtype.ext
    apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
    intro i
    rfl

/--
The inverse-limit augmentation ideal is linearly equivalent to the additive kernel of the
canonical prime-power augmentation.
-/
def primePowerCompletedGroupAlgebraAugmentationIdealLinearEquivAddSubgroup :
    PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G ≃ₗ[ℤ]
      primePowerCompletedGroupAlgebraAugmentationAddSubgroup (ℓ := ℓ) (G := G) :=
  (primePowerCompletedGroupAlgebraAugmentationIdealAddEquivAddSubgroup
    (ℓ := ℓ) (G := G)).toIntLinearEquiv

/--
The canonical inclusion of the inverse-limit augmentation ideal into the prime-power completed
group algebra.
-/
def primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear :
    PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G →ₗ[ℤ]
      PrimePowerCompletedGroupAlgebra ℓ G :=
  (primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear
    (ℓ := ℓ) (G := G)).comp
      (primePowerCompletedGroupAlgebraAugmentationIdealLinearEquivAddSubgroup
        (ℓ := ℓ) (G := G)).toLinearMap

omit [Fact (0 < ℓ)] in
/--
The integral-linear inclusion of the prime-power augmentation ideal returns the underlying completed
group-algebra element.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear_apply
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
        (ℓ := ℓ) (G := G) x =
      (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
        (ℓ := ℓ) (G := G) x).1 := by
  rfl

/--
The canonical inclusion of the inverse-limit augmentation ideal into the prime-power completed
group algebra, viewed over the completed coefficient ring.
-/
def primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear :
    PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G →ₗ[PrimePowerCompletedCoeff ℓ G]
      PrimePowerCompletedGroupAlgebra ℓ G where
  toFun := fun x =>
    (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) x).1
  map_add' := by
    intro x y
    apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
    intro i
    change (((primePowerCompletedGroupAlgebraAugmentationIdealProjection
        (ℓ := ℓ) (G := G) i x +
          primePowerCompletedGroupAlgebraAugmentationIdealProjection
            (ℓ := ℓ) (G := G) i y :
          primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i) :
            PrimePowerCompletedGroupAlgebraStage ℓ G i)) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        ((ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
          (ℓ := ℓ) (G := G) x).1 +
          (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
            (ℓ := ℓ) (G := G) y).1)
    rw [primePowerCompletedGroupAlgebraProjection_add,
      primePowerCompletedGroupAlgebraProjection_ofAugmentationIdeal,
      primePowerCompletedGroupAlgebraProjection_ofAugmentationIdeal]
    rfl
  map_smul' := by
    intro a x
    apply (primePowerCompletedGroupAlgebraSystem ℓ G).ext
    intro i
    change (((primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i a) •
        primePowerCompletedGroupAlgebraAugmentationIdealProjection
          (ℓ := ℓ) (G := G) i x :
          primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i) :
            PrimePowerCompletedGroupAlgebraStage ℓ G i) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (a • (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
          (ℓ := ℓ) (G := G) x).1)
    rw [primePowerCompletedGroupAlgebraProjection_smul,
      primePowerCompletedGroupAlgebraProjection_ofAugmentationIdeal]
    rfl

omit [Fact (0 < ℓ)] in
/--
The coefficient-linear inclusion of the prime-power augmentation ideal returns the underlying
completed group-algebra element.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear_apply
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear
        (ℓ := ℓ) (G := G) x =
      (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
        (ℓ := ℓ) (G := G) x).1 := rfl

omit [Fact (0 < ℓ)] in
/-- The canonical linear inclusion of the completed augmentation ideal is injective. -/
theorem primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear_injective :
    Function.Injective
      (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
        (ℓ := ℓ) (G := G)) := by
  intro x y hxy
  apply (primePowerCompletedGroupAlgebraAugmentationIdealLinearEquivAddSubgroup
    (ℓ := ℓ) (G := G)).injective
  exact
    (primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear_injective
      (ℓ := ℓ) (G := G)) hxy

omit [Fact (0 < ℓ)] in
/--
The linear inclusion of the prime-power completed augmentation ideal has image equal to the
kernel of the prime-power augmentation.
-/
theorem exact_primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear :
    Function.Exact
      (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
        (ℓ := ℓ) (G := G))
      (primePowerCompletedGroupAlgebraAugmentationLinear (ℓ := ℓ) (G := G)) := by
  intro x
  constructor
  · intro hx
    rcases
        (exact_primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear
          (ℓ := ℓ) (G := G) x).1 hx with
      ⟨y, hy⟩
    refine ⟨(primePowerCompletedGroupAlgebraAugmentationIdealLinearEquivAddSubgroup
      (ℓ := ℓ) (G := G)).symm y, ?_⟩
    simpa [primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear] using hy
  · rintro ⟨y, rfl⟩
    let z :=
      (primePowerCompletedGroupAlgebraAugmentationIdealLinearEquivAddSubgroup
        (ℓ := ℓ) (G := G)) y
    exact
      (exact_primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear
        (ℓ := ℓ) (G := G)
        ((primePowerCompletedGroupAlgebraAugmentationAddSubgroupSubtypeLinear
          (ℓ := ℓ) (G := G)) z)).2
        ⟨z, rfl⟩

omit [Fact (0 < ℓ)] in
/--
The canonical augmentation sequence with augmentation ideal as kernel is short exact: the
inclusion is injective, its image is the kernel of augmentation, and the augmentation is
surjective.
-/
theorem primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear_shortExact :
    Function.Injective
        (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
          (ℓ := ℓ) (G := G)) ∧
      Function.Exact
        (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
          (ℓ := ℓ) (G := G))
        (primePowerCompletedGroupAlgebraAugmentationLinear (ℓ := ℓ) (G := G)) ∧
      Function.Surjective
        (primePowerCompletedGroupAlgebraAugmentationLinear (ℓ := ℓ) (G := G)) := by
  refine ⟨
    primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear_injective
      (ℓ := ℓ) (G := G),
    exact_primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
      (ℓ := ℓ) (G := G),
    primePowerCompletedGroupAlgebraAugmentationLinear_surjective (ℓ := ℓ) (G := G)⟩

omit [Fact (0 < ℓ)] in
/-- The coefficient-linear form of the prime-power completed augmentation is surjective. -/
theorem primePowerCompletedGroupAlgebraAugmentationCoeffLinear_surjective :
    Function.Surjective
      (primePowerCompletedGroupAlgebraAugmentationCoeffLinear (ℓ := ℓ) (G := G)) := by
  intro y
  rcases primePowerCompletedGroupAlgebraAugmentation_surjective
      (ℓ := ℓ) (G := G) y with ⟨x, hx⟩
  refine ⟨x, ?_⟩
  change primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x = y
  exact hx

omit [Fact (0 < ℓ)] in
/-- The canonical linear inclusion of the completed augmentation ideal is injective. -/
theorem primePowerCompletedGAAugmentationIdealToGACoeffLinear_inj :
    Function.Injective
      (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear
        (ℓ := ℓ) (G := G)) := by
  intro x y hxy
  apply primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear_injective
    (ℓ := ℓ) (G := G)
  change
    (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
        (ℓ := ℓ) (G := G) x).1 =
      (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
        (ℓ := ℓ) (G := G) y).1
  change
    (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
        (ℓ := ℓ) (G := G) x).1 =
      (ofPrimePowerCompletedGroupAlgebraAugmentationIdeal
        (ℓ := ℓ) (G := G) y).1 at hxy
  exact hxy

omit [Fact (0 < ℓ)] in
/--
The coefficient-linear inclusion of the prime-power completed augmentation ideal has image equal
to the kernel of the coefficient-linear augmentation.
-/
theorem exact_primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear :
    Function.Exact
      (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear
        (ℓ := ℓ) (G := G))
      (primePowerCompletedGroupAlgebraAugmentationCoeffLinear (ℓ := ℓ) (G := G)) := by
  change Function.Exact
    (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
      (ℓ := ℓ) (G := G))
    (primePowerCompletedGroupAlgebraAugmentationLinear (ℓ := ℓ) (G := G))
  exact exact_primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraLinear
    (ℓ := ℓ) (G := G)

omit [Fact (0 < ℓ)] in
/--
The canonical augmentation sequence with augmentation ideal as kernel is short exact: the
inclusion is injective, its image is the kernel of augmentation, and the augmentation is
surjective.
-/
theorem primePowerCompletedGAAugmentationIdealToGACoeffLinear_shortExact :
    Function.Injective
        (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear
          (ℓ := ℓ) (G := G)) ∧
      Function.Exact
        (primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear
          (ℓ := ℓ) (G := G))
        (primePowerCompletedGroupAlgebraAugmentationCoeffLinear (ℓ := ℓ) (G := G)) ∧
      Function.Surjective
        (primePowerCompletedGroupAlgebraAugmentationCoeffLinear (ℓ := ℓ) (G := G)) := by
  refine ⟨
    primePowerCompletedGAAugmentationIdealToGACoeffLinear_inj
      (ℓ := ℓ) (G := G),
    exact_primePowerCompletedGroupAlgebraAugmentationIdealToGroupAlgebraCoeffLinear
      (ℓ := ℓ) (G := G),
    primePowerCompletedGroupAlgebraAugmentationCoeffLinear_surjective (ℓ := ℓ) (G := G)⟩

end

end FoxDifferential
