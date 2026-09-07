import ProCGroups.FoxDifferential.Completed.CoefficientRings.AugmentationIdealPrimePower.Stage

set_option autoImplicit false

/-!
# Fox differential: completed — coefficient rings — prime-power augmentation ideal — additive

The principal declarations in this module are:

- `instAddCommGroupPrimePowerCompletedGroupAlgebraAugmentationIdealStage`
  Each finite-stage prime-power augmentation ideal inherits an additive commutative group structure
  from its ambient finite group algebra.
- `instAddCommGroupPrimePowerCompletedGroupAlgebraAugmentationIdealFamily`
  The dependent family of finite-stage prime-power augmentation ideals carries the pointwise
  additive commutative group structure.
- `coe_zero_primePowerCompletedGroupAlgebraAugmentationIdeal`
  The inclusion of the completed augmentation ideal preserves zero.
- `coe_add_primePowerCompletedGroupAlgebraAugmentationIdeal`
  The inclusion of the completed augmentation ideal preserves addition.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems

universe u


variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
The zero element of the prime-power completed augmentation ideal is the compatible family of
zero elements at all finite stages.
-/
instance instZeroPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    Zero (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  zero := ⟨fun i =>
    (0 : primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i), by
    intro i j hij
    apply Subtype.ext
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
      (0 : PrimePowerCompletedGroupAlgebraStage ℓ G j) = 0
    exact map_zero _⟩

/--
Addition in the prime-power completed augmentation ideal is defined coordinatewise through
finite stages.
-/
instance instAddPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    Add (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  add x y := ⟨fun i =>
      (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
        from x.1 i) +
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
          from y.1 i), by
    intro i j hij
    apply Subtype.ext
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from x.1 j) : PrimePowerCompletedGroupAlgebraStage ℓ G j) +
          ((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from y.1 j) : PrimePowerCompletedGroupAlgebraStage ℓ G j)) =
      (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
          from x.1 i) : PrimePowerCompletedGroupAlgebraStage ℓ G i) +
        ((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
          from y.1 i) : PrimePowerCompletedGroupAlgebraStage ℓ G i))
    rw [map_add]
    exact congrArg₂ HAdd.hAdd
      (congrArg Subtype.val (x.2 i j hij))
      (congrArg Subtype.val (y.2 i j hij))⟩

/--
Coordinatewise zero and addition on the prime-power completed augmentation ideal satisfy the
left and right zero laws.
-/
instance instAddZeroClassPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    AddZeroClass (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  zero := 0
  add := (· + ·)
  zero_add x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change (0 : PrimePowerCompletedGroupAlgebraStage ℓ G i) +
      ((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i from x.1 i) :
        PrimePowerCompletedGroupAlgebraStage ℓ G i) =
      ((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i from x.1 i) :
        PrimePowerCompletedGroupAlgebraStage ℓ G i)
    simp only [zero_add]
  add_zero x := by
    apply Subtype.ext
    funext i
    apply Subtype.ext
    change ((show primePowerCompletedGroupAlgebraStageAugmentationIdeal
        (ℓ := ℓ) (G := G) i from x.1 i) :
        PrimePowerCompletedGroupAlgebraStage ℓ G i) +
      (0 : PrimePowerCompletedGroupAlgebraStage ℓ G i) =
      ((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i from x.1 i) :
        PrimePowerCompletedGroupAlgebraStage ℓ G i)
    simp only [add_zero]

/--
Negation on the prime-power completed augmentation ideal is defined coordinatewise through
finite-stage negations.
-/
instance instNegPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    Neg (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  neg x := ⟨fun i =>
    -(show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
      from x.1 i), by
    intro i j hij
    apply Subtype.ext
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (-(((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from x.1 j) : PrimePowerCompletedGroupAlgebraStage ℓ G j))) =
      -(((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
          from x.1 i) : PrimePowerCompletedGroupAlgebraStage ℓ G i))
    rw [map_neg]
    exact congrArg Neg.neg (congrArg Subtype.val (x.2 i j hij))⟩

/--
Subtraction on the prime-power completed augmentation ideal is defined coordinatewise through
the finite-stage augmentation ideals.
-/
instance instSubPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    Sub (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  sub x y := ⟨fun i =>
      (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
        from x.1 i) -
        (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
          from y.1 i), by
    intro i j hij
    apply Subtype.ext
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        ((((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from x.1 j) : PrimePowerCompletedGroupAlgebraStage ℓ G j)) -
          (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from y.1 j) : PrimePowerCompletedGroupAlgebraStage ℓ G j))) =
      ((((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
            from x.1 i) : PrimePowerCompletedGroupAlgebraStage ℓ G i)) -
        (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
            from y.1 i) : PrimePowerCompletedGroupAlgebraStage ℓ G i)))
    rw [map_sub]
    exact congrArg₂ HSub.hSub
      (congrArg Subtype.val (x.2 i j hij))
      (congrArg Subtype.val (y.2 i j hij))⟩

/--
The prime-power completed augmentation ideal carries natural-number scalar multiplication
coordinatewise at every finite quotient stage.
-/
instance instSMulNatPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    SMul ℕ (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  smul m x := ⟨fun i =>
    m • (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
      from x.1 i), by
    intro i j hij
    apply Subtype.ext
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (m • (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from x.1 j) : PrimePowerCompletedGroupAlgebraStage ℓ G j))) =
      m • (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
          from x.1 i) : PrimePowerCompletedGroupAlgebraStage ℓ G i))
    rw [map_nsmul]
    exact congrArg (m • ·) (congrArg Subtype.val (x.2 i j hij))⟩

/--
The prime-power completed augmentation ideal carries integer scalar multiplication
coordinatewise at every finite quotient stage.
-/
instance instSMulIntPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    SMul ℤ (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) where
  smul m x := ⟨fun i =>
    m • (show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
      from x.1 i), by
    intro i j hij
    apply Subtype.ext
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (m • (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j
            from x.1 j) : PrimePowerCompletedGroupAlgebraStage ℓ G j))) =
      m • (((show primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i
          from x.1 i) : PrimePowerCompletedGroupAlgebraStage ℓ G i))
    rw [map_zsmul]
    exact congrArg (m • ·) (congrArg Subtype.val (x.2 i j hij))⟩

/--
Each finite-stage prime-power augmentation ideal inherits an additive commutative group structure
from its ambient finite group algebra.
-/
@[reducible]
private def instAddCommGroupPrimePowerCompletedGroupAlgebraAugmentationIdealStage
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    AddCommGroup ((primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) := by
  dsimp [primePowerCompletedGroupAlgebraAugmentationIdealSystem]
  infer_instance
attribute [local instance] instAddCommGroupPrimePowerCompletedGroupAlgebraAugmentationIdealStage

/--
The dependent family of finite-stage prime-power augmentation ideals carries the pointwise
additive commutative group structure.
-/
@[reducible]
private def instAddCommGroupPrimePowerCompletedGroupAlgebraAugmentationIdealFamily :
    AddCommGroup
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) :=
  inferInstance
attribute [local instance] instAddCommGroupPrimePowerCompletedGroupAlgebraAugmentationIdealFamily

omit [Fact (0 < ℓ)] in
/-- The inclusion of the completed augmentation ideal preserves zero. -/
@[simp]
theorem coe_zero_primePowerCompletedGroupAlgebraAugmentationIdeal :
    ((0 : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) = 0 := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- The inclusion of the completed augmentation ideal preserves addition. -/
@[simp]
theorem coe_add_primePowerCompletedGroupAlgebraAugmentationIdeal
    (x y : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    ((x + y : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) = x + y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- The inclusion of the completed augmentation ideal preserves negation. -/
@[simp]
theorem coe_neg_primePowerCompletedGroupAlgebraAugmentationIdeal
    (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    ((-x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) = -x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- The inclusion of the completed augmentation ideal preserves subtraction. -/
@[simp]
theorem coe_sub_primePowerCompletedGroupAlgebraAugmentationIdeal
    (x y : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    ((x - y : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) = x - y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/--
The inclusion of the completed augmentation ideal preserves natural-number scalar
multiplication.
-/
@[simp]
theorem coe_nsmul_primePowerCompletedGroupAlgebraAugmentationIdeal
    (m : ℕ) (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    ((m • x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) = m • x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- The inclusion of the completed augmentation ideal preserves integer scalar multiplication. -/
@[simp]
theorem coe_zsmul_primePowerCompletedGroupAlgebraAugmentationIdeal
    (m : ℤ) (x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
    ((m • x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i) = m • x := by
  funext i
  rfl

/--
The prime-power completed augmentation ideal inherits an additive commutative group structure
from its injective inclusion into the family of finite-stage ideals.
-/
instance instAddCommGroupPrimePowerCompletedGroupAlgebraAugmentationIdeal :
    AddCommGroup (PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G) :=
  Function.Injective.addCommGroup
    (fun x : PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G =>
      (x :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).X i))
    Subtype.val_injective
    (coe_zero_primePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G))
    (coe_add_primePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G))
    (coe_neg_primePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G))
    (coe_sub_primePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G))
    (fun x m => coe_nsmul_primePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) m x)
    (fun x m => coe_zsmul_primePowerCompletedGroupAlgebraAugmentationIdeal (ℓ := ℓ) (G := G) m x)


end

end FoxDifferential
