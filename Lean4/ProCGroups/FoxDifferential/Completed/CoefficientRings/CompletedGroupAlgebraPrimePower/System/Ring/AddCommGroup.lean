import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.System.Basic

set_option autoImplicit false

/-!
# Fox differential: prime-power completed group algebra — system — ring — add comm group

The principal declarations in this module are:

- `instAddCommGroupPrimePowerCompletedGroupAlgebraStage`
  Each finite prime-power group-algebra stage carries its standard additive group.
- `instAddCommGroupPrimePowerCompletedGroupAlgebraFamily`
  The dependent family of finite prime-power group-algebra stages carries the pointwise additive
  commutative group structure.
- `coe_zero_primePowerCompletedGroupAlgebra`
  The inclusion of the prime-power completed group algebra preserves zero.
- `coe_add_primePowerCompletedGroupAlgebra`
  The inclusion of the prime-power completed group algebra preserves addition.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
The zero element is defined coordinatewise as the compatible family of zero elements at all
finite stages.
-/
instance instZeroPrimePowerCompletedGroupAlgebra : Zero (PrimePowerCompletedGroupAlgebra ℓ G) where
  zero := ⟨fun i => (0 : PrimePowerCompletedGroupAlgebraStage ℓ G i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
      (0 : PrimePowerCompletedGroupAlgebraStage ℓ G j) = 0
    exact map_zero _⟩

/--
Addition in the prime-power completed group algebra is defined coordinatewise through
finite-stage group-algebra additions.
-/
instance instAddPrimePowerCompletedGroupAlgebra : Add (PrimePowerCompletedGroupAlgebra ℓ G) where
  add x y := ⟨fun i =>
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) +
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i), by
    intro i j hij
    calc
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          ((show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j) +
            (show PrimePowerCompletedGroupAlgebraStage ℓ G j from y.1 j))
        =
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          (show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j) +
        primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          (show PrimePowerCompletedGroupAlgebraStage ℓ G j from y.1 j) := by
            rw [map_add]
      _ =
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) +
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i) := by
            exact congrArg₂ HAdd.hAdd (x.2 i j hij) (y.2 i j hij)⟩

/--
Coordinatewise zero and addition on the prime-power completed group algebra satisfy the left and
right zero laws.
-/
instance instAddZeroClassPrimePowerCompletedGroupAlgebra :
    AddZeroClass (PrimePowerCompletedGroupAlgebra ℓ G) where
  zero := 0
  add := (· + ·)
  zero_add x := by
    apply Subtype.ext
    funext i
    change (0 : PrimePowerCompletedGroupAlgebraStage ℓ G i) +
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) =
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
    exact zero_add (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
  add_zero x := by
    apply Subtype.ext
    funext i
    change (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) +
      (0 : PrimePowerCompletedGroupAlgebraStage ℓ G i) =
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
    exact add_zero (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)

/--
Negation on the prime-power completed group algebra is defined coordinatewise through
finite-stage group-algebra negations.
-/
instance instNegPrimePowerCompletedGroupAlgebra : Neg (PrimePowerCompletedGroupAlgebra ℓ G) where
  neg x := ⟨fun i => -(show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (-(show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j)) =
      -(show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
    rw [map_neg]
    exact congrArg Neg.neg (x.2 i j hij)⟩

/--
Subtraction on the completed group algebra is defined coordinatewise through the finite-stage
group-algebra subtractions.
-/
instance instSubPrimePowerCompletedGroupAlgebra : Sub (PrimePowerCompletedGroupAlgebra ℓ G) where
  sub x y := ⟨fun i =>
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) -
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        ((show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j) -
          (show PrimePowerCompletedGroupAlgebraStage ℓ G j from y.1 j)) =
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) -
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i)
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 i j hij) (y.2 i j hij)⟩

/--
The completed group algebra carries coefficient-ring scalar multiplication by applying the
scalar action at every finite quotient stage.
-/
instance instSMulNatPrimePowerCompletedGroupAlgebra :
    SMul ℕ (PrimePowerCompletedGroupAlgebra ℓ G) where
  smul m x := ⟨fun i => m • (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (m • (show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j)) =
      m • (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
    rw [map_nsmul]
    exact congrArg (m • ·) (x.2 i j hij)⟩

/--
The completed group algebra carries coefficient-ring scalar multiplication by applying the
scalar action at every finite quotient stage.
-/
instance instSMulIntPrimePowerCompletedGroupAlgebra :
    SMul ℤ (PrimePowerCompletedGroupAlgebra ℓ G) where
  smul m x := ⟨fun i => m • (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        (m • (show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j)) =
      m • (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i)
    rw [map_zsmul]
    exact congrArg (m • ·) (x.2 i j hij)⟩

/-- Each finite prime-power group-algebra stage carries its standard additive group. -/
@[reducible] def instAddCommGroupPrimePowerCompletedGroupAlgebraStage
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    AddCommGroup ((primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  dsimp [primePowerCompletedGroupAlgebraSystem, PrimePowerCompletedGroupAlgebraStage]
  infer_instance

attribute [local instance] instAddCommGroupPrimePowerCompletedGroupAlgebraStage

/--
The dependent family of finite prime-power group-algebra stages carries the pointwise additive
commutative group structure.
-/
@[reducible] def instAddCommGroupPrimePowerCompletedGroupAlgebraFamily :
    AddCommGroup
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) :=
  inferInstance

attribute [local instance] instAddCommGroupPrimePowerCompletedGroupAlgebraFamily

omit [Fact (0 < ℓ)] in
/-- The inclusion of the prime-power completed group algebra preserves zero. -/
@[simp]
theorem coe_zero_primePowerCompletedGroupAlgebra :
    ((0 : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) = 0 := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- The inclusion of the prime-power completed group algebra preserves addition. -/
@[simp]
theorem coe_add_primePowerCompletedGroupAlgebra
    (x y : PrimePowerCompletedGroupAlgebra ℓ G) :
    ((x + y : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) = x + y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- The inclusion of the prime-power completed group algebra preserves negation. -/
@[simp]
theorem coe_neg_primePowerCompletedGroupAlgebra
    (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    ((-x : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) = -x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- The inclusion of the prime-power completed group algebra preserves subtraction. -/
@[simp]
theorem coe_sub_primePowerCompletedGroupAlgebra
    (x y : PrimePowerCompletedGroupAlgebra ℓ G) :
    ((x - y : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) = x - y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/--
The inclusion of the prime-power completed group algebra preserves natural-number scalar
multiplication.
-/
@[simp]
theorem coe_nsmul_primePowerCompletedGroupAlgebra
    (m : ℕ) (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    ((m • x : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) = m • x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/--
The inclusion of the prime-power completed group algebra preserves integer scalar
multiplication.
-/
@[simp]
theorem coe_zsmul_primePowerCompletedGroupAlgebra
    (m : ℤ) (x : PrimePowerCompletedGroupAlgebra ℓ G) :
    ((m • x : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) = m • x := by
  funext i
  rfl

/--
The prime-power completion inherits an additive commutative group structure from its injective
inclusion into the family of finite stages.
-/
@[reducible] def instAddCommGroupPrimePowerCompletedGroupAlgebra :
    AddCommGroup (PrimePowerCompletedGroupAlgebra ℓ G) :=
  Function.Injective.addCommGroup
    (fun x : PrimePowerCompletedGroupAlgebra ℓ G =>
      (x :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i))
    Subtype.val_injective
    (coe_zero_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_add_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_neg_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_sub_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (fun x m => coe_nsmul_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G) m x)
    (fun x m => coe_zsmul_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G) m x)

attribute [local instance] instAddCommGroupPrimePowerCompletedGroupAlgebra

end

end FoxDifferential
