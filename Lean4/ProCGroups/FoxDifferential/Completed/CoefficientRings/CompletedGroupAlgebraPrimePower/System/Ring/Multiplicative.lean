import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.System.Ring.AddCommGroup

set_option autoImplicit false

/-!
# Fox differential: prime-power completed group algebra — system — ring — multiplicative

The principal declarations in this module are:

- `instRingPrimePowerCompletedGroupAlgebraStage`
  Each finite prime-power group-algebra stage carries its standard ring structure.
- `instRingPrimePowerCompletedGroupAlgebraFamily`
  The dependent family of finite prime-power group-algebra stages carries the pointwise ring
  structure.
- `coe_one_primePowerCompletedGroupAlgebra`
  The multiplicative identity in the prime-power completed group algebra is computed coordinatewise.
- `coe_mul_primePowerCompletedGroupAlgebra`
  Multiplication in the prime-power completed group algebra is computed coordinatewise.
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
attribute [local instance] instAddCommGroupPrimePowerCompletedGroupAlgebra

/-- The prime-power completed group algebra has a coordinatewise multiplicative identity. -/
instance instOnePrimePowerCompletedGroupAlgebra : One (PrimePowerCompletedGroupAlgebra ℓ G) where
  one := ⟨fun i => (1 : PrimePowerCompletedGroupAlgebraStage ℓ G i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
      (1 : PrimePowerCompletedGroupAlgebraStage ℓ G j) = 1
    exact map_one _⟩

/--
Multiplication on the completed group algebra is defined coordinatewise through the finite-stage
group-algebra products.
-/
instance instMulPrimePowerCompletedGroupAlgebra : Mul (PrimePowerCompletedGroupAlgebra ℓ G) where
  mul x y := ⟨fun i =>
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) *
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i), by
    intro i j hij
    calc
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          ((show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j) *
            (show PrimePowerCompletedGroupAlgebraStage ℓ G j from y.1 j))
        =
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          (show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j) *
        primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
          (show PrimePowerCompletedGroupAlgebraStage ℓ G j from y.1 j) := by
            rw [map_mul]
      _ =
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) *
        (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i) := by
            exact congrArg₂ HMul.hMul (x.2 i j hij) (y.2 i j hij)⟩

/-- Natural number casts in the prime-power completed group algebra are computed coordinatewise. -/
instance instNatCastPrimePowerCompletedGroupAlgebra :
    NatCast (PrimePowerCompletedGroupAlgebra ℓ G) where
  natCast n := ⟨fun i => (n : PrimePowerCompletedGroupAlgebraStage ℓ G i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
      (n : PrimePowerCompletedGroupAlgebraStage ℓ G j) = n
    exact map_natCast _ _⟩

/-- Integer casts in the prime-power completed group algebra are computed coordinatewise. -/
instance instIntCastPrimePowerCompletedGroupAlgebra :
    IntCast (PrimePowerCompletedGroupAlgebra ℓ G) where
  intCast n := ⟨fun i => (n : PrimePowerCompletedGroupAlgebraStage ℓ G i), by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
      (n : PrimePowerCompletedGroupAlgebraStage ℓ G j) = n
    exact map_intCast _ _⟩

/-- Each finite prime-power group-algebra stage carries its standard ring structure. -/
@[reducible]
private def instRingPrimePowerCompletedGroupAlgebraStage
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    Ring ((primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  dsimp [primePowerCompletedGroupAlgebraSystem, PrimePowerCompletedGroupAlgebraStage]
  infer_instance
attribute [local instance] instRingPrimePowerCompletedGroupAlgebraStage

/--
The dependent family of finite prime-power group-algebra stages carries the pointwise ring
structure.
-/
@[reducible]
private def instRingPrimePowerCompletedGroupAlgebraFamily :
    Ring
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) :=
  inferInstance
attribute [local instance] instRingPrimePowerCompletedGroupAlgebraFamily

/-- Powers in the prime-power completed group algebra are computed coordinatewise. -/
instance instPowPrimePowerCompletedGroupAlgebra : Pow (PrimePowerCompletedGroupAlgebra ℓ G) ℕ where
  pow x n := ⟨fun i => (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) ^ n, by
    intro i j hij
    change primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij
        ((show PrimePowerCompletedGroupAlgebraStage ℓ G j from x.1 j) ^ n) =
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) ^ n
    rw [map_pow]
    exact congrArg (fun t => t ^ n) (x.2 i j hij)⟩

omit [Fact (0 < ℓ)] in
/--
The multiplicative identity in the prime-power completed group algebra is computed
coordinatewise.
-/
@[simp]
theorem coe_one_primePowerCompletedGroupAlgebra :
    ((1 : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) =
      (1 :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- Multiplication in the prime-power completed group algebra is computed coordinatewise. -/
@[simp]
theorem coe_mul_primePowerCompletedGroupAlgebra
    (x y : PrimePowerCompletedGroupAlgebra ℓ G) :
    ((x * y : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) =
      (x * y :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- Natural number casts in the prime-power completed group algebra are computed coordinatewise. -/
@[simp]
theorem coe_natCast_primePowerCompletedGroupAlgebra
    (n : ℕ) :
    ((n : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) =
      (n :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- Integer casts in the prime-power completed group algebra are computed coordinatewise. -/
@[simp]
theorem coe_intCast_primePowerCompletedGroupAlgebra
    (n : ℤ) :
    ((n : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) =
      (n :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] in
/-- Powers in the prime-power completed group algebra are computed coordinatewise. -/
@[simp]
theorem coe_pow_primePowerCompletedGroupAlgebra
    (x : PrimePowerCompletedGroupAlgebra ℓ G) (n : ℕ) :
    ((x ^ n : PrimePowerCompletedGroupAlgebra ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedGroupAlgebraSystem ℓ G).X i) =
      (x ^ n :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i) := by
  funext i
  rfl

/--
The completed group algebra is a ring because all ring operations and ring axioms are inherited
coordinatewise from the finite-stage group algebras.
-/
instance instRingPrimePowerCompletedGroupAlgebra :
    Ring (PrimePowerCompletedGroupAlgebra ℓ G) :=
  Function.Injective.ring
    (fun x : PrimePowerCompletedGroupAlgebra ℓ G =>
      (x :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedGroupAlgebraSystem ℓ G).X i))
    Subtype.val_injective
    (coe_zero_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_one_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_add_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_mul_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_neg_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (coe_sub_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G))
    (fun n x => coe_nsmul_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G) n x)
    (fun n x => coe_zsmul_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G) n x)
    (fun x n => coe_pow_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G) x n)
    (by
      intro n
      exact coe_natCast_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G) n)
    (by
      intro z
      exact coe_intCast_primePowerCompletedGroupAlgebra (ℓ := ℓ) (G := G) z)

end

end FoxDifferential
