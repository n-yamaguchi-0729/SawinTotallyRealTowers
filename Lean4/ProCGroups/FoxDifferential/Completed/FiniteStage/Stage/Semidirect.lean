import ProCGroups.FoxDifferential.Completed.FiniteStage.Basic

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — stage — semidirect

The principal declarations in this module are:

- `foxAlgebraicStageTargetQuotient`
  The finite-stage target quotient \(F/N\).
- `foxAlgebraicStageTargetGroupAlgebra`
  The finite-stage target group algebra \((\mathbb{Z}/n\mathbb{Z})[F/N]\).
- `mem_foxAlgebraicStageGroupAlgebraMapKernelIdeal`
  Membership test for the finite-stage group-algebra map kernel ideal.
- `mem_foxAlgebraicStageSourceAugmentationIdeal`
  Membership in the finite-stage source augmentation ideal is equivalent to vanishing under the
  finite-stage source augmentation map.
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

/-- The finite-stage target quotient \(F/N\). -/
abbrev foxAlgebraicStageTargetQuotient : Type u :=
  FreeGroup X ⧸ N

/-- The finite-stage target group algebra \((\mathbb{Z}/n\mathbb{Z})[F/N]\). -/
abbrev foxAlgebraicStageTargetGroupAlgebra : Type u :=
  MonoidAlgebra (ModNCompletedCoeff n) (foxAlgebraicStageTargetQuotient (X := X) N)

/-- The finite-stage source group algebra \((\mathbb{Z}/n\mathbb{Z})[F/[N,N]N^n]\). -/
abbrev foxAlgebraicStageSourceGroupAlgebra : Type u :=
  MonoidAlgebra (ModNCompletedCoeff n)
    (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)

/--
The finite-stage kernel \(K_j\) of \((\mathbb{Z}/n\mathbb{Z})[F/[N,N]N^n] \to
(\mathbb{Z}/n\mathbb{Z})[F/N]\).
-/
def foxAlgebraicStageGroupAlgebraMapKernelIdeal :
    Ideal (foxAlgebraicStageSourceGroupAlgebra (X := X) N n) :=
  RingHom.ker (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n)

omit [DecidableEq X] in
/-- Membership test for the finite-stage group-algebra map kernel ideal. -/
@[simp]
theorem mem_foxAlgebraicStageGroupAlgebraMapKernelIdeal
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ}
    {x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n} :
    x ∈ foxAlgebraicStageGroupAlgebraMapKernelIdeal (X := X) N n ↔
      foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n x = 0 := by
  rfl

/--
The finite-stage source augmentation ideal is the kernel of the corresponding finite-stage
augmentation map.
-/
def foxAlgebraicStageSourceAugmentationIdeal :
    Ideal (foxAlgebraicStageSourceGroupAlgebra (X := X) N n) :=
  RingHom.ker
    (foxCommutatorPowerSourceGroupAlgebraAugmentation
      (F := FreeGroup X) N n).toRingHom

omit [DecidableEq X] in
/--
Membership in the finite-stage source augmentation ideal is equivalent to vanishing under the
finite-stage source augmentation map.
-/
@[simp]
theorem mem_foxAlgebraicStageSourceAugmentationIdeal
    {N : Subgroup (FreeGroup X)} {n : ℕ}
    {x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n} :
    x ∈ foxAlgebraicStageSourceAugmentationIdeal (X := X) N n ↔
      foxCommutatorPowerSourceGroupAlgebraAugmentation
        (F := FreeGroup X) N n x = 0 := by
  rfl

/-- The finite-stage product ideal \(K_j I_j\) governing the Fox kernel criterion. -/
def foxAlgebraicStageGroupAlgebraMapKernelMulAugmentationIdeal :
    Ideal (foxAlgebraicStageSourceGroupAlgebra (X := X) N n) :=
  foxAlgebraicStageGroupAlgebraMapKernelIdeal (X := X) N n *
    foxAlgebraicStageSourceAugmentationIdeal (X := X) N n

/-- Coordinate vectors for finite-stage Fox derivatives. -/
abbrev foxAlgebraicStageCoordinateVector : Type u :=
  X → foxAlgebraicStageTargetGroupAlgebra (X := X) N n

/--
Finite-stage Fox semidirect target \(A^X \rtimes F/N\), whose left component stores the
derivative vector and whose right component stores the quotient word.
-/
structure FoxAlgebraicStageSemidirect where
  /-- The vector of finite-stage Fox-derivative coordinates. -/
  left : foxAlgebraicStageCoordinateVector (X := X) N n
  /-- The element of the finite-stage target quotient. -/
  right : foxAlgebraicStageTargetQuotient (X := X) N

namespace FoxAlgebraicStageSemidirect

omit [DecidableEq X] [N.Normal] in
/-- Extensionality for algebraic-stage semidirect elements. -/
@[ext]
theorem ext
    {a b : FoxAlgebraicStageSemidirect (X := X) N n}
    (hleft : a.left = b.left) (hright : a.right = b.right) : a = b := by
  cases a
  cases b
  simp_all

/-- The identity element of the finite-stage Fox semidirect product is \((0,1)\). -/
instance instOneFoxAlgebraicStageSemidirect : One (FoxAlgebraicStageSemidirect (X := X) N n) where
  one := ⟨0, 1⟩

/--
Multiplication in a finite Fox-stage semidirect product is defined by the finite-stage
coefficient action and quotient-group multiplication.
-/
instance instMulFoxAlgebraicStageSemidirect : Mul (FoxAlgebraicStageSemidirect (X := X) N n) where
  mul a b :=
    ⟨a.left +
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) a.right) • b.left,
      a.right * b.right⟩

/-- Inversion in the finite-stage Fox semidirect product. -/
instance instInvFoxAlgebraicStageSemidirect : Inv (FoxAlgebraicStageSemidirect (X := X) N n) where
  inv a :=
    ⟨-((MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N) a.right⁻¹) • a.left),
      a.right⁻¹⟩

omit [DecidableEq X] in
/-- The left component of the algebraic-stage semidirect identity is zero. -/
@[simp]
theorem one_left :
    (1 : FoxAlgebraicStageSemidirect (X := X) N n).left = 0 := rfl

omit [DecidableEq X] in
/-- The right component of the algebraic-stage semidirect identity is the group identity. -/
@[simp]
theorem one_right :
    (1 : FoxAlgebraicStageSemidirect (X := X) N n).right = 1 := rfl

omit [DecidableEq X] in
/-- Left-component formula for multiplication in the algebraic-stage semidirect product. -/
@[simp]
theorem mul_left
    (a b : FoxAlgebraicStageSemidirect (X := X) N n) :
    (a * b).left =
      a.left +
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) a.right) • b.left := rfl

omit [DecidableEq X] in
/-- Right-component formula for multiplication in the algebraic-stage semidirect product. -/
@[simp]
theorem mul_right
    (a b : FoxAlgebraicStageSemidirect (X := X) N n) :
    (a * b).right = a.right * b.right := rfl

omit [DecidableEq X] in
/-- Left-component formula for inversion in the algebraic-stage semidirect product. -/
@[simp]
theorem inv_left
    (a : FoxAlgebraicStageSemidirect (X := X) N n) :
    a⁻¹.left =
      -((MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N) a.right⁻¹) • a.left) := rfl

omit [DecidableEq X] in
/-- Right-component formula for inversion in the algebraic-stage semidirect product. -/
@[simp]
theorem inv_right
    (a : FoxAlgebraicStageSemidirect (X := X) N n) :
    a⁻¹.right = a.right⁻¹ := rfl

/-- Group structure on the finite-stage Fox semidirect product. -/
instance instGroupFoxAlgebraicStageSemidirect : Group (FoxAlgebraicStageSemidirect (X := X) N n)
    where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  mul_assoc a b c := by
    apply ext
    · funext i
      simp only [mul_left, MonoidAlgebra.of_apply, mul_right, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, add_assoc,
  smul_add, smul_smul, MonoidAlgebra.single_mul_single, mul_one]
    · simp only [mul_right, mul_assoc]
  one_mul a := by
    apply ext
    · funext i
      simp only [mul_left, one_left, one_right, Pi.smul_apply, zero_add]
      have hone :
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N) 1 :
              foxAlgebraicStageTargetGroupAlgebra (X := X) N n) = 1 := by
        exact map_one
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N))
      rw [hone, one_smul]
    · simp only [mul_right, one_right, one_mul]
  mul_one a := by
    apply ext
    · funext i
      simp only [mul_left, one_left, smul_zero, Pi.add_apply, Pi.zero_apply, add_zero]
    · simp only [mul_right, one_right, mul_one]
  inv_mul_cancel a := by
    apply ext
    · funext i
      simp only [mul_left, inv_left, MonoidAlgebra.of_apply, inv_right, Pi.add_apply,
          Pi.neg_apply, Pi.smul_apply,
  smul_eq_mul, neg_add_cancel, one_left, Pi.zero_apply]
    · simp only [mul_right, inv_right, inv_mul_cancel, one_right]

end FoxAlgebraicStageSemidirect


end

end FoxDifferential
