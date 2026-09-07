import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Coeff.AddCommGroup

set_option autoImplicit false

/-!
# Fox differential: coefficient rings — prime-power completed group algebra — coeff — ring

The principal declarations in this module are:

- `instCommRingPrimePowerCompletedCoeffStage`
  Each finite prime-power coefficient stage is a commutative ring.
- `instCommRingPrimePowerCompletedCoeffFamily`
  The family-level prime-power completed coefficient object is a commutative ring with operations
  computed coordinatewise.
- `coe_one_primePowerCompletedCoeff`
  The multiplicative identity in the prime-power completed coefficient ring is computed
  coordinatewise.
- `coe_mul_primePowerCompletedCoeff`
  Multiplication in the prime-power completed coefficient ring is computed coordinatewise.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

attribute [local instance] instAddCommGroupPrimePowerCompletedCoeffStage
attribute [local instance] instAddCommGroupPrimePowerCompletedCoeffFamily
attribute [local instance] instAddCommGroupPrimePowerCompletedCoeff

/--
The unit of the prime-power completed coefficient ring is the compatible family of finite-stage
units.
-/
instance instOnePrimePowerCompletedCoeff : One (PrimePowerCompletedCoeff ℓ G) where
  one := ⟨fun i => (1 : ZMod (ℓ ^ i.1)), by
    intro i j hij
    exact map_one
      (modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1))⟩

/--
Multiplication on the prime-power completed coefficient ring is defined coordinatewise through
finite-stage coefficient rings.
-/
instance instMulPrimePowerCompletedCoeff : Mul (PrimePowerCompletedCoeff ℓ G) where
  mul x y := ⟨fun i =>
      (show ZMod (ℓ ^ i.1) from x.1 i) * (show ZMod (ℓ ^ i.1) from y.1 i), by
    intro i j hij
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        ((show ZMod (ℓ ^ j.1) from x.1 j) * (show ZMod (ℓ ^ j.1) from y.1 j)) =
      (show ZMod (ℓ ^ i.1) from x.1 i) * (show ZMod (ℓ ^ i.1) from y.1 i)
    rw [map_mul]
    exact congrArg₂ HMul.hMul (x.2 i j hij) (y.2 i j hij)⟩

/--
Natural number casts in the prime-power completed coefficient ring are computed coordinatewise
from finite-stage natural number casts.
-/
instance instNatCastPrimePowerCompletedCoeff : NatCast (PrimePowerCompletedCoeff ℓ G) where
  natCast n := ⟨fun i => (n : ZMod (ℓ ^ i.1)), by
    intro i j hij
    exact map_natCast
      (modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)) n⟩

/--
Integer casts in the prime-power completed coefficient ring are computed coordinatewise from
finite-stage integer casts.
-/
instance instIntCastPrimePowerCompletedCoeff : IntCast (PrimePowerCompletedCoeff ℓ G) where
  intCast n := ⟨fun i => (n : ZMod (ℓ ^ i.1)), by
    intro i j hij
    exact map_intCast
      (modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)) n⟩

/-- Each finite prime-power coefficient stage is a commutative ring. -/
@[reducible]
private def instCommRingPrimePowerCompletedCoeffStage
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    CommRing ((primePowerCompletedCoeffSystem ℓ G).X i) := by
  dsimp [primePowerCompletedCoeffSystem]
  infer_instance
attribute [local instance] instCommRingPrimePowerCompletedCoeffStage

/--
The family-level prime-power completed coefficient object is a commutative ring with operations
computed coordinatewise.
-/
@[reducible]
private def instCommRingPrimePowerCompletedCoeffFamily :
    CommRing
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) :=
  inferInstance
attribute [local instance] instCommRingPrimePowerCompletedCoeffFamily

/--
Powers in the prime-power completed coefficient ring are computed at every finite coefficient
stage.
-/
instance instPowPrimePowerCompletedCoeff : Pow (PrimePowerCompletedCoeff ℓ G) ℕ where
  pow x n := ⟨fun i => (show ZMod (ℓ ^ i.1) from x.1 i) ^ n, by
    intro i j hij
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        ((show ZMod (ℓ ^ j.1) from x.1 j) ^ n) =
      (show ZMod (ℓ ^ i.1) from x.1 i) ^ n
    rw [map_pow]
    exact congrArg (fun t => t ^ n) (x.2 i j hij)⟩

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/--
The multiplicative identity in the prime-power completed coefficient ring is computed
coordinatewise.
-/
@[simp]
theorem coe_one_primePowerCompletedCoeff :
    ((1 : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) =
      (1 :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedCoeffSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- Multiplication in the prime-power completed coefficient ring is computed coordinatewise. -/
@[simp]
theorem coe_mul_primePowerCompletedCoeff
    (x y : PrimePowerCompletedCoeff ℓ G) :
    ((x * y : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) =
      (x * y :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedCoeffSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/--
Natural number casts in the prime-power completed coefficient ring are computed coordinatewise.
-/
@[simp]
theorem coe_natCast_primePowerCompletedCoeff
    (n : ℕ) :
    ((n : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) =
      (n :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedCoeffSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- Integer casts in the prime-power completed coefficient ring are computed coordinatewise. -/
@[simp]
theorem coe_intCast_primePowerCompletedCoeff
    (n : ℤ) :
    ((n : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) =
      (n :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedCoeffSystem ℓ G).X i) := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- Powers in the prime-power completed coefficient ring are computed coordinatewise. -/
@[simp]
theorem coe_pow_primePowerCompletedCoeff
    (x : PrimePowerCompletedCoeff ℓ G) (n : ℕ) :
    ((x ^ n : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) =
      (x ^ n :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedCoeffSystem ℓ G).X i) := by
  funext i
  rfl

/--
The prime-power completed coefficient object is a commutative ring with operations computed
coordinatewise.
-/
instance instCommRingPrimePowerCompletedCoeff :
    CommRing (PrimePowerCompletedCoeff ℓ G) :=
  Function.Injective.commRing
    (fun x : PrimePowerCompletedCoeff ℓ G =>
      (x :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedCoeffSystem ℓ G).X i))
    Subtype.val_injective
    (coe_zero_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_one_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_add_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_mul_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_neg_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_sub_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (fun n x => coe_nsmul_primePowerCompletedCoeff (ℓ := ℓ) (G := G) n x)
    (fun n x => coe_zsmul_primePowerCompletedCoeff (ℓ := ℓ) (G := G) n x)
    (fun x n => coe_pow_primePowerCompletedCoeff (ℓ := ℓ) (G := G) x n)
    (by
      intro n
      exact coe_natCast_primePowerCompletedCoeff (ℓ := ℓ) (G := G) n)
    (by
      intro z
      exact coe_intCast_primePowerCompletedCoeff (ℓ := ℓ) (G := G) z)

end

end FoxDifferential
