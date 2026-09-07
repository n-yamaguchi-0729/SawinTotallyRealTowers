import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Coeff.System

set_option autoImplicit false

/-!
# Fox differential: coefficient rings — prime-power completed group algebra — coeff — add comm group

The principal declarations in this module are:

- `instAddCommGroupPrimePowerCompletedCoeffStage`
  Each coefficient stage \(\mathbb{Z}/\ell^i\mathbb{Z}\) carries its standard additive group.
- `instAddCommGroupPrimePowerCompletedCoeffFamily`
  The dependent family of prime-power coefficient stages carries the pointwise additive commutative
  group structure.
- `coe_zero_primePowerCompletedCoeff`
  The inclusion of the prime-power completed coefficient ring preserves zero.
- `coe_add_primePowerCompletedCoeff`
  The inclusion of the prime-power completed coefficient ring preserves addition.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
The zero element of the prime-power completed coefficient ring is the compatible family of
finite-stage zero elements.
-/
instance instZeroPrimePowerCompletedCoeff : Zero (PrimePowerCompletedCoeff ℓ G) where
  zero := ⟨fun i => (0 : ZMod (ℓ ^ i.1)), by
    intro i j hij
    exact map_zero
      (modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1))⟩

/--
Addition in the prime-power completed coefficient ring is defined coordinatewise through
finite-stage coefficient additions.
-/
instance instAddPrimePowerCompletedCoeff : Add (PrimePowerCompletedCoeff ℓ G) where
  add x y := ⟨fun i =>
      (show ZMod (ℓ ^ i.1) from x.1 i) + (show ZMod (ℓ ^ i.1) from y.1 i), by
    intro i j hij
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        ((show ZMod (ℓ ^ j.1) from x.1 j) + (show ZMod (ℓ ^ j.1) from y.1 j)) =
      (show ZMod (ℓ ^ i.1) from x.1 i) + (show ZMod (ℓ ^ i.1) from y.1 i)
    rw [map_add]
    exact congrArg₂ HAdd.hAdd (x.2 i j hij) (y.2 i j hij)⟩

/--
Coordinatewise zero and addition on the prime-power completed coefficient ring satisfy the left
and right zero laws.
-/
instance instAddZeroClassPrimePowerCompletedCoeff :
    AddZeroClass (PrimePowerCompletedCoeff ℓ G) where
  zero := 0
  add := (· + ·)
  zero_add x := by
    apply Subtype.ext
    funext i
    change (0 : ZMod (ℓ ^ i.1)) + (show ZMod (ℓ ^ i.1) from x.1 i) =
      (show ZMod (ℓ ^ i.1) from x.1 i)
    exact zero_add (show ZMod (ℓ ^ i.1) from x.1 i)
  add_zero x := by
    apply Subtype.ext
    funext i
    change (show ZMod (ℓ ^ i.1) from x.1 i) + (0 : ZMod (ℓ ^ i.1)) =
      (show ZMod (ℓ ^ i.1) from x.1 i)
    exact add_zero (show ZMod (ℓ ^ i.1) from x.1 i)

/--
Negation on the prime-power completed coefficient ring is defined coordinatewise through
finite-stage coefficient negations.
-/
instance instNegPrimePowerCompletedCoeff : Neg (PrimePowerCompletedCoeff ℓ G) where
  neg x := ⟨fun i => -(show ZMod (ℓ ^ i.1) from x.1 i), by
    intro i j hij
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        (-(show ZMod (ℓ ^ j.1) from x.1 j)) =
      -(show ZMod (ℓ ^ i.1) from x.1 i)
    rw [map_neg]
    exact congrArg Neg.neg (x.2 i j hij)⟩

/--
Subtraction in the prime-power completed coefficient ring is defined coordinatewise through
finite-stage coefficient-ring subtractions.
-/
instance instSubPrimePowerCompletedCoeff : Sub (PrimePowerCompletedCoeff ℓ G) where
  sub x y := ⟨fun i =>
      (show ZMod (ℓ ^ i.1) from x.1 i) - (show ZMod (ℓ ^ i.1) from y.1 i), by
    intro i j hij
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        ((show ZMod (ℓ ^ j.1) from x.1 j) - (show ZMod (ℓ ^ j.1) from y.1 j)) =
      (show ZMod (ℓ ^ i.1) from x.1 i) - (show ZMod (ℓ ^ i.1) from y.1 i)
    rw [map_sub]
    exact congrArg₂ HSub.hSub (x.2 i j hij) (y.2 i j hij)⟩

/--
The prime-power completed coefficient ring carries natural-number scalar multiplication
coordinatewise at every finite coefficient stage.
-/
instance instSMulNatPrimePowerCompletedCoeff : SMul ℕ (PrimePowerCompletedCoeff ℓ G) where
  smul m x := ⟨fun i => m • (show ZMod (ℓ ^ i.1) from x.1 i), by
    intro i j hij
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        (m • (show ZMod (ℓ ^ j.1) from x.1 j)) =
      m • (show ZMod (ℓ ^ i.1) from x.1 i)
    rw [map_nsmul]
    exact congrArg (m • ·) (x.2 i j hij)⟩

/--
The prime-power completed coefficient ring carries integer scalar multiplication coordinatewise
at every finite coefficient stage.
-/
instance instSMulIntPrimePowerCompletedCoeff : SMul ℤ (PrimePowerCompletedCoeff ℓ G) where
  smul m x := ⟨fun i => m • (show ZMod (ℓ ^ i.1) from x.1 i), by
    intro i j hij
    change modNCompletedCoeffMap
        (n := ℓ ^ i.1) (m := ℓ ^ j.1)
        (primePow_dvd_primePow (ℓ := ℓ) hij.1)
        (m • (show ZMod (ℓ ^ j.1) from x.1 j)) =
      m • (show ZMod (ℓ ^ i.1) from x.1 i)
    rw [map_zsmul]
    exact congrArg (m • ·) (x.2 i j hij)⟩

/-- Each coefficient stage \(\mathbb{Z}/\ell^i\mathbb{Z}\) carries its standard additive group. -/
@[reducible] def instAddCommGroupPrimePowerCompletedCoeffStage
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    AddCommGroup ((primePowerCompletedCoeffSystem ℓ G).X i) := by
  dsimp [primePowerCompletedCoeffSystem]
  infer_instance

attribute [local instance] instAddCommGroupPrimePowerCompletedCoeffStage

/--
The dependent family of prime-power coefficient stages carries the pointwise additive
commutative group structure.
-/
@[reducible] def instAddCommGroupPrimePowerCompletedCoeffFamily :
    AddCommGroup
      ((i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) :=
  inferInstance

attribute [local instance] instAddCommGroupPrimePowerCompletedCoeffFamily

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The inclusion of the prime-power completed coefficient ring preserves zero. -/
@[simp]
theorem coe_zero_primePowerCompletedCoeff :
    ((0 : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) = 0 := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The inclusion of the prime-power completed coefficient ring preserves addition. -/
@[simp]
theorem coe_add_primePowerCompletedCoeff
    (x y : PrimePowerCompletedCoeff ℓ G) :
    ((x + y : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) = x + y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The inclusion of the prime-power completed coefficient ring preserves negation. -/
@[simp]
theorem coe_neg_primePowerCompletedCoeff
    (x : PrimePowerCompletedCoeff ℓ G) :
    ((-x : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) = -x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The inclusion of the prime-power completed coefficient ring preserves subtraction. -/
@[simp]
theorem coe_sub_primePowerCompletedCoeff
    (x y : PrimePowerCompletedCoeff ℓ G) :
    ((x - y : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) = x - y := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/--
The inclusion of the prime-power completed coefficient ring preserves natural-number scalar
multiplication.
-/
@[simp]
theorem coe_nsmul_primePowerCompletedCoeff
    (m : ℕ) (x : PrimePowerCompletedCoeff ℓ G) :
    ((m • x : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) = m • x := by
  funext i
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/--
The inclusion of the prime-power completed coefficient ring preserves integer scalar
multiplication.
-/
@[simp]
theorem coe_zsmul_primePowerCompletedCoeff
    (m : ℤ) (x : PrimePowerCompletedCoeff ℓ G) :
    ((m • x : PrimePowerCompletedCoeff ℓ G) :
      (i : PrimePowerCompletedGroupAlgebraIndex G) →
        (primePowerCompletedCoeffSystem ℓ G).X i) = m • x := by
  funext i
  rfl

/--
The prime-power completed coefficient ring inherits an additive commutative group structure from
its injective inclusion into the family of coefficient stages.
-/
@[reducible] def instAddCommGroupPrimePowerCompletedCoeff :
    AddCommGroup (PrimePowerCompletedCoeff ℓ G) :=
  Function.Injective.addCommGroup
    (fun x : PrimePowerCompletedCoeff ℓ G =>
      (x :
        (i : PrimePowerCompletedGroupAlgebraIndex G) →
          (primePowerCompletedCoeffSystem ℓ G).X i))
    Subtype.val_injective
    (coe_zero_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_add_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_neg_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (coe_sub_primePowerCompletedCoeff (ℓ := ℓ) (G := G))
    (fun x m => coe_nsmul_primePowerCompletedCoeff (ℓ := ℓ) (G := G) m x)
    (fun x m => coe_zsmul_primePowerCompletedCoeff (ℓ := ℓ) (G := G) m x)

attribute [local instance] instAddCommGroupPrimePowerCompletedCoeff

end

end FoxDifferential
