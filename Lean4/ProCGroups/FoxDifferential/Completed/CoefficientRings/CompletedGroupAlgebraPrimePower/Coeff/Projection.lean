import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Coeff.Ring

set_option autoImplicit false

/-!
# Fox differential: coefficient rings — prime-power completed group algebra — coeff — projection

The principal declarations in this module are:

- `primePowerCompletedCoeffProjection_one`
  The finite-stage projection sends \(1\) to \(1\).
- `primePowerCompletedCoeffProjection_mul`
  The finite-stage projection preserves multiplication.
- `primePowerCompletedCoeffProjection_natCast`
  The finite-stage projection preserves natural number casts.
- `primePowerCompletedCoeffProjection_intCast`
  The finite-stage projection preserves integer casts.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The finite-stage projection sends \(1\) to \(1\). -/
@[simp]
theorem primePowerCompletedCoeffProjection_one
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (1 : PrimePowerCompletedCoeff ℓ G) = 1 := by
  change (1 : ZMod (ℓ ^ i.1)) = 1
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The finite-stage projection preserves multiplication. -/
@[simp]
theorem primePowerCompletedCoeffProjection_mul
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedCoeff ℓ G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (x * y) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i x *
        primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i y := by
  change (show ZMod (ℓ ^ i.1) from (x * y).1 i) =
    (show ZMod (ℓ ^ i.1) from x.1 i) * (show ZMod (ℓ ^ i.1) from y.1 i)
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The finite-stage projection preserves natural number casts. -/
@[simp]
theorem primePowerCompletedCoeffProjection_natCast
    (i : PrimePowerCompletedGroupAlgebraIndex G) (n : ℕ) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (n : PrimePowerCompletedCoeff ℓ G) = n := by
  change (n : ZMod (ℓ ^ i.1)) = n
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The finite-stage projection preserves integer casts. -/
@[simp]
theorem primePowerCompletedCoeffProjection_intCast
    (i : PrimePowerCompletedGroupAlgebraIndex G) (n : ℤ) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (n : PrimePowerCompletedCoeff ℓ G) = n := by
  change (n : ZMod (ℓ ^ i.1)) = n
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The finite-stage projection sends \(0\) to \(0\). -/
@[simp]
theorem primePowerCompletedCoeffProjection_zero
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
        (0 : PrimePowerCompletedCoeff ℓ G) = 0 := by
  change (0 : ZMod (ℓ ^ i.1)) = 0
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The prime-power coefficient projection preserves addition. -/
@[simp]
theorem primePowerCompletedCoeffProjection_add
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedCoeff ℓ G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (x + y) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i x +
        primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i y := by
  change (show ZMod (ℓ ^ i.1) from (x + y).1 i) =
    (show ZMod (ℓ ^ i.1) from x.1 i) + (show ZMod (ℓ ^ i.1) from y.1 i)
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The prime-power coefficient projection preserves negation. -/
@[simp]
theorem primePowerCompletedCoeffProjection_neg
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x : PrimePowerCompletedCoeff ℓ G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (-x) =
      -primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i x := by
  change (show ZMod (ℓ ^ i.1) from (-x).1 i) =
    -(show ZMod (ℓ ^ i.1) from x.1 i)
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/-- The prime-power coefficient projection preserves subtraction. -/
@[simp]
theorem primePowerCompletedCoeffProjection_sub
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedCoeff ℓ G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i (x - y) =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i x -
        primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i y := by
  change (show ZMod (ℓ ^ i.1) from (x - y).1 i) =
    (show ZMod (ℓ ^ i.1) from x.1 i) - (show ZMod (ℓ ^ i.1) from y.1 i)
  rfl

omit [Fact (0 < ℓ)] [IsTopologicalGroup G] in
/--
Coefficient projections with the same prime-power exponent do not depend on the finite-quotient
component of the group-algebra index. The second index component synchronizes coefficients and
group-algebra stages in one inverse system.
-/
theorem primePowerCompletedCoeffProjection_eq_of_same_exponent
    (a : ℕ) (U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G)
    (z : PrimePowerCompletedCoeff ℓ G) :
    primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) (a, U) z =
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) (a, V) z := by
  let T : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G :=
      _root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G
  let hTU : (a, T) ≤ (a, U) :=
    ⟨le_rfl, _root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex_le (G := G) U⟩
  let hTV : (a, T) ≤ (a, V) :=
    ⟨le_rfl, _root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex_le (G := G) V⟩
  have hTU_coeff :
      modNCompletedCoeffMap
          (n := ℓ ^ a) (m := ℓ ^ a)
          (primePow_dvd_primePow (ℓ := ℓ) hTU.1) = RingHom.id _ := by
    have hproof :
        primePow_dvd_primePow (ℓ := ℓ) hTU.1 = (dvd_rfl : ℓ ^ a ∣ ℓ ^ a) :=
      Subsingleton.elim _ _
    rw [hproof]
    exact modNCompletedCoeffMap_rfl (n := ℓ ^ a)
  have hTV_coeff :
      modNCompletedCoeffMap
          (n := ℓ ^ a) (m := ℓ ^ a)
          (primePow_dvd_primePow (ℓ := ℓ) hTV.1) = RingHom.id _ := by
    have hproof :
        primePow_dvd_primePow (ℓ := ℓ) hTV.1 = (dvd_rfl : ℓ ^ a ∣ ℓ ^ a) :=
      Subsingleton.elim _ _
    rw [hproof]
    exact modNCompletedCoeffMap_rfl (n := ℓ ^ a)
  have hU := z.2 (a, T) (a, U) hTU
  have hV := z.2 (a, T) (a, V) hTV
  have hU' :
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) (a, U) z =
        primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) (a, T) z := by
    change (show ZMod (ℓ ^ a) from z.1 (a, U)) =
      (show ZMod (ℓ ^ a) from z.1 (a, T))
    change
      (modNCompletedCoeffMap
          (n := ℓ ^ a) (m := ℓ ^ a)
          (primePow_dvd_primePow (ℓ := ℓ) hTU.1))
          (show ZMod (ℓ ^ a) from z.1 (a, U)) =
        (show ZMod (ℓ ^ a) from z.1 (a, T)) at hU
    rw [hTU_coeff, RingHom.id_apply] at hU
    exact hU
  have hV' :
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) (a, V) z =
        primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) (a, T) z := by
    change (show ZMod (ℓ ^ a) from z.1 (a, V)) =
      (show ZMod (ℓ ^ a) from z.1 (a, T))
    change
      (modNCompletedCoeffMap
          (n := ℓ ^ a) (m := ℓ ^ a)
          (primePow_dvd_primePow (ℓ := ℓ) hTV.1))
          (show ZMod (ℓ ^ a) from z.1 (a, V)) =
        (show ZMod (ℓ ^ a) from z.1 (a, T)) at hV
    rw [hTV_coeff, RingHom.id_apply] at hV
    exact hV
  exact hU'.trans hV'.symm

end

end FoxDifferential
