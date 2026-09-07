import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.System.Ring.Multiplicative

set_option autoImplicit false

/-!
# Fox differential: prime-power completed group algebra — system — ring — group like

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraOf`
  The canonical map sends a group element to its compatible family of prime-power finite-stage
  group-like elements.
- `primePowerCompletedGroupAlgebraProjection_one`
  The finite-stage projection sends \(1\) to \(1\).
- `primePowerCompletedGroupAlgebraProjection_mul`
  The finite-stage projection preserves multiplication.
- `primePowerCompletedGroupAlgebraProjection_of`
  The prime-power completed group-algebra projection sends a group-like element to its finite-stage
  group-like class.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < ℓ)] in
/-- The finite-stage projection sends \(1\) to \(1\). -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_one
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i
        (1 : PrimePowerCompletedGroupAlgebra ℓ G) = 1 := by
  change (1 : PrimePowerCompletedGroupAlgebraStage ℓ G i) = 1
  rfl

omit [Fact (0 < ℓ)] in
/-- The finite-stage projection preserves multiplication. -/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_mul
    (i : PrimePowerCompletedGroupAlgebraIndex G)
    (x y : PrimePowerCompletedGroupAlgebra ℓ G) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i (x * y) =
      primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x *
        primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i y := by
  change (show PrimePowerCompletedGroupAlgebraStage ℓ G i from (x * y).1 i) =
    (show PrimePowerCompletedGroupAlgebraStage ℓ G i from x.1 i) *
      (show PrimePowerCompletedGroupAlgebraStage ℓ G i from y.1 i)
  rfl

omit [Fact (0 < ℓ)] in
/--
The canonical map sends a group element to its compatible family of prime-power finite-stage
group-like elements.
-/
def primePowerCompletedGroupAlgebraOf
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (h : H) :
    PrimePowerCompletedGroupAlgebra ell H := by
  refine ⟨fun i => ?_, ?_⟩
  · exact
      MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
        (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2)
        (QuotientGroup.mk h)
  · intro i j hij
    let qj : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H j.2 :=
      QuotientGroup.mk h
    let qi : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2 :=
      QuotientGroup.mk h
    change primePowerCompletedGroupAlgebraTransition (ℓ := ell) (G := H) hij
        (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ j.1))
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H j.2)
          qj) =
      MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
        (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2)
        qi
    calc
      _ = MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2)
          ((OpenNormalSubgroupInClass.map
            (C := ProCGroups.FiniteGroupClass.allFinite) (G := H)
            (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) qj) :=
        primePowerCompletedGroupAlgebraTransition_of
          (ℓ := ell) (G := H) hij qj
      _ = MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2) qi := by
        apply congrArg
          (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
            (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2))
        rfl

/--
The prime-power completed group-algebra projection sends a group-like element to its
finite-stage group-like class.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraProjection_of
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (i : PrimePowerCompletedGroupAlgebraIndex H) (h : H) :
    primePowerCompletedGroupAlgebraProjection (ℓ := ell) (G := H) i
        (primePowerCompletedGroupAlgebraOf (ell := ell) h) =
      MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
        (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2)
        (QuotientGroup.mk h) := by
  rfl

/-- The canonical map to the prime-power completed group algebra sends \(1\) to \(1\). -/
@[simp]
theorem primePowerCompletedGroupAlgebraOf_one
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] :
    primePowerCompletedGroupAlgebraOf (ell := ell) (1 : H) = 1 := by
  apply (primePowerCompletedGroupAlgebraSystem ell H).ext
  intro i
  change primePowerCompletedGroupAlgebraProjection (ℓ := ell) (G := H) i
      (primePowerCompletedGroupAlgebraOf (ell := ell) (1 : H)) =
    primePowerCompletedGroupAlgebraProjection (ℓ := ell) (G := H) i
      (1 : PrimePowerCompletedGroupAlgebra ell H)
  rw [primePowerCompletedGroupAlgebraProjection_of,
    primePowerCompletedGroupAlgebraProjection_one]
  exact map_one
    (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
      (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2))

/-- The canonical map to the prime-power completed group algebra preserves multiplication. -/
@[simp]
theorem primePowerCompletedGroupAlgebraOf_mul
    (ell : Nat)
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] (h₁ h₂ : H) :
    primePowerCompletedGroupAlgebraOf (ell := ell) (h₁ * h₂) =
      primePowerCompletedGroupAlgebraOf (ell := ell) h₁ *
        primePowerCompletedGroupAlgebraOf (ell := ell) h₂ := by
  apply (primePowerCompletedGroupAlgebraSystem ell H).ext
  intro i
  change primePowerCompletedGroupAlgebraProjection (ℓ := ell) (G := H) i
      (primePowerCompletedGroupAlgebraOf (ell := ell) (h₁ * h₂)) =
    primePowerCompletedGroupAlgebraProjection (ℓ := ell) (G := H) i
      (primePowerCompletedGroupAlgebraOf (ell := ell) h₁ *
        primePowerCompletedGroupAlgebraOf (ell := ell) h₂)
  rw [primePowerCompletedGroupAlgebraProjection_of,
    primePowerCompletedGroupAlgebraProjection_mul,
    primePowerCompletedGroupAlgebraProjection_of,
    primePowerCompletedGroupAlgebraProjection_of]
  change
    (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
      (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2))
        (QuotientGroup.mk (h₁ * h₂)) =
      (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
        (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2))
          (QuotientGroup.mk h₁) *
        (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
          (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2))
            (QuotientGroup.mk h₂)
  rw [QuotientGroup.mk_mul]
  exact map_mul
    (MonoidAlgebra.of (ModNCompletedCoeff (ell ^ i.1))
      (_root_.CompletedGroupAlgebra.CompletedGroupAlgebraQuotient H i.2))
    (QuotientGroup.mk h₁) (QuotientGroup.mk h₂)

end

end FoxDifferential
