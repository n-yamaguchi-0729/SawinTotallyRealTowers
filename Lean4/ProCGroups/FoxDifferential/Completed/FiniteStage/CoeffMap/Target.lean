import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Source

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — coeff map — target

The principal declarations in this module are:

- `foxAlgebraicStageTargetGroupAlgebraCoeffMap`
  Coefficient-reduction map on finite-stage target group algebras for a divisor \(n \mid m\).
- `foxAlgebraicStageTargetGroupAlgebraCoeffMap_of`
  Evaluation of target coefficient reduction on a represented quotient word.
- `foxAlgebraicStageTargetGroupAlgebraCoeffMap_of_quotient`
  Evaluation of target coefficient reduction on a quotient basis element.
- `foxAlgebraicStageTargetGroupAlgebraCoeffMap_single_apply`
  The finite-stage target coefficient map sends a singleton to the singleton with reduced
  coefficient and unchanged support.
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


variable {n₀ m₀ : ℕ} [Fact (0 < n₀)] [Fact (0 < m₀)]
/-- Coefficient-reduction map on finite-stage target group algebras for a divisor \(n \mid m\). -/
def foxAlgebraicStageTargetGroupAlgebraCoeffMap
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) :
    foxAlgebraicStageTargetGroupAlgebra (X := X) N m₀ →+*
      foxAlgebraicStageTargetGroupAlgebra (X := X) N n₀ :=
  modNCompletedGroupRingCoeffMap
    (n := n₀) (m := m₀) (foxAlgebraicStageTargetQuotient (X := X) N) hnm

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Evaluation of target coefficient reduction on a represented quotient word. -/
@[simp]
theorem foxAlgebraicStageTargetGroupAlgebraCoeffMap_of
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) (w : FreeGroup X) :
    foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m₀)
          (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w)) =
      MonoidAlgebra.of (ModNCompletedCoeff n₀)
        (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w) := by
  simpa [foxAlgebraicStageTargetGroupAlgebraCoeffMap] using
    (modNCompletedGroupRingCoeffMap_of
      (n := n₀) (m := m₀)
      (H := foxAlgebraicStageTargetQuotient (X := X) N) hnm (QuotientGroup.mk' N w))

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Evaluation of target coefficient reduction on a quotient basis element. -/
@[simp]
theorem foxAlgebraicStageTargetGroupAlgebraCoeffMap_of_quotient
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (q : foxAlgebraicStageTargetQuotient (X := X) N) :
    foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m₀)
          (foxAlgebraicStageTargetQuotient (X := X) N) q) =
      MonoidAlgebra.of (ModNCompletedCoeff n₀)
        (foxAlgebraicStageTargetQuotient (X := X) N) q := by
  rcases QuotientGroup.mk'_surjective N q with ⟨w, rfl⟩
  exact foxAlgebraicStageTargetGroupAlgebraCoeffMap_of (X := X) N hnm w

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/--
The finite-stage target coefficient map sends a singleton to the singleton with reduced coefficient
and unchanged support.
-/
@[simp]
theorem foxAlgebraicStageTargetGroupAlgebraCoeffMap_single_apply
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (q : foxAlgebraicStageTargetQuotient (X := X) N)
    (a : ModNCompletedCoeff m₀) :
    foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single q (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a) := by
  let : Algebra (ModNCompletedCoeff m₀) (ModNCompletedCoeff n₀) :=
    ZMod.algebra' (R := ModNCompletedCoeff n₀) (m := n₀) (n := m₀) hnm
  have hcoeff :
      algebraMap (ModNCompletedCoeff m₀) (ModNCompletedCoeff n₀) a =
        modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a := by
    rfl
  change
    MonoidAlgebra.lift (ModNCompletedCoeff m₀)
        (ModNCompletedGroupRing n₀
          (foxAlgebraicStageTargetQuotient (X := X) N))
        (foxAlgebraicStageTargetQuotient (X := X) N)
        (MonoidAlgebra.of (ModNCompletedCoeff n₀)
          (foxAlgebraicStageTargetQuotient (X := X) N))
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single q
        (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a)
  rw [MonoidAlgebra.lift_single]
  change
    algebraMap (ModNCompletedCoeff m₀) (ModNCompletedCoeff n₀) a •
        MonoidAlgebra.of (ModNCompletedCoeff n₀)
          (foxAlgebraicStageTargetQuotient (X := X) N) q =
      MonoidAlgebra.single q
        (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a)
  rw [hcoeff, MonoidAlgebra.smul_of]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Target coefficient reduction is the native monoid-algebra coefficient map. -/
theorem foxAlgebraicStageTargetGroupAlgebraCoeffMap_eq_mapRange
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) :
    foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm =
      MonoidAlgebra.mapRingHom
        (foxAlgebraicStageTargetQuotient (X := X) N)
        (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm x =
        MonoidAlgebra.mapRingHom
          (foxAlgebraicStageTargetQuotient (X := X) N)
          (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm) x)
    x ?_ ?_ ?_
  · intro q
    rw [foxAlgebraicStageTargetGroupAlgebraCoeffMap_of_quotient]
    simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one]
  · intro y z hy hz
    simp only [map_add, hy, hz]
  · intro a y hy
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, map_mul, map_mul, hy]
    simp only [map_intCast]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/--
The finite-stage target coefficient map changes each coefficient while retaining its target-quotient
support.
-/
@[simp]
theorem foxAlgebraicStageTargetGroupAlgebraCoeffMap_apply
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (x : foxAlgebraicStageTargetGroupAlgebra (X := X) N m₀)
    (q : foxAlgebraicStageTargetQuotient (X := X) N) :
    (foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm x).coeff q =
      modNCompletedCoeffMap (n := n₀) (m := m₀) hnm (x.coeff q) := by
  rw [foxAlgebraicStageTargetGroupAlgebraCoeffMap_eq_mapRange]
  exact MonoidAlgebra.coeff_mapRingHom
    (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm) x q

omit [DecidableEq X] [Fact (0 < n₀)] in
/-- Target coefficient reduction is the identity map when the modulus is unchanged. -/
@[simp]
theorem foxAlgebraicStageTargetGroupAlgebraCoeffMap_rfl
    (N : Subgroup (FreeGroup X)) [N.Normal] :
    foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) (n₀ := n₀) (m₀ := n₀) N dvd_rfl =
      RingHom.id _ := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) (n₀ := n₀) (m₀ := n₀) N
          dvd_rfl x = x)
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective N q with ⟨w, rfl⟩
    rw [foxAlgebraicStageTargetGroupAlgebraCoeffMap_of]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, hx]
    simp only [foxAlgebraicStageTargetGroupAlgebraCoeffMap, modNCompletedGroupRingCoeffMap,
        AlgHom.toRingHom_eq_coe,
  map_intCast]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Target coefficient reductions compose along divisibility. -/
@[simp 900]
theorem foxAlgebraicStageTargetGroupAlgebraCoeffMap_comp
    {k₀ : ℕ}
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀) (hmk : m₀ ∣ k₀) :
    (foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm).comp
        (foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hmk) =
      foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N (dvd_trans hnm hmk) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm).comp
          (foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hmk)) x =
        foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N (dvd_trans hnm hmk) x)
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective N q with ⟨w, rfl⟩
    rw [RingHom.comp_apply, foxAlgebraicStageTargetGroupAlgebraCoeffMap_of,
      foxAlgebraicStageTargetGroupAlgebraCoeffMap_of,
          foxAlgebraicStageTargetGroupAlgebraCoeffMap_of]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [foxAlgebraicStageTargetGroupAlgebraCoeffMap, modNCompletedGroupRingCoeffMap,
        AlgHom.toRingHom_eq_coe,
  map_intCast, RingHom.coe_coe]




end

end FoxDifferential
