import ProCGroups.FoxDifferential.Completed.FiniteStage.CoeffMap.Target

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — coeff map — source

The principal declarations in this module are:

- `foxAlgebraicStageSameSourceGroupAlgebraCoeffMap`
  Coefficient-reduction map on a fixed finite Fox source quotient.
- `foxAlgebraicStagePowerSourceQuotientMap`
  Source quotient transition \(F/[N,N]N^m \to F/[N,N]N^n\) induced by \(n \mid m\).
- `foxAlgebraicStageSameSourceGroupAlgebraCoeffMap_of`
  Fixed-source coefficient reduction evaluated on a quotient basis element.
- `foxAlgebraicStagePowerSourceQuotientMap_mk`
  Evaluation of the source quotient transition on a representative.
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
/-- Coefficient-reduction map on a fixed finite Fox source quotient. -/
def foxAlgebraicStageSameSourceGroupAlgebraCoeffMap
    (N : Subgroup (FreeGroup X)) (k : ℕ) (hnm : n₀ ∣ m₀) :
    MonoidAlgebra (ModNCompletedCoeff m₀)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N k) →+*
      MonoidAlgebra (ModNCompletedCoeff n₀)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N k) :=
  modNCompletedGroupRingCoeffMap
    (n := n₀) (m := m₀)
    (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N k) hnm

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Fixed-source coefficient reduction evaluated on a quotient basis element. -/
@[simp]
theorem foxAlgebraicStageSameSourceGroupAlgebraCoeffMap_of
    (N : Subgroup (FreeGroup X)) (k : ℕ) (hnm : n₀ ∣ m₀)
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N k) :
    foxAlgebraicStageSameSourceGroupAlgebraCoeffMap (X := X) N k hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m₀)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N k) q) =
      MonoidAlgebra.of (ModNCompletedCoeff n₀)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N k) q := by
  simpa [foxAlgebraicStageSameSourceGroupAlgebraCoeffMap] using
    (modNCompletedGroupRingCoeffMap_of
      (n := n₀) (m := m₀)
      (H := FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N k)
      hnm q)

omit [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Source quotient transition \(F/[N,N]N^m \to F/[N,N]N^n\) induced by \(n \mid m\). -/
def foxAlgebraicStagePowerSourceQuotientMap
    (N : Subgroup (FreeGroup X)) (hnm : n₀ ∣ m₀) :
    FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀ →*
      FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n₀ :=
  QuotientGroup.map _ _ (MonoidHom.id (FreeGroup X))
    (foxCommutatorPowerSubgroup_dvd (X := X) N hnm)

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Evaluation of the source quotient transition on a representative. -/
@[simp]
theorem foxAlgebraicStagePowerSourceQuotientMap_mk
    (N : Subgroup (FreeGroup X)) (hnm : n₀ ∣ m₀) (w : FreeGroup X) :
    foxAlgebraicStagePowerSourceQuotientMap (X := X) N hnm
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) w) =
      QuotientGroup.mk'
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N n₀) w := by
  rfl

/--
Combined source transition on finite Fox source group algebras: quotient transition plus
coefficient reduction.
-/
def foxAlgebraicStagePowerSourceGroupAlgebraMap
    (N : Subgroup (FreeGroup X)) (hnm : n₀ ∣ m₀) :
    MonoidAlgebra (ModNCompletedCoeff m₀)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) →+*
      MonoidAlgebra (ModNCompletedCoeff n₀)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n₀) :=
  (foxAlgebraicStageSameSourceGroupAlgebraCoeffMap (X := X) N n₀ hnm).comp
    (MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff m₀)
      (foxAlgebraicStagePowerSourceQuotientMap (X := X) N hnm))

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- The finite Fox source group-algebra transition evaluated on a represented word. -/
@[simp 900]
theorem foxAlgebraicStagePowerSourceGroupAlgebraMap_of
    (N : Subgroup (FreeGroup X)) (hnm : n₀ ∣ m₀) (w : FreeGroup X) :
    foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm
        (MonoidAlgebra.of (ModNCompletedCoeff m₀)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀)
          (QuotientGroup.mk'
            (foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) w)) =
      MonoidAlgebra.of (ModNCompletedCoeff n₀)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n₀)
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N n₀) w) := by
  rw [foxAlgebraicStagePowerSourceGroupAlgebraMap, RingHom.comp_apply]
  have hmap :
      MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff m₀)
          (foxAlgebraicStagePowerSourceQuotientMap (X := X) N hnm)
          (MonoidAlgebra.of (ModNCompletedCoeff m₀)
            (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀)
            (QuotientGroup.mk'
              (foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) w)) =
        MonoidAlgebra.of (ModNCompletedCoeff m₀)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n₀)
          (QuotientGroup.mk'
            (foxCommutatorPowerSubgroup (F := FreeGroup X) N n₀) w) := by
    change
      MonoidAlgebra.mapDomain
          (foxAlgebraicStagePowerSourceQuotientMap (X := X) N hnm)
          (MonoidAlgebra.single
            (QuotientGroup.mk'
              (foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) w) 1) =
        MonoidAlgebra.single
          (QuotientGroup.mk'
            (foxCommutatorPowerSubgroup (F := FreeGroup X) N n₀) w) 1
    rw [MonoidAlgebra.mapDomain_single,
      foxAlgebraicStagePowerSourceQuotientMap_mk]
  rw [hmap, foxAlgebraicStageSameSourceGroupAlgebraCoeffMap_of]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/--
On a single source-stage basis coefficient, the finite source transition sends the group
coordinate by the quotient map and reduces the coefficient.
-/
@[simp]
theorem foxAlgebraicStagePowerSourceGroupAlgebraMap_single_apply
    (N : Subgroup (FreeGroup X)) (hnm : n₀ ∣ m₀)
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀)
    (a : ModNCompletedCoeff m₀) :
    foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single
        (foxAlgebraicStagePowerSourceQuotientMap (X := X) N hnm q)
        (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a) := by
  let : Algebra (ModNCompletedCoeff m₀) (ModNCompletedCoeff n₀) :=
    ZMod.algebra' (R := ModNCompletedCoeff n₀) (m := n₀) (n := m₀) hnm
  have hcoeff :
      algebraMap (ModNCompletedCoeff m₀) (ModNCompletedCoeff n₀) a =
        modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a := by
    rfl
  rw [foxAlgebraicStagePowerSourceGroupAlgebraMap, RingHom.comp_apply]
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
  change
    MonoidAlgebra.lift (ModNCompletedCoeff m₀)
        (ModNCompletedGroupRing n₀
          (FreeGroup X ⧸
            foxCommutatorPowerSubgroup (F := FreeGroup X) N n₀))
        (FreeGroup X ⧸
          foxCommutatorPowerSubgroup (F := FreeGroup X) N n₀)
        (MonoidAlgebra.of (ModNCompletedCoeff n₀)
          (FreeGroup X ⧸
            foxCommutatorPowerSubgroup (F := FreeGroup X) N n₀))
        (MonoidAlgebra.single
          (foxAlgebraicStagePowerSourceQuotientMap (X := X) N hnm q) a) =
      MonoidAlgebra.single
        (foxAlgebraicStagePowerSourceQuotientMap (X := X) N hnm q)
        (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a)
  rw [MonoidAlgebra.lift_single]
  change
    algebraMap (ModNCompletedCoeff m₀) (ModNCompletedCoeff n₀) a •
        MonoidAlgebra.of (ModNCompletedCoeff n₀)
          (FreeGroup X ⧸
            foxCommutatorPowerSubgroup (F := FreeGroup X) N n₀)
          (foxAlgebraicStagePowerSourceQuotientMap (X := X) N hnm q) =
      MonoidAlgebra.single
        (foxAlgebraicStagePowerSourceQuotientMap (X := X) N hnm q)
        (modNCompletedCoeffMap (n := n₀) (m := m₀) hnm a)
  rw [hcoeff, MonoidAlgebra.smul_of]

omit [DecidableEq X] [Fact (0 < n₀)] in
/--
The finite Fox source group-algebra transition is the identity map when the modulus is
unchanged.
-/
@[simp 900]
theorem foxAlgebraicStagePowerSourceGroupAlgebraMap_rfl
    (N : Subgroup (FreeGroup X)) :
    foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) (n₀ := n₀) (m₀ := n₀) N
        dvd_rfl =
      RingHom.id _ := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) (n₀ := n₀) (m₀ := n₀) N
          dvd_rfl x = x)
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N n₀) q with ⟨w, rfl⟩
    rw [foxAlgebraicStagePowerSourceGroupAlgebraMap_of]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, hx]
    simp only [foxAlgebraicStagePowerSourceGroupAlgebraMap,
        foxAlgebraicStageSameSourceGroupAlgebraCoeffMap,
  modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe, MonoidAlgebra.mapDomainRingHom,
  foxAlgebraicStagePowerSourceQuotientMap, map_intCast]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/-- Finite Fox source group-algebra transitions compose along divisibility. -/
@[simp 900]
theorem foxAlgebraicStagePowerSourceGroupAlgebraMap_comp
    {k₀ : ℕ}
    (N : Subgroup (FreeGroup X)) (hnm : n₀ ∣ m₀) (hmk : m₀ ∣ k₀) :
    (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm).comp
        (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hmk) =
      foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N (dvd_trans hnm hmk) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm).comp
          (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hmk)) x =
        foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N (dvd_trans hnm hmk) x)
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N k₀) q with ⟨w, rfl⟩
    rw [RingHom.comp_apply, foxAlgebraicStagePowerSourceGroupAlgebraMap_of,
      foxAlgebraicStagePowerSourceGroupAlgebraMap_of,
          foxAlgebraicStagePowerSourceGroupAlgebraMap_of]
  · intro x y hx hy
    simp only [RingHom.map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [foxAlgebraicStagePowerSourceGroupAlgebraMap,
        foxAlgebraicStageSameSourceGroupAlgebraCoeffMap,
  modNCompletedGroupRingCoeffMap, AlgHom.toRingHom_eq_coe, MonoidAlgebra.mapDomainRingHom,
  foxAlgebraicStagePowerSourceQuotientMap, map_intCast, RingHom.coe_comp, RingHom.coe_coe,
      RingHom.coe_mk,
  MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < m₀)] in
/--
The natural finite-stage map \(((\mathbb{Z}/m\mathbb{Z})[F/[N,N]N^m]) \to
((\mathbb{Z}/m\mathbb{Z})[F/N])\) commutes with coefficient/source reduction to a divisor \(n
\mid m\).
-/
theorem foxAlgebraicStageGroupAlgebraMap_powerSourceGroupAlgebraMap
    (N : Subgroup (FreeGroup X)) [N.Normal] (hnm : n₀ ∣ m₀)
    (x : foxAlgebraicStageSourceGroupAlgebra (X := X) N m₀) :
    foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
        (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N m₀ x) =
      foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n₀
        (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm x) := by
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm
          (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N m₀ x) =
        foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n₀
          (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm x))
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N m₀) q with ⟨w, rfl⟩
    rw [foxCommutatorPowerGroupAlgebraMap_of,
      foxAlgebraicStageTargetGroupAlgebraCoeffMap_of,
      foxAlgebraicStagePowerSourceGroupAlgebraMap_of,
      foxCommutatorPowerGroupAlgebraMap_of]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def]
    change
      ((foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm).comp
          (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N m₀))
          (algebraMap (ModNCompletedCoeff m₀)
              (foxAlgebraicStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀) * x) =
        ((foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n₀).comp
          (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm))
          (algebraMap (ModNCompletedCoeff m₀)
              (foxAlgebraicStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀) * x)
    rw [RingHom.map_mul, RingHom.map_mul]
    have hx' :
        ((foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm).comp
            (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N m₀)) x =
          ((foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n₀).comp
            (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm)) x := by
      simpa [RingHom.comp_apply] using hx
    rw [hx']
    have hcoeff :
        ((foxAlgebraicStageTargetGroupAlgebraCoeffMap (X := X) N hnm).comp
            (foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N m₀))
            (algebraMap (ModNCompletedCoeff m₀)
              (foxAlgebraicStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀)) =
          ((foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n₀).comp
            (foxAlgebraicStagePowerSourceGroupAlgebraMap (X := X) N hnm))
            (algebraMap (ModNCompletedCoeff m₀)
              (foxAlgebraicStageSourceGroupAlgebra (X := X) N m₀)
              (t : ModNCompletedCoeff m₀)) := by
      simp only [foxAlgebraicStageTargetGroupAlgebraCoeffMap, modNCompletedGroupRingCoeffMap,
          AlgHom.toRingHom_eq_coe,
  foxCommutatorPowerGroupAlgebraMap, MonoidAlgebra.mapDomainRingHom, map_intCast,
  foxAlgebraicStagePowerSourceGroupAlgebraMap, foxAlgebraicStageSameSourceGroupAlgebraCoeffMap,
  foxAlgebraicStagePowerSourceQuotientMap]
    rw [hcoeff]




end

end FoxDifferential
