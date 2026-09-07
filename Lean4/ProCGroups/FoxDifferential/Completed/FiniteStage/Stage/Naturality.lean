import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Fundamental.Formula

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — stage — naturality

The principal declarations in this module are:

- `foxAlgebraicStageTargetQuotientMap`
  Natural quotient map \(F/N \to F/M\) induced by an inclusion \(N \le M\).
- `foxAlgebraicStageTargetGroupAlgebraMap`
  Group-algebra map on finite-stage targets induced by \(N \le M\).
- `foxCommutatorPowerRelatorSet_mono`
  Commutator-power relators are monotone in the normal subgroup.
- `foxCommutatorPowerSubgroup_mono`
  The finite Fox commutator-power subgroup is monotone in the normal subgroup.
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

omit [DecidableEq X] in
/-- Commutator-power relators are monotone in the normal subgroup. -/
theorem foxCommutatorPowerRelatorSet_mono
    {N M : Subgroup (FreeGroup X)} {n : ℕ} (hNM : N ≤ M) :
    foxCommutatorPowerRelatorSet (F := FreeGroup X) N n ⊆
      foxCommutatorPowerRelatorSet (F := FreeGroup X) M n := by
  intro g hg
  rcases hg with ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩
  · exact Or.inl ⟨a, hNM ha, b, hNM hb, rfl⟩
  · exact Or.inr ⟨a, hNM ha, rfl⟩

omit [DecidableEq X] in
/-- The finite Fox commutator-power subgroup is monotone in the normal subgroup. -/
theorem foxCommutatorPowerSubgroup_mono
    {N M : Subgroup (FreeGroup X)} (hNM : N ≤ M) (n : ℕ) :
    foxCommutatorPowerSubgroup (F := FreeGroup X) N n ≤
      foxCommutatorPowerSubgroup (F := FreeGroup X) M n := by
  simpa [foxCommutatorPowerSubgroup] using
    Subgroup.normalClosure_mono
      (foxCommutatorPowerRelatorSet_mono (X := X) (n := n) hNM)

omit [DecidableEq X] in
/-- Commutator-power relators are contravariantly monotone under divisibility of exponents. -/
theorem foxCommutatorPowerRelatorSet_dvd
    {N : Subgroup (FreeGroup X)} {n m : ℕ} (hnm : n ∣ m) :
    foxCommutatorPowerRelatorSet (F := FreeGroup X) N m ⊆
      foxCommutatorPowerRelatorSet (F := FreeGroup X) N n := by
  intro g hg
  rcases hg with ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩
  · exact Or.inl ⟨a, ha, b, hb, rfl⟩
  · rcases hnm with ⟨k, rfl⟩
    exact Or.inr ⟨a ^ k, N.pow_mem ha k, (pow_mul' a n k).symm⟩

omit [DecidableEq X] in
/--
The finite Fox commutator-power subgroup is contravariantly monotone under divisibility of
exponents.
-/
theorem foxCommutatorPowerSubgroup_dvd
    (N : Subgroup (FreeGroup X)) {n m : ℕ} (hnm : n ∣ m) :
    foxCommutatorPowerSubgroup (F := FreeGroup X) N m ≤
      foxCommutatorPowerSubgroup (F := FreeGroup X) N n := by
  simpa [foxCommutatorPowerSubgroup] using
    Subgroup.normalClosure_mono
      (foxCommutatorPowerRelatorSet_dvd (X := X) (N := N) hnm)

/-- Natural quotient map \(F/N \to F/M\) induced by an inclusion \(N \le M\). -/
def foxAlgebraicStageTargetQuotientMap
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal] (hNM : N ≤ M) :
    foxAlgebraicStageTargetQuotient (X := X) N →*
      foxAlgebraicStageTargetQuotient (X := X) M :=
  QuotientGroup.map _ _ (MonoidHom.id (FreeGroup X)) hNM

omit [DecidableEq X] in
/-- Evaluation of the finite-stage target quotient map on a representative. -/
@[simp]
theorem foxAlgebraicStageTargetQuotientMap_mk
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
    (hNM : N ≤ M) (w : FreeGroup X) :
    foxAlgebraicStageTargetQuotientMap (X := X) hNM (QuotientGroup.mk' N w) =
      QuotientGroup.mk' M w := by
  rfl

/-- Group-algebra map on finite-stage targets induced by \(N \le M\). -/
def foxAlgebraicStageTargetGroupAlgebraMap
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal] (hNM : N ≤ M) (n : ℕ) :
    foxAlgebraicStageTargetGroupAlgebra (X := X) N n →+*
      foxAlgebraicStageTargetGroupAlgebra (X := X) M n :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
    (foxAlgebraicStageTargetQuotientMap (X := X) hNM)

omit [DecidableEq X] in
/-- Evaluation of the finite-stage target group-algebra map on a represented word. -/
@[simp]
theorem foxAlgebraicStageTargetGroupAlgebraMap_of
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
    (hNM : N ≤ M) (n : ℕ) (w : FreeGroup X) :
    foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) (QuotientGroup.mk' N w)) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) M) (QuotientGroup.mk' M w) := by
  change
    MonoidAlgebra.mapDomain (foxAlgebraicStageTargetQuotientMap (X := X) hNM)
        (MonoidAlgebra.single (QuotientGroup.mk' N w) 1) =
      MonoidAlgebra.single (QuotientGroup.mk' M w) 1
  rw [MonoidAlgebra.mapDomain_single,
    foxAlgebraicStageTargetQuotientMap_mk]

omit [DecidableEq X] in
/-- Evaluation of the finite-stage target group-algebra map on a quotient basis element. -/
@[simp]
theorem foxAlgebraicStageTargetGroupAlgebraMap_of_quotient
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
    (hNM : N ≤ M) (n : ℕ) (q : foxAlgebraicStageTargetQuotient (X := X) N) :
    foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) q) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) M)
        (foxAlgebraicStageTargetQuotientMap (X := X) hNM q) := by
  rcases QuotientGroup.mk'_surjective N q with ⟨w, rfl⟩
  rw [foxAlgebraicStageTargetGroupAlgebraMap_of, foxAlgebraicStageTargetQuotientMap_mk]

/-- The natural quotient map between finite-stage source quotients is induced by \(N \le M\). -/
def foxAlgebraicStageSourceQuotientMap
    {N M : Subgroup (FreeGroup X)} (hNM : N ≤ M) (n : ℕ) :
    FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n →*
      FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) M n :=
  QuotientGroup.map _ _ (MonoidHom.id (FreeGroup X))
    (foxCommutatorPowerSubgroup_mono (X := X) hNM n)

omit [DecidableEq X] in
/-- Evaluation of the finite-stage source quotient map on a representative. -/
@[simp]
theorem foxAlgebraicStageSourceQuotientMap_mk
    {N M : Subgroup (FreeGroup X)}
    (hNM : N ≤ M) (n : ℕ) (w : FreeGroup X) :
    foxAlgebraicStageSourceQuotientMap (X := X) hNM n
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) w) =
      QuotientGroup.mk'
        (foxCommutatorPowerSubgroup (F := FreeGroup X) M n) w := by
  rfl

/-- Group-algebra map on finite-stage source quotients induced by \(N \le M\). -/
def foxAlgebraicStageSourceGroupAlgebraMap
    {N M : Subgroup (FreeGroup X)} (hNM : N ≤ M) (n : ℕ) :
    MonoidAlgebra (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) →+*
      MonoidAlgebra (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) M n) :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff n)
    (foxAlgebraicStageSourceQuotientMap (X := X) hNM n)

omit [DecidableEq X] in
/-- Evaluation of the finite-stage source group-algebra map on a represented word. -/
@[simp]
theorem foxAlgebraicStageSourceGroupAlgebraMap_of
    {N M : Subgroup (FreeGroup X)}
    (hNM : N ≤ M) (n : ℕ) (w : FreeGroup X) :
    foxAlgebraicStageSourceGroupAlgebraMap (X := X) hNM n
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
          (QuotientGroup.mk'
            (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) w)) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) M n)
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) M n) w) := by
  change
    MonoidAlgebra.mapDomain (foxAlgebraicStageSourceQuotientMap (X := X) hNM n)
        (MonoidAlgebra.single
          (QuotientGroup.mk'
            (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) w) 1) =
      MonoidAlgebra.single
        (QuotientGroup.mk'
          (foxCommutatorPowerSubgroup (F := FreeGroup X) M n) w) 1
  rw [MonoidAlgebra.mapDomain_single,
    foxAlgebraicStageSourceQuotientMap_mk]

omit [DecidableEq X] in
/-- Evaluation of the finite-stage source group-algebra map on a quotient basis element. -/
@[simp]
theorem foxAlgebraicStageSourceGroupAlgebraMap_of_quotient
    {N M : Subgroup (FreeGroup X)}
    (hNM : N ≤ M) (n : ℕ)
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageSourceGroupAlgebraMap (X := X) hNM n
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) M n)
        (foxAlgebraicStageSourceQuotientMap (X := X) hNM n q) := by
  rcases QuotientGroup.mk'_surjective
      (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
  rw [foxAlgebraicStageSourceGroupAlgebraMap_of, foxAlgebraicStageSourceQuotientMap_mk]

/-- Semidirect target map induced by functoriality in the normal subgroup. -/
def foxAlgebraicStageSemidirectMap
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal] (hNM : N ≤ M) (n : ℕ) :
    FoxAlgebraicStageSemidirect (X := X) N n →*
      FoxAlgebraicStageSemidirect (X := X) M n where
  toFun a :=
    { left := fun i => foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n (a.left i)
      right := foxAlgebraicStageTargetQuotientMap (X := X) hNM a.right }
  map_one' := by
    apply FoxAlgebraicStageSemidirect.ext
    · funext i
      simp only [FoxAlgebraicStageSemidirect.one_left, Pi.zero_apply, map_zero]
    · simp only [FoxAlgebraicStageSemidirect.one_right, map_one]
  map_mul' a b := by
    apply FoxAlgebraicStageSemidirect.ext
    · funext i
      have hright :
          foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
              (MonoidAlgebra.single a.right (1 : ModNCompletedCoeff n)) =
            MonoidAlgebra.single
              (foxAlgebraicStageTargetQuotientMap (X := X) hNM a.right) 1 := by
        change
          MonoidAlgebra.mapDomain
              (foxAlgebraicStageTargetQuotientMap (X := X) hNM)
              (MonoidAlgebra.single a.right 1) =
            MonoidAlgebra.single
              (foxAlgebraicStageTargetQuotientMap (X := X) hNM a.right) 1
        exact MonoidAlgebra.mapDomain_single
      simp only [FoxAlgebraicStageSemidirect.mul_left, MonoidAlgebra.of_apply, Pi.add_apply,
          Pi.smul_apply,
  smul_eq_mul, map_add, map_mul, hright]
    · simp only [FoxAlgebraicStageSemidirect.mul_right, map_mul]

/-- The finite-stage semidirect map carries the lift for \(N\) to the lift for \(M\). -/
theorem foxAlgebraicStageSemidirectMap_lift
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
    (hNM : N ≤ M) (n : ℕ) (w : FreeGroup X) :
    foxAlgebraicStageSemidirectMap (X := X) hNM n
        (foxAlgebraicStageLift (X := X) N n w) =
      foxAlgebraicStageLift (X := X) M n w := by
  induction w using FreeGroup.induction_on with
  | C1 =>
      simp only [foxAlgebraicStageLift, QuotientGroup.mk'_apply, map_one]
  | of x =>
      apply FoxAlgebraicStageSemidirect.ext
      · funext i
        by_cases hix : i = x
        · subst hix
          simp only [foxAlgebraicStageSemidirectMap, foxAlgebraicStageLift,
              QuotientGroup.mk'_apply, FreeGroup.lift_apply_of,
  MonoidHom.coe_mk, OneHom.coe_mk, Pi.single_eq_same, map_one]
        · simp only [foxAlgebraicStageSemidirectMap, foxAlgebraicStageLift,
            QuotientGroup.mk'_apply, FreeGroup.lift_apply_of,
  MonoidHom.coe_mk, OneHom.coe_mk, Pi.single_eq_of_ne hix, map_zero]
      · exact foxAlgebraicStageTargetQuotientMap_mk (X := X) hNM (FreeGroup.of x)
  | inv_of x hx =>
      simpa using congrArg Inv.inv hx
  | mul x y hx hy =>
      simp only [map_mul, hx, hy]

/-- Naturality of finite-stage Fox derivative coordinates under \(N \le M\). -/
theorem foxAlgebraicStageDerivative_natural
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
    (hNM : N ≤ M) (n : ℕ) (i : X) (w : FreeGroup X) :
    foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
        (foxAlgebraicStageDerivative (X := X) N n i w) =
      foxAlgebraicStageDerivative (X := X) M n i w := by
  have h :=
    congrArg FoxAlgebraicStageSemidirect.left
      (foxAlgebraicStageSemidirectMap_lift (X := X) hNM n w)
  simpa [foxAlgebraicStageDerivative, foxAlgebraicStageDerivativeVector,
    foxAlgebraicStageSemidirectMap] using congrFun h i

/-- Naturality of finite-stage group-algebra derivative coordinates under \(N \le M\). -/
theorem foxAlgebraicStageGroupAlgebraDerivative_natural
    {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
    (hNM : N ≤ M) (n : ℕ) (i : X)
    (x : MonoidAlgebra (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)) :
    foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
        (foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x) =
      foxAlgebraicStageGroupAlgebraDerivative (X := X) M n i
        (foxAlgebraicStageSourceGroupAlgebraMap (X := X) hNM n x) := by
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
          (foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x) =
        foxAlgebraicStageGroupAlgebraDerivative (X := X) M n i
          (foxAlgebraicStageSourceGroupAlgebraMap (X := X) hNM n x))
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q with ⟨w, rfl⟩
    rw [foxAlgebraicStageGroupAlgebraDerivative_of,
      foxAlgebraicStageSourceGroupAlgebraMap_of,
      foxAlgebraicStageGroupAlgebraDerivative_of,
      foxAlgebraicStageDerivative_natural]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro a x hx
    calc
      foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
          (foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i (a • x))
        =
          foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
            (a • foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x) := by
            rw [LinearMap.map_smul]
      _ =
          a • foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
            (foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x) := by
            exact MonoidAlgebra.mapDomain_smul
              (foxAlgebraicStageTargetQuotientMap (X := X) hNM) a
              (foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x)
      _ =
          a • foxAlgebraicStageGroupAlgebraDerivative (X := X) M n i
            (foxAlgebraicStageSourceGroupAlgebraMap (X := X) hNM n x) := by
            rw [hx]
      _ =
          foxAlgebraicStageGroupAlgebraDerivative (X := X) M n i
            (a • foxAlgebraicStageSourceGroupAlgebraMap (X := X) hNM n x) := by
            rw [LinearMap.map_smul]
      _ =
            foxAlgebraicStageGroupAlgebraDerivative (X := X) M n i
            (foxAlgebraicStageSourceGroupAlgebraMap (X := X) hNM n (a • x)) := by
            congr 1
            exact
              (MonoidAlgebra.mapDomain_smul
                (foxAlgebraicStageSourceQuotientMap (X := X) hNM n) a x).symm


end

end FoxDifferential
