import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Naturality

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — stage — source

The principal declarations in this module are:

- `foxAlgebraicStageSourceRepresentative`
  A chosen free-group representative of a finite Fox source quotient element, supplying
  source-valued coefficients without a canonicality requirement.
- `foxAlgebraicStageSourceQuotientDerivative`
  Source-valued finite Fox coefficient attached to a source quotient element, using a chosen
  free-group representative.
- `foxAlgebraicStageSourceRepresentative_mk`
  The chosen representative maps back to the original source quotient element.
- `foxAlgebraicStageSourceGroupAlgebraDerivative_of_quotient`
  Evaluation of the source-valued finite Fox derivative on a source quotient basis element.
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

/--
A chosen free-group representative of a finite Fox source quotient element, supplying
source-valued coefficients without a canonicality requirement.
-/
def foxAlgebraicStageSourceRepresentative
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    FreeGroup X :=
  Classical.choose
    (QuotientGroup.mk'_surjective
      (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)

omit [DecidableEq X] [N.Normal] in
/-- The chosen representative maps back to the original source quotient element. -/
@[simp]
theorem foxAlgebraicStageSourceRepresentative_mk
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    QuotientGroup.mk'
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
        (foxAlgebraicStageSourceRepresentative (X := X) N n q) = q := by
  exact
    Classical.choose_spec
      (QuotientGroup.mk'_surjective
        (foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)

/--
Source-valued finite Fox coefficient attached to a source quotient element, using a chosen
free-group representative.
-/
def foxAlgebraicStageSourceQuotientDerivative
    (i : X)
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageSourceGroupAlgebra (X := X) N n :=
  foxAlgebraicStageDerivative
    (X := X)
    (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
    n i (foxAlgebraicStageSourceRepresentative (X := X) N n q)

/--
Source-valued finite Fox derivative on the source group algebra. It is defined by extending the
representative-based source coefficients linearly.
-/
def foxAlgebraicStageSourceGroupAlgebraDerivative (i : X) :
    foxAlgebraicStageSourceGroupAlgebra (X := X) N n →ₗ[ModNCompletedCoeff n]
      foxAlgebraicStageSourceGroupAlgebra (X := X) N n :=
  (Finsupp.linearCombination (ModNCompletedCoeff n)
    (foxAlgebraicStageSourceQuotientDerivative (X := X) N n i)).comp
      (MonoidAlgebra.coeffLinearEquiv (ModNCompletedCoeff n)).toLinearMap

omit [N.Normal] in
/-- Evaluation of the source-valued finite Fox derivative on a source quotient basis element. -/
@[simp]
theorem foxAlgebraicStageSourceGroupAlgebraDerivative_of_quotient
    (i : X)
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
      foxAlgebraicStageSourceQuotientDerivative (X := X) N n i q := by
  change
      (Finsupp.linearCombination (ModNCompletedCoeff n)
        (foxAlgebraicStageSourceQuotientDerivative (X := X) N n i))
          (Finsupp.single q (1 : ModNCompletedCoeff n)) =
        foxAlgebraicStageSourceQuotientDerivative (X := X) N n i q
  rw [Finsupp.linearCombination_single, one_smul]

omit [N.Normal] in
/-- The source-valued finite Fox fundamental formula on a source quotient basis element. -/
theorem foxAlgebraicStageSourceGroupAlgebraDerivative_of_quotient_fundamental_formula
    [Fintype X]
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q - 1 =
      ∑ i : X,
        foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
            (QuotientGroup.mk'
              (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (FreeGroup.of i)) - 1) := by
  let C : Subgroup (FreeGroup X) :=
    foxCommutatorPowerSubgroup (F := FreeGroup X) N n
  let w : FreeGroup X :=
    foxAlgebraicStageSourceRepresentative (X := X) N n q
  have hw : QuotientGroup.mk' C w = q := by
    simpa [C, w] using foxAlgebraicStageSourceRepresentative_mk (X := X) N n q
  have h :=
    foxAlgebraicStageDerivative_fundamental_formula
      (X := X) (N := C) (n := n) w
  have hD (i : X) :
      foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) =
        foxAlgebraicStageDerivative (X := X) C n i w := by
    change
      (Finsupp.linearCombination (ModNCompletedCoeff n)
          (foxAlgebraicStageSourceQuotientDerivative (X := X) N n i))
        (Finsupp.single q (1 : ModNCompletedCoeff n)) =
        foxAlgebraicStageDerivative (X := X) C n i w
    rw [Finsupp.linearCombination_single, one_smul]
    simp only [foxAlgebraicStageSourceQuotientDerivative, C, w]
  calc
    MonoidAlgebra.of (ModNCompletedCoeff n)
        (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q - 1 =
        ∑ i : X,
          foxAlgebraicStageDerivative (X := X) C n i w *
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (QuotientGroup.mk'
                (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (FreeGroup.of i)) - 1) := by
      simpa [C, w, hw] using h
    _ =
        ∑ i : X,
          foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) *
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (QuotientGroup.mk'
                (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (FreeGroup.of i)) - 1) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hD i]

omit [N.Normal] in
/-- Source-valued finite Fox fundamental formula on the full source group algebra. -/
theorem foxAlgebraicStageSourceGroupAlgebraDerivative_groupAlgebra_fundamental_formula
    [Fintype X]
    (x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n) :
    x -
        algebraMap (ModNCompletedCoeff n)
          (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
          (foxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n x) =
      ∑ i : X,
        foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i x *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
            (QuotientGroup.mk'
              (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (FreeGroup.of i)) - 1) := by
  classical
  let P := fun y : foxAlgebraicStageSourceGroupAlgebra (X := X) N n =>
    y -
        algebraMap (ModNCompletedCoeff n)
          (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
          (foxCommutatorPowerSourceGroupAlgebraAugmentation
            (F := FreeGroup X) N n y) =
      ∑ i : X,
        foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i y *
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
            (QuotientGroup.mk'
              (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (FreeGroup.of i)) - 1)
  change P x
  refine MonoidAlgebra.induction_on (motive := P) x ?_ ?_ ?_
  · intro q
    dsimp [P]
    rw [foxCommutatorPowerSourceGroupAlgebraAugmentation_of_quotient]
    simpa only [MonoidAlgebra.one_def, QuotientGroup.mk'_apply] using
      foxAlgebraicStageSourceGroupAlgebraDerivative_of_quotient_fundamental_formula
        (X := X) (N := N) (n := n) q
  · intro x y hx hy
    dsimp [P] at hx hy ⊢
    let x0 : foxAlgebraicStageSourceGroupAlgebra (X := X) N n := x
    let y0 : foxAlgebraicStageSourceGroupAlgebra (X := X) N n := y
    have hx0 :
        x0 -
            algebraMap (ModNCompletedCoeff n)
              (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
              (foxCommutatorPowerSourceGroupAlgebraAugmentation
                (F := FreeGroup X) N n x0) =
          ∑ i : X,
            foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i x0 *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1) := by
      simpa [x0] using hx
    have hy0 :
        y0 -
            algebraMap (ModNCompletedCoeff n)
              (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
              (foxCommutatorPowerSourceGroupAlgebraAugmentation
                (F := FreeGroup X) N n y0) =
          ∑ i : X,
            foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i y0 *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1) := by
      simpa [y0] using hy
    change
      x0 + y0 -
          algebraMap (ModNCompletedCoeff n)
            (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
            (foxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N n (x0 + y0)) =
        ∑ i : X,
          foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i (x0 + y0) *
            (MonoidAlgebra.of (ModNCompletedCoeff n)
              (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
              (QuotientGroup.mk'
                (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (FreeGroup.of i)) - 1)
    calc
      x0 + y0 -
          algebraMap (ModNCompletedCoeff n)
            (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
            (foxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N n (x0 + y0)) =
          (x0 -
              algebraMap (ModNCompletedCoeff n)
                (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
                (foxCommutatorPowerSourceGroupAlgebraAugmentation
                  (F := FreeGroup X) N n x0)) +
            (y0 -
              algebraMap (ModNCompletedCoeff n)
                (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
                (foxCommutatorPowerSourceGroupAlgebraAugmentation
                  (F := FreeGroup X) N n y0)) := by
        rw [map_add, map_add]
        abel
      _ = (∑ i : X,
            foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i x0 *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1)) +
          (∑ i : X,
            foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i y0 *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1)) := by
        rw [hx0, hy0]
      _ = ∑ i : X,
            (foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i x0 +
              foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i y0) *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [add_mul]
      _ = ∑ i : X,
            foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i (x0 + y0) *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_add]
  · intro a y hy
    dsimp [P] at hy ⊢
    calc
      a • y -
          algebraMap (ModNCompletedCoeff n)
            (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
            (foxCommutatorPowerSourceGroupAlgebraAugmentation
              (F := FreeGroup X) N n (a • y)) =
          a •
            (y -
              algebraMap (ModNCompletedCoeff n)
                (foxAlgebraicStageSourceGroupAlgebra (X := X) N n)
                (foxCommutatorPowerSourceGroupAlgebraAugmentation
                  (F := FreeGroup X) N n y)) := by
        rw [map_smul, smul_sub]
        simp only [Algebra.smul_def, map_mul, Algebra.algebraMap_self,
          RingHom.coe_id, id_eq]
      _ = a • (∑ i : X,
            foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i
              y *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1)) := by
        exact congrArg (fun z => a • z) hy
      _ = ∑ i : X,
            foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i
              (a • y) *
              (MonoidAlgebra.of (ModNCompletedCoeff n)
                (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                (QuotientGroup.mk'
                  (foxCommutatorPowerSubgroup (F := FreeGroup X) N n)
                  (FreeGroup.of i)) - 1) := by
        rw [Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_smul, smul_mul_assoc]

omit [DecidableEq X] in
/--
The source-to-target group-algebra map commutes with scalar multiplication by
\(\mathbb{Z}/n\mathbb{Z}\) coefficients.
-/
theorem foxCommutatorPowerGroupAlgebraMap_smul
    (a : ModNCompletedCoeff n)
    (x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n) :
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n (a • x) =
      a • foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n x := by
  rw [Algebra.smul_def, Algebra.smul_def, RingHom.map_mul]
  congr 1
  simp only [MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id,
      Function.comp_apply, id_eq,
  foxCommutatorPowerGroupAlgebraMap_single_apply, map_one]

/--
Applying the source-to-target finite group-algebra map to the source-valued derivative gives the
existing target-valued finite Fox derivative.
-/
theorem foxAlgebraicStageSourceGroupAlgebraDerivative_map_of_quotient
    (i : X)
    (q : FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) :
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
        (foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)) =
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q) := by
  rw [foxAlgebraicStageSourceGroupAlgebraDerivative_of_quotient]
  let C : Subgroup (FreeGroup X) :=
    foxCommutatorPowerSubgroup (F := FreeGroup X) N n
  let hCN : C ≤ N :=
    foxCommutatorPowerSubgroup_le_normal (F := FreeGroup X) N n
  let w : FreeGroup X :=
    foxAlgebraicStageSourceRepresentative (X := X) N n q
  have hw : QuotientGroup.mk' C w = q := by
    simpa [C, w] using foxAlgebraicStageSourceRepresentative_mk (X := X) N n q
  change
    foxAlgebraicStageTargetGroupAlgebraMap (X := X) hCN n
        (foxAlgebraicStageDerivative (X := X) C n i w) =
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i
        (MonoidAlgebra.of (ModNCompletedCoeff n)
          (FreeGroup X ⧸ foxCommutatorPowerSubgroup (F := FreeGroup X) N n) q)
  rw [← hw, foxAlgebraicStageGroupAlgebraDerivative_of]
  exact foxAlgebraicStageDerivative_natural (X := X) hCN n i w

/--
Applying the source-to-target finite group-algebra map to the source-valued derivative agrees
with the target-valued finite Fox derivative on all source group-algebra elements.
-/
theorem foxAlgebraicStageSourceGroupAlgebraDerivative_map
    (i : X) (x : foxAlgebraicStageSourceGroupAlgebra (X := X) N n) :
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
        (foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i x) =
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i x := by
  classical
  let P := fun y : foxAlgebraicStageSourceGroupAlgebra (X := X) N n =>
    foxCommutatorPowerGroupAlgebraMap (F := FreeGroup X) N n
        (foxAlgebraicStageSourceGroupAlgebraDerivative (X := X) N n i y) =
      foxAlgebraicStageGroupAlgebraDerivative (X := X) N n i y
  change P x
  refine MonoidAlgebra.induction_on (motive := P) x ?_ ?_ ?_
  · intro q
    dsimp [P]
    exact
      foxAlgebraicStageSourceGroupAlgebraDerivative_map_of_quotient
        (X := X) (N := N) (n := n) i q
  · intro y z hy hz
    dsimp [P] at hy hz ⊢
    rw [map_add, map_add, hy, hz]
    rw [map_add]
  · intro a y hy
    dsimp [P] at hy ⊢
    rw [map_smul, foxCommutatorPowerGroupAlgebraMap_smul, map_smul, hy]


end

end FoxDifferential
