import ProCGroups.FoxDifferential.Completed.FiniteStage.Stage.Derivative.Lift

set_option autoImplicit false

/-!
# Fox differential: finite stage — stage — derivative — relators

The principal declarations in this module are:

- `foxAlgebraicStageLift_right_eq_one_of_mem`
  If a word lies in N, the finite-stage lift has trivial right component.
- `mem_ker_foxAlgebraicStageLift_iff`
  Membership in the kernel of the finite Fox stage lift is equivalent to vanishing of the
  corresponding finite-stage coordinate.
- `ker_foxAlgebraicStageLift_le_foxCommutatorPowerSubgroup_iff`
  The finite-stage Magnus reverse inclusion is equivalent to the derivative-zero criterion inside
  \(N\).
- `foxAlgebraicStageSemidirect_commutator_eq_one_of_right_one`
  In the finite-stage semidirect product, commutators of elements with trivial right component are
  trivial.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC
open scoped commutatorElement

universe u v

variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]


variable {X : Type u} [DecidableEq X]
variable (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ)

/-- If a word lies in N, the finite-stage lift has trivial right component. -/
theorem foxAlgebraicStageLift_right_eq_one_of_mem
    {a : FreeGroup X} (ha : a ∈ N) :
    (foxAlgebraicStageLift (X := X) N n a).right = 1 := by
  rw [foxAlgebraicStageLift_right]
  apply QuotientGroup.eq.2
  simpa using ha

/--
Membership in the kernel of the finite Fox stage lift is equivalent to vanishing of the
corresponding finite-stage coordinate.
-/
theorem mem_ker_foxAlgebraicStageLift_iff
    {N : Subgroup (FreeGroup X)} [N.Normal] {n : ℕ}
    {w : FreeGroup X} :
    w ∈ (foxAlgebraicStageLift (X := X) N n).ker ↔
      w ∈ N ∧ foxAlgebraicStageDerivativeVector (X := X) N n w = 0 := by
  constructor
  · intro hw
    have hlift : foxAlgebraicStageLift (X := X) N n w = 1 := by
      simpa [MonoidHom.mem_ker] using hw
    constructor
    · have hright := congrArg FoxAlgebraicStageSemidirect.right hlift
      rw [foxAlgebraicStageLift_right] at hright
      exact (QuotientGroup.eq_one_iff (N := N) w).1 hright
    · have hleft := congrArg FoxAlgebraicStageSemidirect.left hlift
      simpa [foxAlgebraicStageDerivativeVector] using hleft
  · rintro ⟨hwN, hder⟩
    rw [MonoidHom.mem_ker]
    apply FoxAlgebraicStageSemidirect.ext
    · simpa [foxAlgebraicStageDerivativeVector] using hder
    · rw [foxAlgebraicStageLift_right]
      exact (QuotientGroup.eq_one_iff (N := N) w).2 hwN

/--
The finite-stage Magnus reverse inclusion is equivalent to the derivative-zero criterion inside
\(N\).
-/
theorem ker_foxAlgebraicStageLift_le_foxCommutatorPowerSubgroup_iff
    (N : Subgroup (FreeGroup X)) [N.Normal] (n : ℕ) :
    (foxAlgebraicStageLift (X := X) N n).ker ≤
        foxCommutatorPowerSubgroup (F := FreeGroup X) N n ↔
      ∀ w : FreeGroup X,
        w ∈ N →
        foxAlgebraicStageDerivativeVector (X := X) N n w = 0 →
          w ∈ foxCommutatorPowerSubgroup (F := FreeGroup X) N n := by
  constructor
  · intro hle w hwN hder
    exact hle ((mem_ker_foxAlgebraicStageLift_iff
      (X := X) (N := N) (n := n)).2 ⟨hwN, hder⟩)
  · intro h w hw
    rcases (mem_ker_foxAlgebraicStageLift_iff
      (X := X) (N := N) (n := n)).1 hw with ⟨hwN, hder⟩
    exact h w hwN hder

omit [DecidableEq X] in
/--
In the finite-stage semidirect product, commutators of elements with trivial right component are
trivial.
-/
theorem foxAlgebraicStageSemidirect_commutator_eq_one_of_right_one
    (a b : FoxAlgebraicStageSemidirect (X := X) N n)
    (ha : a.right = 1) (hb : b.right = 1) :
    ⁅a, b⁆ = 1 := by
  rw [commutatorElement_def]
  apply FoxAlgebraicStageSemidirect.ext
  · funext i
    have hone :
        (MonoidAlgebra.single
          (1 : foxAlgebraicStageTargetQuotient (X := X) N)
          (1 : ModNCompletedCoeff n) :
            foxAlgebraicStageTargetGroupAlgebra (X := X) N n) = 1 := by
      simp only [MonoidAlgebra.one_def]
    simp only [FoxAlgebraicStageSemidirect.mul_left, ha, MonoidAlgebra.of_apply, hone, one_smul,
  FoxAlgebraicStageSemidirect.mul_right, hb, mul_one, FoxAlgebraicStageSemidirect.inv_left,
      inv_one, smul_neg, add_assoc,
  add_neg_cancel_comm_assoc, FoxAlgebraicStageSemidirect.inv_right, Pi.add_apply, Pi.neg_apply,
      add_neg_cancel,
  FoxAlgebraicStageSemidirect.one_left, Pi.zero_apply]
  · simp only [FoxAlgebraicStageSemidirect.mul_right, ha, hb, mul_one,
      FoxAlgebraicStageSemidirect.inv_right, inv_one,
  FoxAlgebraicStageSemidirect.one_right]

/-- The finite-stage lift kills commutators of words in \(N\). -/
theorem foxAlgebraicStageLift_commutator_eq_one_of_mem
    {a b : FreeGroup X} (ha : a ∈ N) (hb : b ∈ N) :
    foxAlgebraicStageLift (X := X) N n ⁅a, b⁆ = 1 := by
  rw [map_commutatorElement]
  exact foxAlgebraicStageSemidirect_commutator_eq_one_of_right_one
    (X := X) N n
    (foxAlgebraicStageLift (X := X) N n a)
    (foxAlgebraicStageLift (X := X) N n b)
    (foxAlgebraicStageLift_right_eq_one_of_mem (X := X) N n ha)
    (foxAlgebraicStageLift_right_eq_one_of_mem (X := X) N n hb)

omit [DecidableEq X] in
/--
Powers of a finite-stage semidirect element with trivial right component still have trivial
right component.
-/
theorem foxAlgebraicStageSemidirect_pow_right_eq_one_of_right_one
    (a : FoxAlgebraicStageSemidirect (X := X) N n)
    (ha : a.right = 1) (m : ℕ) :
    (a ^ m).right = 1 := by
  induction m with
  | zero =>
      simp only [pow_zero, FoxAlgebraicStageSemidirect.one_right]
  | succ m ih =>
      rw [pow_succ]
      simp only [FoxAlgebraicStageSemidirect.mul_right, ih, ha, mul_one]

omit [DecidableEq X] in
/--
Powers of a finite-stage semidirect element with trivial right component scale the left
component by the exponent.
-/
theorem foxAlgebraicStageSemidirect_pow_left_of_right_one
    (a : FoxAlgebraicStageSemidirect (X := X) N n)
    (ha : a.right = 1) (m : ℕ) :
    (a ^ m).left = m • a.left := by
  induction m with
  | zero =>
      simp only [pow_zero, FoxAlgebraicStageSemidirect.one_left, zero_nsmul]
  | succ m ih =>
      rw [pow_succ]
      have hright :
          (a ^ m).right = 1 :=
        foxAlgebraicStageSemidirect_pow_right_eq_one_of_right_one
          (X := X) N n a ha m
      have hone :
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N) 1 :
              foxAlgebraicStageTargetGroupAlgebra (X := X) N n) = 1 := by
        exact map_one
          (MonoidAlgebra.of (ModNCompletedCoeff n)
            (foxAlgebraicStageTargetQuotient (X := X) N))
      ext i q
      simp only [FoxAlgebraicStageSemidirect.mul_left, ih, nsmul_eq_mul, hright, hone, one_smul,
          Pi.add_apply,
  Pi.mul_apply, Pi.natCast_apply, MonoidAlgebra.coeff_add, Pi.smul_apply, Nat.cast_succ,
      add_mul, one_mul]

omit [DecidableEq X] in
/--
The \(n\)-th power of a finite-stage semidirect element with trivial right component is trivial
over \(\mathbb{Z}/n\mathbb{Z}\).
-/
theorem foxAlgebraicStageSemidirect_pow_char_eq_one_of_right_one
    (a : FoxAlgebraicStageSemidirect (X := X) N n)
    (ha : a.right = 1) :
    a ^ n = 1 := by
  apply FoxAlgebraicStageSemidirect.ext
  · rw [foxAlgebraicStageSemidirect_pow_left_of_right_one (X := X) N n a ha n]
    exact ZModModule.char_nsmul_eq_zero (n := n) a.left
  · exact foxAlgebraicStageSemidirect_pow_right_eq_one_of_right_one
      (X := X) N n a ha n

/-- The finite-stage lift kills \(n\)-th powers of words in \(N\). -/
theorem foxAlgebraicStageLift_pow_eq_one_of_mem
    {a : FreeGroup X} (ha : a ∈ N) :
    foxAlgebraicStageLift (X := X) N n (a ^ n) = 1 := by
  rw [map_pow]
  exact foxAlgebraicStageSemidirect_pow_char_eq_one_of_right_one
    (X := X) N n (foxAlgebraicStageLift (X := X) N n a)
    (foxAlgebraicStageLift_right_eq_one_of_mem (X := X) N n ha)

/-- The finite Fox commutator-power relators lie in the kernel of the finite-stage lift. -/
theorem foxCommutatorPowerRelatorSet_subset_ker_foxAlgebraicStageLift :
    foxCommutatorPowerRelatorSet (F := FreeGroup X) N n ⊆
      (foxAlgebraicStageLift (X := X) N n).ker := by
  intro g hg
  change foxAlgebraicStageLift (X := X) N n g = 1
  rcases hg with ⟨a, ha, b, hb, rfl⟩ | ⟨a, ha, rfl⟩
  · exact foxAlgebraicStageLift_commutator_eq_one_of_mem (X := X) N n ha hb
  · exact foxAlgebraicStageLift_pow_eq_one_of_mem (X := X) N n ha

/-- The finite Fox commutator-power subgroup lies in the kernel of the finite-stage lift. -/
theorem foxCommutatorPowerSubgroup_le_ker_foxAlgebraicStageLift :
    foxCommutatorPowerSubgroup (F := FreeGroup X) N n ≤
      (foxAlgebraicStageLift (X := X) N n).ker := by
  exact Subgroup.normalClosure_le_normal
    (foxCommutatorPowerRelatorSet_subset_ker_foxAlgebraicStageLift
      (X := X) N n)


end

end FoxDifferential
