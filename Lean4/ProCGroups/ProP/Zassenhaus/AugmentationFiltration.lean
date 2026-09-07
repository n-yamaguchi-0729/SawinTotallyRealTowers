import Mathlib.Topology.Algebra.Ring.Ideal
import ProCGroups.CompletedGroupAlgebra.Augmentation.Functoriality
import ProCGroups.FiniteGroups.StandardClasses

set_option autoImplicit false
/-!
# The closed augmentation filtration over `ZMod p`

This file specializes the completed group algebra already provided by
`ProCGroups` to finite `p`-group quotients and packages the closures of the
powers of its canonical augmentation ideal.  The elementary multiplicative
lemmas are stated once here so later Zassenhaus files need no repeated
two-sided-ideal instances.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra

noncomputable section

universe u

variable (p : ℕ) [Fact p.Prime]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The mod-`p` completed group algebra formed from finite `p`-group quotients. -/
abbrev ModPCompletedGroupAlgebra :=
  CompletedGroupAlgebraInClass (ProCGroups.FiniteGroupClass.pGroup p) (ZMod p) G

/-- The mod-`p` completed group algebra has characteristic `p`.

The proof uses the canonical augmentation as a retraction to `ZMod p`; no
global characteristic instance is installed. -/
theorem modPCompletedGroupAlgebraCharP :
    CharP (ModPCompletedGroupAlgebra p G) p where
  cast_eq_zero_iff n := by
    constructor
    · intro hn
      have haug := congrArg
        (CompletedGroupAlgebra.completedGroupAlgebraCanonicalAugmentationInClass
          (R := ZMod p) (G := G) (ProCGroups.FiniteGroupClass.pGroup p)) hn
      have hnZMod : (n : ZMod p) = 0 := by
        simpa using haug
      exact (CharP.cast_eq_zero_iff (ZMod p) p n).mp hnZMod
    · intro hn
      have hnZMod : (n : ZMod p) = 0 :=
        (CharP.cast_eq_zero_iff (ZMod p) p n).mpr hn
      calc
        (n : ModPCompletedGroupAlgebra p G) =
            algebraMap (ZMod p) (ModPCompletedGroupAlgebra p G) (n : ZMod p) := by
              simp
        _ = 0 := by rw [hnZMod, map_zero]

/-- The canonical augmentation ideal in the mod-`p` completed group algebra. -/
abbrev modPAugmentationIdeal : Ideal (ModPCompletedGroupAlgebra p G) :=
  completedGroupAlgebraCanonicalAugmentationIdealInClass
    (R := ZMod p) (G := G) (ProCGroups.FiniteGroupClass.pGroup p)

/-- The closure of the `n`-th power of the mod-`p` augmentation ideal. -/
def closedAugmentationPower (n : ℕ) : Ideal (ModPCompletedGroupAlgebra p G) :=
  ((modPAugmentationIdeal p G) ^ n).closure

/-- Closed augmentation powers decrease with the exponent. -/
theorem closedAugmentationPower_antitone : Antitone (closedAugmentationPower p G) := by
  intro m n hmn x hx
  change x ∈ closure ((modPAugmentationIdeal p G) ^ n) at hx
  change x ∈ closure ((modPAugmentationIdeal p G) ^ m)
  exact closure_mono (Ideal.pow_le_pow_right hmn) hx

/-- Multiplication of points in two ideal closures lands in the closure of the
ideal product. -/
theorem mul_mem_idealClosure_mul
    {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    {I J : Ideal R} {x y : R} (hx : x ∈ I.closure) (hy : y ∈ J.closure) :
    x * y ∈ (I * J).closure := by
  have hright : ∀ z ∈ J, x * z ∈ (I * J).closure := by
    intro z hz
    exact map_mem_closure (f := fun a : R => a * z) (s := (I : Set R))
      (t := ((I * J : Ideal R) : Set R)) (continuous_mul_const z) hx fun a ha =>
        Ideal.mul_mem_mul ha hz
  have hxy := map_mem_closure (f := fun z : R => x * z) (s := (J : Set R))
    (t := closure ((I * J : Ideal R) : Set R)) (continuous_const_mul x) hy hright
  rw [isClosed_closure.closure_eq] at hxy
  exact hxy

/-- The canonical augmentation ideal is two-sided. -/
theorem modPAugmentationIdeal_isTwoSided :
    (modPAugmentationIdeal p G).IsTwoSided := by
  change (RingHom.ker
    (CompletedGroupAlgebra.completedGroupAlgebraCanonicalAugmentationInClass
      (R := ZMod p) (G := G)
      (ProCGroups.FiniteGroupClass.pGroup p))).IsTwoSided
  infer_instance

/-- Closed augmentation powers multiply with additive exponents. -/
theorem closedAugmentationPower_mul_mem
    {m n : ℕ} {x y : ModPCompletedGroupAlgebra p G}
    (hx : x ∈ closedAugmentationPower p G m)
    (hy : y ∈ closedAugmentationPower p G n) :
    x * y ∈ closedAugmentationPower p G (m + n) := by
  let _ : (modPAugmentationIdeal p G).IsTwoSided :=
    modPAugmentationIdeal_isTwoSided p G
  change x * y ∈ closure ((modPAugmentationIdeal p G) ^ (m + n))
  rw [Ideal.IsTwoSided.pow_add]
  exact mul_mem_idealClosure_mul hx hy

/-- A power of a point in the `n`-th closed augmentation layer belongs to the
`n*k`-th layer. -/
theorem pow_mem_closedAugmentationPower
    {n : ℕ} {x : ModPCompletedGroupAlgebra p G}
    (hx : x ∈ closedAugmentationPower p G n) (k : ℕ) :
    x ^ k ∈ closedAugmentationPower p G (n * k) := by
  induction k with
  | zero =>
      rw [Nat.mul_zero]
      change 1 ∈ closure (((modPAugmentationIdeal p G) ^ 0 :
        Ideal (ModPCompletedGroupAlgebra p G)) : Set (ModPCompletedGroupAlgebra p G))
      apply subset_closure
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      trivial
  | succ k ih =>
      rw [pow_succ, Nat.mul_succ]
      exact closedAugmentationPower_mul_mem (p := p) (G := G) ih hx

/-- A ring homomorphism taking `I` to `J` takes `I^n` to `J^n`. -/
theorem ringHom_mem_ideal_pow
    {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    {I : Ideal R} {J : Ideal S}
    (hmap : ∀ x ∈ I, f x ∈ J) (n : ℕ) {x : R} (hx : x ∈ I ^ n) :
    f x ∈ J ^ n := by
  induction n generalizing x with
  | zero =>
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      trivial
  | succ n ih =>
      rw [Submodule.pow_succ] at hx ⊢
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        rw [map_mul]
        exact Ideal.mul_mem_mul (ih ha) (hmap b hb)
      · intro a b ha hb
        rw [map_add]
        exact (J ^ (n + 1)).add_mem ha hb

/-- The closure of a two-sided ideal remains two-sided in a topological ring. -/
theorem idealClosure_isTwoSided
    {R : Type*} [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    (I : Ideal R) [I.IsTwoSided] : I.closure.IsTwoSided := by
  constructor
  intro a b ha
  exact map_mem_closure (f := fun x : R => x * b) (s := (I : Set R))
    (t := (I : Set R)) (continuous_mul_const b) ha fun x hx => I.mul_mem_right b hx

/-- Every closed augmentation power is two-sided. -/
theorem closedAugmentationPower_isTwoSided (n : ℕ) :
    (closedAugmentationPower p G n).IsTwoSided := by
  let _ : (modPAugmentationIdeal p G).IsTwoSided :=
    modPAugmentationIdeal_isTwoSided p G
  let _ : ((modPAugmentationIdeal p G) ^ n).IsTwoSided := inferInstance
  exact idealClosure_isTwoSided ((modPAugmentationIdeal p G) ^ n)

end

end ClassFieldTower.ProP
