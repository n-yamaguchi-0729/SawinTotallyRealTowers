import ProCGroups.ProP.Zassenhaus.AugmentationFiltration

set_option autoImplicit false
/-!
# Filtration drop for continuous Fox operators

An additive Fox operator satisfying the right-Fox Leibniz rule lowers powers
of the augmentation ideal.  Continuity extends this algebraic result to closed
powers, and hence makes the drop independent of representatives modulo the
next source layer.
-/

open scoped Topology

namespace ClassFieldTower.ProP

noncomputable section

universe u v w

variable {A : Type u} {B : Type v} {R : Type w}
variable [Ring A] [Ring B] [Ring R]

/-- An additive Fox operator lowers ordinary powers of the augmentation ideal.

The product rule is written in the right-Fox convention used by the existing
finite-stage PCG derivative.  The proof has no topological hypotheses. -/
theorem mem_ideal_pow_of_foxOperator
    (epsilon : A →+* R) (phi : A →+* B) (coeff : R →+* B)
    (D : A →+ B) (J : Ideal B) [J.IsTwoSided]
    (hphi : ∀ x ∈ RingHom.ker epsilon, phi x ∈ J)
    (hleibniz : ∀ x y,
      D (x * y) = coeff (epsilon y) * D x + phi x * D y)
    (n : ℕ) {x : A} (hx : x ∈ RingHom.ker epsilon ^ (n + 1)) :
    D x ∈ J ^ n := by
  induction n generalizing x with
  | zero =>
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      trivial
  | succ n ih =>
      let _ : (RingHom.ker epsilon ^ (n + 1)).IsTwoSided := inferInstance
      rw [Submodule.pow_succ] at hx
      refine Submodule.mul_induction_on hx ?_ ?_
      · intro a ha b hb
        rw [hleibniz, show epsilon b = 0 from hb, map_zero, zero_mul, zero_add]
        have hmap : phi a ∈ J ^ (n + 1) :=
          ClassFieldTower.ProP.ringHom_mem_ideal_pow phi hphi (n + 1) ha
        let _ : (J ^ (n + 1)).IsTwoSided := inferInstance
        exact (J ^ (n + 1)).mul_mem_right _ hmap
      · intro a b ha hb
        rw [D.map_add]
        exact (J ^ (n + 1)).add_mem ha hb

/-- A continuous additive Fox operator lowers closed augmentation powers. -/
theorem mem_ideal_pow_closure_of_continuous_foxOperator
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (epsilon : A →+* R) (phi : A →+* B) (coeff : R →+* B)
    (D : A →+ B) (J : Ideal B) [J.IsTwoSided]
    (hphi : ∀ x ∈ RingHom.ker epsilon, phi x ∈ J)
    (hleibniz : ∀ x y,
      D (x * y) = coeff (epsilon y) * D x + phi x * D y)
    (hD : Continuous D) (n : ℕ) {x : A}
    (hx : x ∈ (RingHom.ker epsilon ^ (n + 1)).closure) :
    D x ∈ (J ^ n).closure := by
  have himage : ∀ y ∈ RingHom.ker epsilon ^ (n + 1), D y ∈ (J ^ n).closure := by
    intro y hy
    exact subset_closure
      (mem_ideal_pow_of_foxOperator epsilon phi coeff D J hphi hleibniz n hy)
  have hclosure := map_mem_closure
    (f := D) (s := (RingHom.ker epsilon ^ (n + 1) : Ideal A))
    (t := ((J ^ n).closure : Ideal B)) hD hx himage
  have hclosed : IsClosed (((J ^ n).closure : Ideal B) : Set B) := by
    exact Submodule.isClosed_topologicalClosure (J ^ n)
  rw [hclosed.closure_eq] at hclosure
  exact hclosure

/-- The closed filtration drop is compatible with changing a representative by
one deeper source layer.  This is the exact congruence needed for the induced
graded Fox/Jacobian map. -/
theorem foxOperator_initialForm_congr
    [TopologicalSpace A] [IsTopologicalRing A]
    [TopologicalSpace B] [IsTopologicalRing B]
    (epsilon : A →+* R) (phi : A →+* B) (coeff : R →+* B)
    (D : A →+ B) (J : Ideal B) [J.IsTwoSided]
    (hphi : ∀ x ∈ RingHom.ker epsilon, phi x ∈ J)
    (hleibniz : ∀ x y,
      D (x * y) = coeff (epsilon y) * D x + phi x * D y)
    (hD : Continuous D) (n : ℕ) {x y : A}
    (hxy : x - y ∈ (RingHom.ker epsilon ^ (n + 2)).closure) :
    D x - D y ∈ (J ^ (n + 1)).closure := by
  rw [← D.map_sub]
  simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
    mem_ideal_pow_closure_of_continuous_foxOperator
      epsilon phi coeff D J hphi hleibniz hD (n + 1) hxy

end

end ClassFieldTower.ProP
