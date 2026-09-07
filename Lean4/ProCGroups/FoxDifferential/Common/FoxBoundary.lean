import ProCGroups.FoxDifferential.Common.FreeCrossedDifferential

set_option autoImplicit false

/-!
# Fox differential: common — fox boundary

The principal declarations in this module are:

- `coefficientFoxBoundary`
  The Fox boundary crossed differential attached to a coefficient homomorphism: \(g \mapsto
  \operatorname{coeff}(g)-1\).
- `coefficientFoxBoundaryCrossedHom`
  The coefficient Fox boundary is a crossed differential.
- `coefficientFoxBoundary_one`
  The coefficient Fox boundary sends the identity to zero.
- `coefficientFoxBoundary_mul`
  Product rule for the coefficient Fox boundary \(g \mapsto \operatorname{coeff}(g)-1\).
-/

namespace FoxDifferential

noncomputable section

open scoped BigOperators

universe u v

section CoefficientBoundary

variable {R : Type u} [Ring R]
variable {G : Type v} [Group G]

/--
The Fox boundary crossed differential attached to a coefficient homomorphism: \(g \mapsto
\operatorname{coeff}(g)-1\).
-/
def coefficientFoxBoundary (coeff : G →* R) (g : G) : R :=
  coeff g - 1

/-- The coefficient Fox boundary sends the identity to zero. -/
@[simp]
theorem coefficientFoxBoundary_one (coeff : G →* R) :
    coefficientFoxBoundary coeff 1 = 0 := by
  simp only [coefficientFoxBoundary, map_one, sub_self]

/-- Product rule for the coefficient Fox boundary \(g \mapsto \operatorname{coeff}(g)-1\). -/
theorem coefficientFoxBoundary_mul (coeff : G →* R) (g h : G) :
    coefficientFoxBoundary coeff (g * h) =
      coefficientFoxBoundary coeff g + coeff g • coefficientFoxBoundary coeff h := by
  rw [coefficientFoxBoundary, coefficientFoxBoundary, coefficientFoxBoundary, map_mul]
  change coeff g * coeff h - 1 = coeff g - 1 + coeff g * (coeff h - 1)
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, mul_add, mul_neg, mul_one]
  rw [show coeff g + -1 + (coeff g * coeff h + -coeff g) =
      coeff g + -coeff g + (coeff g * coeff h + -1) by ac_rfl]
  simp only [add_neg_cancel, zero_add]

/-- The coefficient Fox boundary is a crossed differential. -/
def coefficientFoxBoundaryCrossedHom (coeff : G →* R) : ScalarCrossedHom coeff R where
  toFun := coefficientFoxBoundary coeff
  map_mul' := coefficientFoxBoundary_mul coeff

/-- The coefficient boundary crossed homomorphism sends a group element to its coefficient
minus one. -/
@[simp]
theorem coefficientFoxBoundaryCrossedHom_apply (coeff : G →* R) (g : G) :
    coefficientFoxBoundaryCrossedHom coeff g = coeff g - 1 :=
  rfl

end CoefficientBoundary

section BoundaryMap

variable {R : Type u} [Ring R]
variable {X : Type v} [Fintype X]

/--
The finite Fox boundary map with prescribed generator boundary values sends a coordinate vector
\(v : X \to R\) to \(\sum_x v(x)\,\mathrm{generatorBoundary}(x)\).
-/
def foxBoundaryMap (generatorBoundary : X → R) : (X → R) →ₗ[R] R where
  toFun v := ∑ x : X, v x * generatorBoundary x
  map_add' v w := by
    simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' r v := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply, Finset.mul_sum]

/--
The boundary map is evaluated on the canonical generators and then extended linearly to the
coordinate module.
-/
theorem foxBoundaryMap_apply (generatorBoundary : X → R) (v : X → R) :
    foxBoundaryMap generatorBoundary v =
      ∑ x : X, v x * generatorBoundary x :=
  rfl

variable [DecidableEq X]

/--
The finite Fox boundary map sends a coordinate basis vector to the corresponding generator
boundary.
-/
@[simp]
theorem foxBoundaryMap_single (generatorBoundary : X → R) (x : X) :
    foxBoundaryMap generatorBoundary (Pi.single x (1 : R)) = generatorBoundary x := by
  rw [foxBoundaryMap_apply]
  rw [Finset.sum_eq_single x]
  · simp only [Pi.single_eq_same, one_mul]
  · intro y _ hy
    simp only [Pi.single_eq_of_ne hy, zero_mul]
  · simp only [Finset.mem_univ, not_true_eq_false, Pi.single_eq_same, one_mul, IsEmpty.forall_iff]

end BoundaryMap

section FreeGroup

variable {R : Type u} [Ring R]
variable {X : Type v} [Fintype X] [DecidableEq X]
variable (coeff : FreeGroup X →* R)
variable (generatorBoundary : X → R)

/--
Boundary-map form of the generic free-group Fox formula: applying the Fox boundary map to the
free crossed differential recovers the crossed differential with the prescribed generator
values.
-/
theorem foxBoundaryMap_freeCrossedHomWithCoeff
    (boundary : ScalarCrossedHom coeff R)
    (hgenerator : ∀ x : X, boundary (FreeGroup.of x) = generatorBoundary x)
    (w : FreeGroup X) :
    foxBoundaryMap generatorBoundary
        (freeCrossedHomWithCoeff
          (A := X → R) coeff (fun x : X => Pi.single x (1 : R)) w) =
      boundary w := by
  let delta : ScalarCrossedHom coeff R :=
    ScalarCrossedHom.mapLinear
      (freeCrossedHomWithCoeff
        (A := X → R) coeff (fun x : X => Pi.single x (1 : R)))
      (foxBoundaryMap generatorBoundary)
  have hdelta_generator :
      ∀ x : X, delta (FreeGroup.of x) = generatorBoundary x := by
    intro x
    simp only [delta, ScalarCrossedHom.mapLinear_apply, freeCrossedHomWithCoeff_of,
      foxBoundaryMap_single]
  have hdelta_eq :
      delta = freeCrossedHomWithCoeff (A := R) coeff generatorBoundary :=
    freeCrossedHomWithCoeff_unique
      (A := R) coeff generatorBoundary delta hdelta_generator
  have hboundary_eq :
      boundary = freeCrossedHomWithCoeff (A := R) coeff generatorBoundary :=
    freeCrossedHomWithCoeff_unique
      (A := R) coeff generatorBoundary boundary hgenerator
  change delta w = boundary w
  rw [hdelta_eq, hboundary_eq]

/--
Conditional boundary-map form of the generic free-group Fox formula. Any crossed differential
with standard coordinate values satisfies the same boundary formula as the canonical free
crossed differential.
-/
theorem foxBoundaryMap_of_crossedHom
    (delta : ScalarCrossedHom coeff (X → R))
    (hdelta_generator :
      ∀ x : X, delta (FreeGroup.of x) = Pi.single x (1 : R))
    (boundary : ScalarCrossedHom coeff R)
    (hboundary_generator :
      ∀ x : X, boundary (FreeGroup.of x) = generatorBoundary x)
    (w : FreeGroup X) :
    foxBoundaryMap generatorBoundary (delta w) = boundary w := by
  have hdelta_eq :
      delta =
        freeCrossedHomWithCoeff
          (A := X → R) coeff (fun x : X => Pi.single x (1 : R)) :=
    freeCrossedHomWithCoeff_unique
      (A := X → R) coeff (fun x : X => Pi.single x (1 : R))
      delta hdelta_generator
  rw [hdelta_eq]
  exact foxBoundaryMap_freeCrossedHomWithCoeff
    coeff generatorBoundary boundary hboundary_generator w

/--
Explicit finite-sum form of the generic Fox--Euler formula for any crossed differential with
standard coordinate values: \(\mathrm{coeff}(w)-1=\sum_x \delta_x(w)(\mathrm{coeff}(x)-1)\).
-/
theorem foxEulerFormula_of_crossedHom
    (delta : ScalarCrossedHom coeff (X → R))
    (hdelta_generator :
      ∀ x : X, delta (FreeGroup.of x) = Pi.single x (1 : R))
    (w : FreeGroup X) :
    coeff w - 1 =
      ∑ x : X, delta w x * (coeff (FreeGroup.of x) - 1) := by
  have hboundary :=
    foxBoundaryMap_of_crossedHom
      coeff
      (fun x : X => coefficientFoxBoundary coeff (FreeGroup.of x))
      delta hdelta_generator
      (coefficientFoxBoundaryCrossedHom coeff)
      (by intro x; rfl)
      w
  simpa [coefficientFoxBoundary, foxBoundaryMap_apply] using hboundary.symm

end FreeGroup

end

end FoxDifferential
