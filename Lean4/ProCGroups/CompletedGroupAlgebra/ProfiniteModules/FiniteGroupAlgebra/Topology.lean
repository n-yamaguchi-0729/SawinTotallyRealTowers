import ProCGroups.CompletedGroupAlgebra.ProfiniteModules.Basic.OpenIdeals
import Mathlib.GroupTheory.FiniteAbelian.Basic

set_option autoImplicit false

/-!
# Topology and universal maps for finite group algebras

A finite group algebra over a profinite coefficient ring is identified with a finite product of
coefficients and given its profinite ring topology. This file proves continuity of its operations
and constructs continuous linear lifts from basis data.
-/

open scoped Topology
open ProCGroups

namespace CompletedGroupAlgebra

universe u v w

/--
The product topology on the group algebra of a finite group, transported through \(R[G] = G
\to_0 R \simeq G \to R\). This is the finite stage used in the construction of the completed
group algebra.
-/
@[reducible]
noncomputable def finiteGroupAlgebraTopology
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R] :
    TopologicalSpace (MonoidAlgebra R G) :=
  TopologicalSpace.induced
    ((MonoidAlgebra.coeffEquiv (R := R) (M := G)).trans
      Finsupp.equivFunOnFinite : MonoidAlgebra R G ≃ (G → R))
    inferInstance

private noncomputable def finiteGroupAlgebraHomeomorphCore
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    [topology : TopologicalSpace (MonoidAlgebra R G)]
    (htopology : topology = finiteGroupAlgebraTopology R G) :
    MonoidAlgebra R G ≃ₜ (G → R) := by
  let e : MonoidAlgebra R G ≃ (G → R) :=
    (MonoidAlgebra.coeffEquiv (R := R) (M := G)).trans Finsupp.equivFunOnFinite
  apply e.toHomeomorphOfIsInducing
  rw [htopology]
  exact Topology.IsInducing.induced e

private noncomputable def finiteGroupAlgebraContinuousLinearEquivPiCore
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    [topology : TopologicalSpace (MonoidAlgebra R G)]
    (htopology : topology = finiteGroupAlgebraTopology R G) :
    MonoidAlgebra R G ≃L[R] (G → R) := by
  exact ContinuousLinearEquiv.mk
    ((MonoidAlgebra.coeffLinearEquiv R).trans
      (Finsupp.linearEquivFunOnFinite R R G))
    (finiteGroupAlgebraHomeomorphCore R G htopology).continuous
    (finiteGroupAlgebraHomeomorphCore R G htopology).symm.continuous

/--
The finite group algebra with its transported product topology is homeomorphic to the function
space \(G \to R\).
-/
noncomputable def finiteGroupAlgebraHomeomorph
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    MonoidAlgebra R G ≃ₜ (G → R) :=
  finiteGroupAlgebraHomeomorphCore R G
    (topology := finiteGroupAlgebraTopology R G) rfl

/--
The finite-stage group algebra is the finite product of copies of the coefficient ring as a
topological \(R\)-module.
-/
noncomputable def finiteGroupAlgebraContinuousLinearEquivPi
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    MonoidAlgebra R G ≃L[R] (G → R) :=
  finiteGroupAlgebraContinuousLinearEquivPiCore R G
    (topology := finiteGroupAlgebraTopology R G) rfl

/-- The continuous equivalence is evaluated by the corresponding comparison formula. -/
@[simp]
theorem finiteGroupAlgebraContinuousLinearEquivPi_apply
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    (x : MonoidAlgebra R G) :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    finiteGroupAlgebraContinuousLinearEquivPi R G x =
      Finsupp.equivFunOnFinite x.coeff :=
  rfl

/--
Coordinate evaluation on a finite group algebra is continuous for the transported product
topology.
-/
theorem finiteGroupAlgebra_coordinate_continuous
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ∀ g : G, Continuous fun x : MonoidAlgebra R G => x.coeff g := by
  let : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  intro g
  exact (continuous_apply g).comp (finiteGroupAlgebraHomeomorph R G).continuous

/-- Addition is continuous for the finite-stage group algebra topology. -/
theorem finiteGroupAlgebra_continuousAdd
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ContinuousAdd (MonoidAlgebra R G) := by
  let : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  exact continuousAdd_induced
    ((MonoidAlgebra.coeffLinearEquiv R).trans
      (Finsupp.linearEquivFunOnFinite R R G))

/-- Negation is continuous for the finite-stage group algebra topology. -/
theorem finiteGroupAlgebra_continuousNeg
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ContinuousNeg (MonoidAlgebra R G) := by
  let : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let e : MonoidAlgebra R G ≃ₗ[R] (G → R) :=
    (MonoidAlgebra.coeffLinearEquiv R).trans (Finsupp.linearEquivFunOnFinite R R G)
  exact (finiteGroupAlgebraHomeomorph R G).isInducing.continuousNeg
    (fun x => map_neg e x)

/--
Multiplication is continuous for the finite-stage group algebra topology. The coordinate formula
is the finite convolution sum over pairs (g1,g2) with \(g1*g2 = g\).
-/
theorem finiteGroupAlgebra_continuousMul
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ContinuousMul (MonoidAlgebra R G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  have hcoord := finiteGroupAlgebra_coordinate_continuous R G
  refine ⟨?_⟩
  apply (finiteGroupAlgebraHomeomorph R G).isInducing.continuous_iff.mpr
  apply continuous_pi
  intro g
  exact (continuous_finsetSum
    (Finset.univ.filter (fun q : G × G => q.1 * q.2 = g))
    (fun q _hq =>
      ((hcoord q.1).comp continuous_fst).mul ((hcoord q.2).comp continuous_snd))).congr
    (fun p => (MonoidAlgebra.coeff_mul_antidiag p.1 p.2 g
      (Finset.univ.filter (fun q : G × G => q.1 * q.2 = g))
      (by intro q; simp only [Finset.mem_filter, Finset.mem_univ, true_and])).symm)

/--
Scalar multiplication by the coefficient ring is continuous on the finite-stage group algebra
topology.
-/
theorem finiteGroupAlgebra_continuousSMul
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    ContinuousSMul R (MonoidAlgebra R G) := by
  let : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  exact continuousSMul_induced
    ((MonoidAlgebra.coeffLinearEquiv R).trans
      (Finsupp.linearEquivFunOnFinite R R G))

/-- The finite-stage group algebra topology makes \(R[G]\) a topological ring. -/
theorem finiteGroupAlgebra_isTopologicalRing
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G] [TopologicalSpace R]
    [IsTopologicalRing R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    IsTopologicalRing (MonoidAlgebra R G) := by
  let : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  exact
    { toIsTopologicalSemiring :=
        { toContinuousAdd := finiteGroupAlgebra_continuousAdd R G
          toContinuousMul := finiteGroupAlgebra_continuousMul R G }
      toContinuousNeg := finiteGroupAlgebra_continuousNeg R G }

/-- Compactness of the coefficient ring passes to a finite-stage group algebra. -/
theorem finiteGroupAlgebra_compactSpace
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    [CompactSpace R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    CompactSpace (MonoidAlgebra R G) := by
  let : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  exact Homeomorph.compactSpace (finiteGroupAlgebraHomeomorph R G).symm

/-- The Hausdorff property of the coefficient ring passes to a finite-stage group algebra. -/
theorem finiteGroupAlgebra_t2Space
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    [T2Space R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    T2Space (MonoidAlgebra R G) := by
  let : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  exact Homeomorph.t2Space (finiteGroupAlgebraHomeomorph R G).symm

/-- Total disconnectedness of the coefficient ring passes to a finite-stage group algebra. -/
theorem finiteGroupAlgebra_totallyDisconnectedSpace
    (R : Type u) (G : Type v) [CommRing R] [Finite G] [TopologicalSpace R]
    [TotallyDisconnectedSpace R] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    TotallyDisconnectedSpace (MonoidAlgebra R G) := by
  let : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  exact Homeomorph.totallyDisconnectedSpace (finiteGroupAlgebraHomeomorph R G).symm

/--
The finite function-space lift sends a coefficient function to the finite sum of its
coefficients acting on the prescribed values.
-/
private noncomputable def finiteGroupAlgebraPiLift
    (R : Type u) (G : Type v) (N : Type w)
    [Ring R] [TopologicalSpace R] [Fintype G]
    [AddCommGroup N] [TopologicalSpace N] [Module R N] [ContinuousAdd N] [ContinuousSMul R N]
    (f : G -> N) : (G -> R) →L[R] N where
  toLinearMap :=
    { toFun := fun m => ∑ x : G, m x • f x
      map_add' := by
        intro m n
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro lam m
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply, Finset.smul_sum]}
  cont := by
    apply continuous_finsetSum
    intro x _hx
    exact (continuous_apply x).smul continuous_const

/--
The finite function-space lift sends the basis function \(\mathrm{Pi.single}\ g\ 1\) to
\(f(g)\).
-/
private theorem finiteGroupAlgebraPiLift_apply_basis
    (R : Type u) (G : Type v) (N : Type w)
    [Ring R] [TopologicalSpace R] [Fintype G] [DecidableEq G]
    [AddCommGroup N] [TopologicalSpace N] [Module R N] [ContinuousAdd N] [ContinuousSMul R N]
    (f : G -> N) (g : G) :
    finiteGroupAlgebraPiLift R G N f (Pi.single g (1 : R)) = f g := by
  simp only [finiteGroupAlgebraPiLift, ContinuousLinearMap.coe_mk', LinearMap.coe_mk, AddHom.coe_mk,
    Pi.single_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
    ↓reduceIte]

private noncomputable def finiteGroupAlgebraLiftCore
    (R : Type u) (G : Type v) (N : Type w) [CommRing R] [Finite G]
    [TopologicalSpace R] [AddCommGroup N] [TopologicalSpace N] [Module R N]
    [ContinuousAdd N] [ContinuousSMul R N]
    [topology : TopologicalSpace (MonoidAlgebra R G)]
    (htopology : topology = finiteGroupAlgebraTopology R G) (f : G → N) :
    MonoidAlgebra R G →L[R] N := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  exact (finiteGroupAlgebraPiLift R G N f).comp
    (finiteGroupAlgebraContinuousLinearEquivPiCore R G htopology).toContinuousLinearMap

/--
A continuous linear map out of a finite group algebra is determined by its values on group
elements.
-/
noncomputable def finiteGroupAlgebraLift
    (R : Type u) (G : Type v) (N : Type w) [CommRing R] [Finite G]
    [TopologicalSpace R] [AddCommGroup N] [TopologicalSpace N] [Module R N]
    [ContinuousAdd N] [ContinuousSMul R N] (f : G → N) :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    MonoidAlgebra R G →L[R] N :=
  finiteGroupAlgebraLiftCore R G N
    (topology := finiteGroupAlgebraTopology R G) rfl f

/-- The finite group-algebra lift sends the group-like basis vector at \(g\) to \(f(g)\). -/
@[simp]
theorem finiteGroupAlgebraLift_apply_of
    (R : Type u) (G : Type v) (N : Type w) [CommRing R] [Group G] [Finite G]
    [TopologicalSpace R] [AddCommGroup N] [TopologicalSpace N] [Module R N]
    [ContinuousAdd N] [ContinuousSMul R N] (f : G → N) (g : G) :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    finiteGroupAlgebraLift R G N f (MonoidAlgebra.of R G g) = f g := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  rw [show MonoidAlgebra.of R G g =
    (MonoidAlgebra.single g 1 : MonoidAlgebra R G) by rfl]
  unfold finiteGroupAlgebraLift finiteGroupAlgebraLiftCore
  change
    finiteGroupAlgebraPiLift R G N f
        (finiteGroupAlgebraContinuousLinearEquivPi R G
          (MonoidAlgebra.single g 1)) =
      f g
  rw [finiteGroupAlgebraContinuousLinearEquivPi_apply]
  rw [MonoidAlgebra.coeff_single]
  rw [Finsupp.equivFunOnFinite_single]
  exact finiteGroupAlgebraPiLift_apply_basis R G N f g

end CompletedGroupAlgebra
