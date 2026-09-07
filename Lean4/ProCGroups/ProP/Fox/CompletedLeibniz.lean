import Mathlib.Topology.Algebra.Algebra
import ProCGroups.CompletedGroupAlgebra.UniversalProperty.Basic

set_option autoImplicit false
/-!
# Extending the Fox--Leibniz rule to completed group algebras

A continuous linear map out of a completed group algebra is determined by its
values on completed group-like elements.  Applying this uniqueness principle
in each variable extends a crossed-product identity on the underlying group to
the right Fox--Leibniz rule on the whole completed group algebra.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CompletedGroupAlgebra
open ProCGroups

noncomputable section

universe u v w

/-- Left multiplication in a topological algebra, as a continuous linear
map. -/
private def foxMulLeftContinuousLinearMap
    {R : Type u} [CommRing R]
    {A : Type w} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [Algebra R A] (a : A) : A →L[R] A where
  toLinearMap := LinearMap.mulLeft R a
  cont := continuous_const.mul continuous_id

/-- Right multiplication in a topological algebra, as a continuous linear
map. -/
private def foxMulRightContinuousLinearMap
    {R : Type u} [CommRing R]
    {A : Type w} [Ring A] [TopologicalSpace A] [IsTopologicalRing A]
    [Algebra R A] (a : A) : A →L[R] A where
  toLinearMap := LinearMap.mulRight R a
  cont := continuous_id.mul continuous_const

/-- A continuous linear extension of a crossed map on completed group-like
elements satisfies the right Fox--Leibniz rule on the whole completed group
algebra. -/
theorem completedGroupAlgebra_rightFoxLeibniz_of_groupLike
    (R : ProfiniteCommRing.{u}) (G : ProfiniteGrp.{v})
    {B : Type w} [Ring B] [TopologicalSpace B] [IsTopologicalRing B]
    [Algebra R B] [ContinuousSMul R B] [T2Space B]
    (epsilon : CompletedGroupAlgebraCarrier R G →A[R] R)
    (phi : CompletedGroupAlgebraCarrier R G →A[R] B)
    (D : CompletedGroupAlgebraCarrier R G →L[R] B)
    (hepsilon : ∀ g : G,
      epsilon (completedGroupAlgebraOf R G g) = 1)
    (hcrossed : ∀ g h : G,
      D (completedGroupAlgebraOf R G (g * h)) =
        D (completedGroupAlgebraOf R G g) +
          phi (completedGroupAlgebraOf R G g) *
            D (completedGroupAlgebraOf R G h)) :
    ∀ x y : CompletedGroupAlgebraCarrier R G,
      D (x * y) =
        algebraMap R B (epsilon y) * D x + phi x * D y := by
  let ofG : G → CompletedGroupAlgebraCarrier R G :=
    completedGroupAlgebraOf R G
  have hleft (g : G) : ∀ y : CompletedGroupAlgebraCarrier R G,
      D (ofG g * y) = epsilon y • D (ofG g) + phi (ofG g) * D y := by
    let F : CompletedGroupAlgebraCarrier R G →L[R] B :=
      D ∘L foxMulLeftContinuousLinearMap (R := R) (ofG g)
    let K : CompletedGroupAlgebraCarrier R G →L[R] B :=
      Add.add (epsilon.toContinuousLinearMap.smulRight (D (ofG g)))
        (foxMulLeftContinuousLinearMap (R := R) (phi (ofG g)) ∘L D)
    have hFK : F = K := by
      apply completedGroupAlgebraContinuousLinearMap_ext_of_basis
        (R := R) (G := G)
      intro h
      change D (ofG g * ofG h) =
        epsilon (ofG h) • D (ofG g) + phi (ofG g) * D (ofG h)
      rw [← completedGroupAlgebraOf_mul, hepsilon, one_smul]
      exact hcrossed g h
    intro y
    exact DFunLike.congr_fun hFK y
  intro x y
  let F : CompletedGroupAlgebraCarrier R G →L[R] B :=
    D ∘L foxMulRightContinuousLinearMap (R := R) y
  let K : CompletedGroupAlgebraCarrier R G →L[R] B :=
    Add.add (epsilon y • D)
      (foxMulRightContinuousLinearMap (R := R) (D y) ∘L
        phi.toContinuousLinearMap)
  have hFK : F = K := by
    apply completedGroupAlgebraContinuousLinearMap_ext_of_basis
      (R := R) (G := G)
    intro g
    exact hleft g y
  have hx := DFunLike.congr_fun hFK x
  change D (x * y) = epsilon y • D x + phi x * D y at hx
  simpa only [Algebra.smul_def] using hx

end

end ClassFieldTower.ProP
