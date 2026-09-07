import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.DiscreteQuotient
import Mathlib.Topology.Separation.Profinite
import ProCGroups.InverseSystems.CofinalityAndDensity

set_option autoImplicit false

/-!
# Profinite spaces as limits of finite discrete quotients

Clopen equivalence relations on a compact Hausdorff totally disconnected space form an inverse
system of finite discrete quotients.  This module constructs the canonical homeomorphism from
the space to that inverse limit and also proves the clopen-basis criterion used in the converse
direction.
-/

open scoped Topology

namespace ProCGroups.InverseSystems

universe u v w

/-- A compact Hausdorff totally disconnected space has a basis of clopen sets. -/
theorem isTopologicalBasis_isClopen_of_compact_t2_totallyDisconnected {X : Type w}
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] :
    TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s} :=
  isTopologicalBasis_isClopen

/-- Every open neighborhood in a profinite space contains a clopen neighborhood of the point. -/
theorem exists_clopen_subset_of_mem_open {X : Type w} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    {x : X} {U : Set X} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ U :=
  compact_exists_isClopen_in_isOpen hU hx

/-- The inverse system of all discrete quotients of \(X\). -/
def discreteQuotientSystem (X : Type w) [TopologicalSpace X] :
    InverseSystem (I := OrderDual (DiscreteQuotient X)) where
  X := fun Q => Quotient (show DiscreteQuotient X from Q).toSetoid
  topologicalSpace := fun _ => inferInstance
  map := fun {Q R} h => DiscreteQuotient.ofLE h
  continuous_map := fun {Q R} _ => continuous_of_discreteTopology
  map_id := fun Q => by
    funext x
    exact DiscreteQuotient.ofLE_refl_apply (A := (Q : DiscreteQuotient X)) x
  map_comp := fun {Q R T} hQR hRT => by
    funext x
    exact congrFun (DiscreteQuotient.ofLE_comp_ofLE hRT hQR) x

/-- The discrete quotient projections form a compatible family of maps. -/
private theorem compatibleMaps_discreteQuotientProj (X : Type w) [TopologicalSpace X] :
    (discreteQuotientSystem X).CompatibleMaps
      (fun Q : OrderDual (DiscreteQuotient X) => (Q : DiscreteQuotient X).proj) := by
  intro Q R h
  funext x
  exact DiscreteQuotient.ofLE_proj h x

/-- A compact Hausdorff totally disconnected space is profinite. -/
noncomputable def homeomorph_inverseLimit_discreteQuotientSystem (X : Type w)
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X] :
    X ≃ₜ (discreteQuotientSystem X).inverseLimit := by
  let S : InverseSystem (I := OrderDual (DiscreteQuotient X)) := discreteQuotientSystem X
  letI : ∀ Q : OrderDual (DiscreteQuotient X), T2Space (S.X Q) := fun Q => by
    change T2Space (Quotient (show DiscreteQuotient X from Q).toSetoid)
    infer_instance
  let f : X → S.inverseLimit :=
    S.inverseLimitLift (fun Q : OrderDual (DiscreteQuotient X) => (Q : DiscreteQuotient X).proj)
      (compatibleMaps_discreteQuotientProj X)
  have hf_continuous : Continuous f :=
    S.continuous_inverseLimitLift (fun Q : OrderDual (DiscreteQuotient X) => (Q :
        DiscreteQuotient X).proj)
      (fun Q => (Q : DiscreteQuotient X).proj_continuous) (compatibleMaps_discreteQuotientProj X)
  have hf_inj : Function.Injective f := by
    intro x y hxy
    exact DiscreteQuotient.eq_of_forall_proj_eq fun Q => by
      have hQ := congrArg (fun z => S.projection (show OrderDual (DiscreteQuotient X) from Q) z) hxy
      change (show DiscreteQuotient X from Q).proj x =
        (show DiscreteQuotient X from Q).proj y at hQ
      exact hQ
  have hf_surj : Function.Surjective f := by
    intro y
    let qs : (Q : DiscreteQuotient X) → Q := fun Q => S.projection (show OrderDual
        (DiscreteQuotient X) from Q) y
    have hqs :
        ∀ (A B : DiscreteQuotient X) (h : A ≤ B), DiscreteQuotient.ofLE h (qs A) = qs B := by
      intro A B h
      have hcompat :=
        S.projection_compatible y (show OrderDual (DiscreteQuotient X) from B)
          (show OrderDual (DiscreteQuotient X) from A) h
      change DiscreteQuotient.ofLE h (qs A) = qs B at hcompat
      exact hcompat
    rcases DiscreteQuotient.exists_of_compat qs hqs with ⟨x, hx⟩
    refine ⟨x, S.ext ?_⟩
    intro Q
    have hQ := hx (show DiscreteQuotient X from Q)
    change (show DiscreteQuotient X from Q).proj x =
      qs (show DiscreteQuotient X from Q)
    exact hQ
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩) hf_continuous

/--
The homeomorphism from a compact Hausdorff totally disconnected space to the inverse limit of
its discrete quotients has \(Q\)-coordinate equal to the quotient projection of the point.
-/
@[simp] theorem discreteQuotientSystem_projection_homeomorph (X : Type w)
    [TopologicalSpace X] [CompactSpace X] [T2Space X] [TotallyDisconnectedSpace X]
    (Q : OrderDual (DiscreteQuotient X)) (x : X) :
    (discreteQuotientSystem X).projection Q
        (homeomorph_inverseLimit_discreteQuotientSystem X x) =
      (show DiscreteQuotient X from Q).proj x := by
  let S := discreteQuotientSystem X
  change (S.inverseLimitLift (fun Q : OrderDual (DiscreteQuotient X) =>
      (show DiscreteQuotient X from Q).proj)
      (compatibleMaps_discreteQuotientProj X) x).1 Q =
    (show DiscreteQuotient X from Q).proj x
  rfl

/-- A Hausdorff space with a clopen basis is totally disconnected. -/
theorem totallyDisconnectedSpace_of_t2_basis_clopen (X : Type w) [TopologicalSpace X] [T2Space X]
    (hX : TopologicalSpace.IsTopologicalBasis {s : Set X | IsClopen s}) :
    TotallyDisconnectedSpace X := by
  let _ : TotallySeparatedSpace X := totallySeparatedSpace_of_t0_of_basis_clopen hX
  infer_instance

end ProCGroups.InverseSystems
