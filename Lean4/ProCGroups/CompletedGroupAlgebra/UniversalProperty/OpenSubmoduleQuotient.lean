import ProCGroups.CompletedGroupAlgebra.UniversalProperty.FiniteQuotient

set_option autoImplicit false

/-!
# Lifts to open-submodule quotients

The finite-quotient universal property yields a unique continuous linear lift to the quotient of a
profinite module by an open submodule. This file constructs the lift and records its value on
group-like generators and its factorization formula.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (R : ProfiniteCommRing.{u})
variable (G : ProfiniteGrp.{v})

local instance (N : ProfiniteModule.{u, w} R.toProfiniteRing) : Module R N :=
  N.module

local instance (N : ProfiniteModule.{u, w} R.toProfiniteRing) :
    ContinuousSMul R N :=
  N.continuousSMul

/--
The quotient-target form of the existence step in Lemma 5.3.5(d): after quotienting a profinite
target module by an open submodule, the prescribed continuous map from \(G\) extends uniquely
from \(\widehat{R[G]}\).
-/
theorem completedGroupAlgebra_existsUnique_lift_to_openSubmoduleQuotient
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f)
    (W : Submodule R N) (hW : IsOpen (W : Set N)) :
    ∃! F : CompletedGroupAlgebraCarrier R G →L[R] N ⧸ W,
      ∀ g : G, F (completedGroupAlgebraOf R G g) = Submodule.mkQ W (f g) := by
  let hdisc : IsDiscreteModule R (N ⧸ W) :=
    quotient_openSubmodule_isDiscreteModule R N W hW
  let : IsTopologicalAddGroup (N ⧸ W) := hdisc.1.2.1
  let : ContinuousSMul R (N ⧸ W) := hdisc.1.2.2
  let : DiscreteTopology (N ⧸ W) := hdisc.2
  have hqcont : Continuous (Submodule.mkQ W : N → N ⧸ W) := by
    change Continuous (Submodule.Quotient.mk (p := W))
    exact continuous_quotient_mk'
  rcases exists_completedGroupAlgebraIndex_factor_continuous_discrete
      (G := G) (N ⧸ W) (fun g : G => Submodule.mkQ W (f g))
      (hqcont.comp hf) with
    ⟨U, fbar, hfac⟩
  exact completedGroupAlgebra_existsUnique_lift_of_factors (R := R) (G := G) (N ⧸ W)
    U (fun g : G => Submodule.mkQ W (f g)) fbar hfac

/-- The chosen quotient-valued extension attached to an open submodule of a profinite target. -/
def completedGroupAlgebraLiftToOpenSubmoduleQuotient
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f)
    (W : Submodule R N) (hW : IsOpen (W : Set N)) :
    CompletedGroupAlgebraCarrier R G →L[R] N ⧸ W :=
  Classical.choose
    (completedGroupAlgebra_existsUnique_lift_to_openSubmoduleQuotient
      (R := R) (G := G) N f hf W hW)

/-- The quotient-valued lift has the prescribed value on completed group-like elements. -/
@[simp]
theorem completedGroupAlgebraLiftToOpenSubmoduleQuotient_apply_of
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f)
    (W : Submodule R N) (hW : IsOpen (W : Set N)) (g : G) :
    completedGroupAlgebraLiftToOpenSubmoduleQuotient
        (R := R) (G := G) N f hf W hW
        (completedGroupAlgebraOf R G g) =
      Submodule.mkQ W (f g) := by
  exact (Classical.choose_spec
    (completedGroupAlgebra_existsUnique_lift_to_openSubmoduleQuotient
      (R := R) (G := G) N f hf W hW)).1 g

/-- The quotient-valued extensions are compatible with refinement of open submodules. -/
theorem completedGroupAlgebraLiftToOpenSubmoduleQuotient_factor
    (N : ProfiniteModule.{u, w} R.toProfiniteRing)
    (f : G → N) (hf : Continuous f)
    {W V : Submodule R N} (hWV : W ≤ V)
    (hW : IsOpen (W : Set N)) (hV : IsOpen (V : Set N))
    (x : CompletedGroupAlgebraCarrier R G) :
    Submodule.factor hWV
        (completedGroupAlgebraLiftToOpenSubmoduleQuotient
          (R := R) (G := G) N f hf W hW x) =
      completedGroupAlgebraLiftToOpenSubmoduleQuotient
        (R := R) (G := G) N f hf V hV x := by
  let hdiscV : IsDiscreteModule R (N ⧸ V) :=
    quotient_openSubmodule_isDiscreteModule R N V hV
  let hdiscW : IsDiscreteModule R (N ⧸ W) :=
    quotient_openSubmodule_isDiscreteModule R N W hW
  let : DiscreteTopology (N ⧸ W) := hdiscW.2
  let : DiscreteTopology (N ⧸ V) := hdiscV.2
  let factorCLM : N ⧸ W →L[R] N ⧸ V :=
    { toLinearMap := Submodule.factor hWV
      cont := continuous_of_discreteTopology }
  have hEq :
      factorCLM.comp
          (completedGroupAlgebraLiftToOpenSubmoduleQuotient
            (R := R) (G := G) N f hf W hW) =
        completedGroupAlgebraLiftToOpenSubmoduleQuotient
          (R := R) (G := G) N f hf V hV := by
    apply completedGroupAlgebraContinuousLinearMap_ext_of_basis (R := R) (G := G)
    intro g
    change Submodule.factor hWV
        (completedGroupAlgebraLiftToOpenSubmoduleQuotient
          (R := R) (G := G) N f hf W hW
          (completedGroupAlgebraOf R G g)) =
      completedGroupAlgebraLiftToOpenSubmoduleQuotient
        (R := R) (G := G) N f hf V hV
        (completedGroupAlgebraOf R G g)
    rw [completedGroupAlgebraLiftToOpenSubmoduleQuotient_apply_of,
      completedGroupAlgebraLiftToOpenSubmoduleQuotient_apply_of,
      Submodule.factor_mk]
  exact congrArg (fun F : CompletedGroupAlgebraCarrier R G →L[R] N ⧸ V => F x) hEq
end

end CompletedGroupAlgebra
