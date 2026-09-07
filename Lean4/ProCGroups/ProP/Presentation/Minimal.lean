import ProCGroups.ProP.FrattiniQuotient
import ProCGroups.ProP.Presentation.Basic

set_option autoImplicit false
/-!
# Minimal pro-p presentations

Minimality means that the presentation kernel lies in the source
power--commutator core.  The quotient therefore descends the source Frattini
quotient to a continuous surjection from the target.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open ProCGroups
open ProCGroups.Presentations

noncomputable section

universe u

namespace FiniteProPPresentation

variable {p d r : ℕ} [Fact p.Prime]
variable {sourceData :
  FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u}
    (FiniteGroupClass.pGroup p)}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

local instance : (closedPowerCommutator p sourceData.carrier).Normal :=
  closedPowerCommutator_normal p sourceData.carrier

/-- A finite presentation is minimal when its kernel lies in the source
Frattini power--commutator core. -/
def IsMinimal (P : FiniteProPPresentation p d r sourceData G) : Prop :=
  P.quotient.toMonoidHom.ker ≤ closedPowerCommutator p sourceData.carrier

/-- Every displayed relator of a minimal presentation lies in the source
power--commutator core. -/
theorem relator_mem_closedPowerCommutator
    (P : FiniteProPPresentation p d r sourceData G)
    (hP : P.IsMinimal) (i : Fin r) :
    P.relator i ∈ closedPowerCommutator p sourceData.carrier :=
  hP (P.relator_mem_kernel i)

/-- A minimal quotient descends the source Frattini quotient map back from the
target. -/
noncomputable def targetToSourcePowerCommutatorQuotient
    (P : FiniteProPPresentation p d r sourceData G) (hP : P.IsMinimal) :
    G →ₜ* powerCommutatorQuotient p sourceData.carrier := by
  let q := powerCommutatorQuotientMk p sourceData.carrier
  have hker : P.quotient.toMonoidHom.ker ≤ q.toMonoidHom.ker := by
    rw [ker_powerCommutatorQuotientMk]
    exact hP
  let φ : G →* powerCommutatorQuotient p sourceData.carrier :=
    (P.quotient.toMonoidHom.liftOfSurjective P.quotient_surjective)
      ⟨q.toMonoidHom, hker⟩
  have hφcomp : φ.comp P.quotient.toMonoidHom = q.toMonoidHom := by
    ext x
    exact
      MonoidHom.liftOfRightInverse_comp_apply
        (f := P.quotient.toMonoidHom)
        (f_inv := Function.surjInv P.quotient_surjective)
        (Function.rightInverse_surjInv P.quotient_surjective)
        ⟨q.toMonoidHom, hker⟩ x
  have hcomp_continuous : Continuous fun x : sourceData.carrier =>
      φ (P.quotient x) := by
    convert q.continuous_toFun using 1
    funext x
    exact MonoidHom.ext_iff.mp hφcomp x
  exact
    { toMonoidHom := φ
      continuous_toFun :=
        (Topology.IsQuotientMap.of_surjective_continuous
          P.quotient_surjective P.quotient.continuous_toFun).continuous_iff.2
            hcomp_continuous }

/-- The descended map agrees with the source Frattini quotient on presentation
lifts. -/
@[simp] theorem targetToSourcePowerCommutatorQuotient_apply
    (P : FiniteProPPresentation p d r sourceData G) (hP : P.IsMinimal)
    (x : sourceData.carrier) :
    P.targetToSourcePowerCommutatorQuotient hP (P.quotient x) =
      powerCommutatorQuotientMk p sourceData.carrier x := by
  change
    ((P.quotient.toMonoidHom.liftOfSurjective P.quotient_surjective)
      ⟨(powerCommutatorQuotientMk p sourceData.carrier).toMonoidHom, ?_⟩)
        (P.quotient x) = _
  · exact
      MonoidHom.liftOfRightInverse_comp_apply
        (f := P.quotient.toMonoidHom)
        (f_inv := Function.surjInv P.quotient_surjective)
        (Function.rightInverse_surjInv P.quotient_surjective)
        _ x

/-- The descended target-to-source Frattini quotient map is surjective. -/
theorem targetToSourcePowerCommutatorQuotient_surjective
    (P : FiniteProPPresentation p d r sourceData G) (hP : P.IsMinimal) :
    Function.Surjective (P.targetToSourcePowerCommutatorQuotient hP) := by
  intro y
  obtain ⟨x, rfl⟩ :=
    powerCommutatorQuotientMk_surjective p sourceData.carrier y
  exact
    ⟨P.quotient x, P.targetToSourcePowerCommutatorQuotient_apply hP x⟩

end FiniteProPPresentation

end


end ClassFieldTower.ProP
