import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.System.AddCommGroup

set_option autoImplicit false

/-!
# Fox differential: coefficient rings — mod-\(n\) completed group algebra — system — completion map

The principal declarations in this module are:

- `toModNCompletedGroupAlgebra`
  The canonical map \((\mathbb{Z}/n\mathbb{Z})[G] \to \varprojlim_U (\mathbb{Z}/n\mathbb{Z})[G/U]\).
- `modNCompletedGroupAlgebraStageMap_compatibleMaps`
  The mod-\(n\) completed group-algebra stage maps are compatible with transition maps and
  coordinate projections.
- `modNCompletedGroupAlgebraProjection_toCompleted`
  The finite-stage projection to the completed mod-\(n\) group algebra is given by the corresponding
  coordinate formula.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u


variable (n : ℕ) [Fact (0 < n)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [Fact (0 < n)] in
/--
The mod-\(n\) completed group-algebra stage maps are compatible with transition maps and
coordinate projections.
-/
theorem modNCompletedGroupAlgebraStageMap_compatibleMaps :
    (modNCompletedGroupAlgebraSystem n G).CompatibleMaps
      (fun U => modNCompletedGroupAlgebraStageMap n G U) := by
  intro U V hUV
  funext x
  exact congrFun
    (congrArg DFunLike.coe
      (modNCompletedGroupAlgebraStageMap_compatible (n := n) (G := G) (U := U) (V := V) hUV))
    x

/--
The canonical map \((\mathbb{Z}/n\mathbb{Z})[G] \to \varprojlim_U
(\mathbb{Z}/n\mathbb{Z})[G/U]\).
-/
def toModNCompletedGroupAlgebra :
    ModNCompletedGroupRing n G → ModNCompletedGroupAlgebra n G := by
  letI : TopologicalSpace (ModNCompletedGroupRing n G) := ⊥
  exact
    (modNCompletedGroupAlgebraSystem n G).inverseLimitLift
      (fun U => modNCompletedGroupAlgebraStageMap n G U)
      (modNCompletedGroupAlgebraStageMap_compatibleMaps (n := n) (G := G))

omit [Fact (0 < n)] in
/--
The finite-stage projection to the completed mod-\(n\) group algebra is given by the
corresponding coordinate formula.
-/
@[simp]
theorem modNCompletedGroupAlgebraProjection_toCompleted
    (U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) (x : ModNCompletedGroupRing
        n G) :
    modNCompletedGroupAlgebraProjection n G U (toModNCompletedGroupAlgebra n G x) =
      modNCompletedGroupAlgebraStageMap n G U x := by
  rfl

end

end FoxDifferential
