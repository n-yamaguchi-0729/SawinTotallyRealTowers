import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.Augmentation

set_option autoImplicit false

/-!
# Fox differential: completed — coefficient rings — mod-\(n\) completed group algebra — augmentation ideal

The principal declarations in this module are:

- `modNCompletedGroupAlgebraStageAugmentationIdeal`
  The augmentation ideal on one residue-coefficient finite stage.
- `modNCompletedGroupAlgebraAugmentationKernel`
  The kernel of the canonical augmentation on the residue-coefficient completed group algebra.
- `mem_modNCompletedGroupAlgebraStageAugmentationIdeal_iff`
  Membership in a mod-\(N\) finite-stage augmentation ideal is equivalent to vanishing under the
  stage augmentation map.
- `mem_modNCompletedGroupAlgebraAugmentationKernel_iff`
  Membership in the relevant augmentation kernel or augmentation ideal is equivalent to the
  corresponding vanishing condition.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u


variable (n : ℕ) [Fact (0 < n)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section AugmentationIdeal

variable (n : ℕ) [Fact (0 < n)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The augmentation ideal on one residue-coefficient finite stage. -/
def modNCompletedGroupAlgebraStageAugmentationIdeal (U :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    Ideal (ModNCompletedGroupAlgebraStage n G U) :=
  RingHom.ker (modNCompletedGroupAlgebraStageAugmentation n G U)

/-- The kernel of the canonical augmentation on the residue-coefficient completed group algebra. -/
def modNCompletedGroupAlgebraAugmentationKernel :
    Set (ModNCompletedGroupAlgebra n G) :=
  {x | modNCompletedGroupAlgebraAugmentation n G x = 0}

/-- The kernel of the canonical augmentation is viewed as a subtype. -/
abbrev ModNCompletedGroupAlgebraAugmentationKernel :=
  {x : ModNCompletedGroupAlgebra n G // x ∈ modNCompletedGroupAlgebraAugmentationKernel n G}

omit [Fact (0 < n)] in
variable {n G} in
/--
Membership in a mod-\(N\) finite-stage augmentation ideal is equivalent to vanishing under the
stage augmentation map.
-/
@[simp]
theorem mem_modNCompletedGroupAlgebraStageAugmentationIdeal_iff
    {U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} {x :
        ModNCompletedGroupAlgebraStage n G U} :
    x ∈ modNCompletedGroupAlgebraStageAugmentationIdeal n G U ↔
      modNCompletedGroupAlgebraStageAugmentation n G U x = 0 := by
  rw [modNCompletedGroupAlgebraStageAugmentationIdeal, RingHom.mem_ker]

omit [Fact (0 < n)] in
variable {n G} in
/--
Membership in the relevant augmentation kernel or augmentation ideal is equivalent to the
corresponding vanishing condition.
-/
@[simp]
theorem mem_modNCompletedGroupAlgebraAugmentationKernel_iff
    {x : ModNCompletedGroupAlgebra n G} :
    x ∈ modNCompletedGroupAlgebraAugmentationKernel n G ↔
      modNCompletedGroupAlgebraAugmentation n G x = 0 := by
  rfl

omit [Fact (0 < n)] in
variable {n G} in
/--
A mod-\(N\) completed group-algebra element projects into the stage augmentation ideal iff it
lies in the completed augmentation kernel.
-/
@[simp]
theorem mem_modNCompletedGroupAlgebraProjection_stageAugmentationIdeal_iff
    {U : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} {x :
        ModNCompletedGroupAlgebra n G} :
    modNCompletedGroupAlgebraProjection n G U x ∈
        modNCompletedGroupAlgebraStageAugmentationIdeal n G U ↔
      x ∈ modNCompletedGroupAlgebraAugmentationKernel n G := by
  rw [mem_modNCompletedGroupAlgebraStageAugmentationIdeal_iff,
    mem_modNCompletedGroupAlgebraAugmentationKernel_iff]
  change modNCompletedGroupAlgebraAugmentationAt n G U x = 0 ↔
    modNCompletedGroupAlgebraAugmentation n G x = 0
  rw [modNCompletedGroupAlgebraAugmentation_eq_at (n := n) (G := G) U x]

/-- The transition maps on the residue-coefficient finite-stage augmentation ideals. -/
def modNCompletedGroupAlgebraStageAugmentationIdealTransition
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    modNCompletedGroupAlgebraStageAugmentationIdeal n G V →
      modNCompletedGroupAlgebraStageAugmentationIdeal n G U :=
  fun x => ⟨modNCompletedGroupAlgebraTransition n G hUV x.1, by
    rw [mem_modNCompletedGroupAlgebraStageAugmentationIdeal_iff]
    have hcomp := congrFun
      (congrArg DFunLike.coe
        (modNCompletedGroupAlgebraStageAugmentation_compatible
          (n := n) (G := G) (U := U) (V := V) hUV))
      x.1
    rw [RingHom.comp_apply] at hcomp
    exact hcomp.trans
      ((mem_modNCompletedGroupAlgebraStageAugmentationIdeal_iff
        (n := n) (G := G) (U := V) (x := x.1)).1 x.2)⟩

omit [Fact (0 < n)] in
/--
The transition map between finite-stage augmentation ideals is evaluated by the corresponding
stage transition.
-/
@[simp]
theorem modNCompletedGroupAlgebraStageAugmentationIdealTransition_val
    {U V : _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G} (hUV : U ≤ V)
    (x : modNCompletedGroupAlgebraStageAugmentationIdeal n G V) :
    ((modNCompletedGroupAlgebraStageAugmentationIdealTransition
        (n := n) (G := G) hUV x : modNCompletedGroupAlgebraStageAugmentationIdeal n G U) :
      ModNCompletedGroupAlgebraStage n G U) =
      modNCompletedGroupAlgebraTransition n G hUV x.1 := rfl

/-- The inverse system of residue-coefficient finite-stage augmentation ideals. -/
def modNCompletedGroupAlgebraAugmentationIdealSystem :
    InverseSystem (I := _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) where
  X := fun U => ↥(modNCompletedGroupAlgebraStageAugmentationIdeal n G U)
  topologicalSpace := fun _ => ⊥
  map := fun {U V} hUV => modNCompletedGroupAlgebraStageAugmentationIdealTransition
    (n := n) (G := G) hUV
  continuous_map := by
    intro U V hUV
    let : TopologicalSpace (modNCompletedGroupAlgebraStageAugmentationIdeal n G U) := ⊥
    let : TopologicalSpace (modNCompletedGroupAlgebraStageAugmentationIdeal n G V) := ⊥
    let : DiscreteTopology (modNCompletedGroupAlgebraStageAugmentationIdeal n G V) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro U
    funext x
    apply Subtype.ext
    exact congrFun
      (congrArg DFunLike.coe (modNCompletedGroupAlgebraTransition_id (n := n) (G := G) U))
      x.1
  map_comp := by
    intro U V W hUV hVW
    funext x
    apply Subtype.ext
    exact congrFun
      (congrArg DFunLike.coe
        (modNCompletedGroupAlgebraTransition_comp (n := n) (G := G) hUV hVW))
      x.1

/-- The inverse-limit object of the residue-coefficient finite-stage augmentation ideals. -/
abbrev ModNCompletedGroupAlgebraAugmentationIdeal :=
  (modNCompletedGroupAlgebraAugmentationIdealSystem n G).inverseLimit

/-- The projection from the residue-coefficient augmentation-ideal inverse limit to one stage. -/
abbrev modNCompletedGroupAlgebraAugmentationIdealProjection (U :
    _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    ModNCompletedGroupAlgebraAugmentationIdeal n G →
      modNCompletedGroupAlgebraStageAugmentationIdeal n G U :=
  (modNCompletedGroupAlgebraAugmentationIdealSystem n G).projection U

/--
A residue-coefficient augmentation-kernel point determines a compatible family in the
finite-stage augmentation ideals.
-/
def toModNCompletedGroupAlgebraAugmentationIdeal :
    ModNCompletedGroupAlgebraAugmentationKernel n G →
      ModNCompletedGroupAlgebraAugmentationIdeal n G := by
  intro x
  refine ⟨fun U => ⟨modNCompletedGroupAlgebraProjection n G U x.1, ?_⟩, ?_⟩
  · exact (mem_modNCompletedGroupAlgebraProjection_stageAugmentationIdeal_iff
      (n := n) (G := G) (U := U) (x := x.1)).2
      ((mem_modNCompletedGroupAlgebraAugmentationKernel_iff
        (n := n) (G := G) (x := x.1)).1 x.2)
  · intro U V hUV
    apply Subtype.ext
    exact (modNCompletedGroupAlgebraSystem n G).projection_compatible x.1 U V hUV

omit [Fact (0 < n)] in
/--
The projection-to-stage map is one direction of the completed augmentation-ideal stage
equivalence.
-/
@[simp]
theorem modNCompletedGroupAlgebraAugmentationIdealProjection_to
    (x : ModNCompletedGroupAlgebraAugmentationKernel n G) (U :
        _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    ((modNCompletedGroupAlgebraAugmentationIdealProjection (n := n) (G := G) U
        (toModNCompletedGroupAlgebraAugmentationIdeal (n := n) (G := G) x)) :
      ModNCompletedGroupAlgebraStage n G U) =
      modNCompletedGroupAlgebraProjection n G U x.1 := rfl

/--
A compatible family of finite-stage augmentation-ideal elements determines a residue-coefficient
completed augmentation-kernel point.
-/
def ofModNCompletedGroupAlgebraAugmentationIdeal :
    ModNCompletedGroupAlgebraAugmentationIdeal n G →
      ModNCompletedGroupAlgebraAugmentationKernel n G := by
  intro x
  let y : ModNCompletedGroupAlgebra n G := ⟨fun U => (x.1 U).1, by
    intro U V hUV
    exact congrArg Subtype.val (x.2 U V hUV)⟩
  refine ⟨y, ?_⟩
  have hterm :
      modNCompletedGroupAlgebraProjection n G
          (_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G) y ∈
        modNCompletedGroupAlgebraStageAugmentationIdeal n G
          (_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G) := by
    change (x.1 (_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G)).1 ∈
      modNCompletedGroupAlgebraStageAugmentationIdeal n G
        (_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G)
    exact (x.1 (_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G)).2
  exact (mem_modNCompletedGroupAlgebraAugmentationKernel_iff (n := n) (G := G) (x := y)).2
    ((mem_modNCompletedGroupAlgebraProjection_stageAugmentationIdeal_iff
      (n := n) (G := G) (U := _root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndex G)
          (x := y)).1 hterm)

omit [Fact (0 < n)] in
/--
Projecting an element of the completed augmentation ideal gives its corresponding finite-stage
augmentation-ideal coordinate.
-/
@[simp]
theorem modNCompletedGroupAlgebraProjection_ofAugmentationIdeal
    (x : ModNCompletedGroupAlgebraAugmentationIdeal n G) (U :
        _root_.CompletedGroupAlgebra.CompletedGroupAlgebraIndex G) :
    modNCompletedGroupAlgebraProjection n G U
        (ofModNCompletedGroupAlgebraAugmentationIdeal (n := n) (G := G) x).1 =
      ((modNCompletedGroupAlgebraAugmentationIdealProjection (n := n) (G := G) U x) :
        ModNCompletedGroupAlgebraStage n G U) := rfl

omit [Fact (0 < n)] in
/--
The completion-to-stage map is one direction of the completed augmentation-ideal stage
equivalence.
-/
@[simp]
theorem ofModNCompletedGroupAlgebraAugmentationIdeal_to
    (x : ModNCompletedGroupAlgebraAugmentationKernel n G) :
    ofModNCompletedGroupAlgebraAugmentationIdeal (n := n) (G := G)
        (toModNCompletedGroupAlgebraAugmentationIdeal (n := n) (G := G) x) = x := by
  apply Subtype.ext
  apply (modNCompletedGroupAlgebraSystem n G).ext
  intro U
  rfl

omit [Fact (0 < n)] in
/--
The stage-to-completion map is one direction of the completed augmentation-ideal stage
equivalence.
-/
@[simp]
theorem toModNCompletedGroupAlgebraAugmentationIdeal_of
    (x : ModNCompletedGroupAlgebraAugmentationIdeal n G) :
    toModNCompletedGroupAlgebraAugmentationIdeal (n := n) (G := G)
        (ofModNCompletedGroupAlgebraAugmentationIdeal (n := n) (G := G) x) = x := by
  apply (modNCompletedGroupAlgebraAugmentationIdealSystem n G).ext
  intro U
  apply Subtype.ext
  rfl

/--
The residue-coefficient completed augmentation kernel is canonically equivalent to the inverse
limit of the finite-stage augmentation ideals.
-/
def modNCompletedGroupAlgebraAugmentationKernelEquivInverseLimit :
    ModNCompletedGroupAlgebraAugmentationKernel n G ≃
      ModNCompletedGroupAlgebraAugmentationIdeal n G where
  toFun := toModNCompletedGroupAlgebraAugmentationIdeal (n := n) (G := G)
  invFun := ofModNCompletedGroupAlgebraAugmentationIdeal (n := n) (G := G)
  left_inv := ofModNCompletedGroupAlgebraAugmentationIdeal_to (n := n) (G := G)
  right_inv := toModNCompletedGroupAlgebraAugmentationIdeal_of (n := n) (G := G)

omit [Fact (0 < n)] in
/--
The forward mod-\(n\) augmentation-kernel equivalence is the canonical map to the inverse-limit
augmentation ideal.
-/
@[simp]
theorem modNCompletedGroupAlgebraAugmentationKernelEquivInverseLimit_apply
    (x : ModNCompletedGroupAlgebraAugmentationKernel n G) :
    modNCompletedGroupAlgebraAugmentationKernelEquivInverseLimit (n := n) (G := G) x =
      toModNCompletedGroupAlgebraAugmentationIdeal (n := n) (G := G) x := rfl

omit [Fact (0 < n)] in
/--
The inverse mod-\(n\) augmentation-kernel equivalence reconstructs a kernel element from an
inverse-limit augmentation-ideal element.
-/
@[simp]
theorem modNCompletedGroupAlgebraAugmentationKernelEquivInverseLimit_symm_apply
    (x : ModNCompletedGroupAlgebraAugmentationIdeal n G) :
    (modNCompletedGroupAlgebraAugmentationKernelEquivInverseLimit (n := n) (G := G)).symm x =
      ofModNCompletedGroupAlgebraAugmentationIdeal (n := n) (G := G) x := rfl

end AugmentationIdeal

end

end FoxDifferential
