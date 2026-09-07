import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraPrimePower.Augmentation

set_option autoImplicit false

/-!
# Fox differential: completed — coefficient rings — prime-power augmentation ideal — stage

The principal declarations in this module are:

- `primePowerCompletedGroupAlgebraStageAugmentationIdeal`
  The augmentation ideal on one prime-power finite stage.
- `primePowerCompletedGroupAlgebraAugmentationKernel`
  The kernel of the canonical prime-power augmentation.
- `mem_primePowerCompletedGroupAlgebraStageAugmentationIdeal_iff`
  Membership in a prime-power finite-stage augmentation ideal is equivalent to vanishing under the
  stage augmentation map.
- `mem_primePowerCompletedGroupAlgebraAugmentationKernel_iff`
  Membership in the relevant augmentation kernel or augmentation ideal is equivalent to the
  corresponding vanishing condition.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems

universe u


variable (ℓ : ℕ) [Fact (0 < ℓ)]
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The augmentation ideal on one prime-power finite stage. -/
def primePowerCompletedGroupAlgebraStageAugmentationIdeal
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    Ideal (PrimePowerCompletedGroupAlgebraStage ℓ G i) := by
  letI : Fact (0 < ℓ ^ i.1) := ⟨primePower_pos ℓ i.1⟩
  exact RingHom.ker (modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2)

/-- The prime-power completed group-algebra stage augmentation ideal is finite. -/
instance instFinitePrimePowerCompletedGroupAlgebraStageAugmentationIdeal
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    Finite ↥(primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i) := by
  classical
  let : Finite (PrimePowerCompletedGroupAlgebraStage ℓ G i) :=
    instFinitePrimePowerCompletedGroupAlgebraStage (ℓ := ℓ) (G := G) i
  refine Finite.of_injective Subtype.val ?_
  intro x y hxy
  exact Subtype.ext hxy

/-- The kernel of the canonical prime-power augmentation. -/
def primePowerCompletedGroupAlgebraAugmentationKernel :
    Set (PrimePowerCompletedGroupAlgebra ℓ G) :=
  {x | primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x =
    (Zero.zero : PrimePowerCompletedCoeff ℓ G)}

/-- The kernel of the canonical prime-power augmentation is viewed as a subtype. -/
abbrev PrimePowerCompletedGroupAlgebraAugmentationKernel :=
  {x : PrimePowerCompletedGroupAlgebra ℓ G //
    x ∈ primePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G)}

omit [Fact (0 < ℓ)] in
variable {ℓ G} in
/--
Membership in a prime-power finite-stage augmentation ideal is equivalent to vanishing under the
stage augmentation map.
-/
@[simp]
theorem mem_primePowerCompletedGroupAlgebraStageAugmentationIdeal_iff
    {i : PrimePowerCompletedGroupAlgebraIndex G}
    {x : PrimePowerCompletedGroupAlgebraStage ℓ G i} :
    x ∈ primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i ↔
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2 x = 0 := by
  rw [primePowerCompletedGroupAlgebraStageAugmentationIdeal, RingHom.mem_ker]

variable {ℓ G} in
omit [Fact (0 < ℓ)] in
/--
Membership in the relevant augmentation kernel or augmentation ideal is equivalent to the
corresponding vanishing condition.
-/
@[simp]
theorem mem_primePowerCompletedGroupAlgebraAugmentationKernel_iff
    {x : PrimePowerCompletedGroupAlgebra ℓ G} :
    x ∈ primePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G) ↔
      primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x =
        (Zero.zero : PrimePowerCompletedCoeff ℓ G) := by
  rfl

variable {ℓ G} in
omit [Fact (0 < ℓ)] in
/--
Membership in the prime-power augmentation kernel is equivalent to vanishing after every
finite-stage augmentation.
-/
theorem mem_primePowerCompletedGroupAlgebraAugmentationKernel_iff_forall
    {x : PrimePowerCompletedGroupAlgebra ℓ G} :
    x ∈ primePowerCompletedGroupAlgebraAugmentationKernel (ℓ := ℓ) (G := G) ↔
      ∀ i : PrimePowerCompletedGroupAlgebraIndex G,
        modNCompletedGroupAlgebraStageAugmentation (ℓ ^ i.1) G i.2
          (primePowerCompletedGroupAlgebraProjection (ℓ := ℓ) (G := G) i x) = 0 := by
  constructor
  · intro hx i
    have hx0 :
        primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x =
          (Zero.zero : PrimePowerCompletedCoeff ℓ G) :=
      (mem_primePowerCompletedGroupAlgebraAugmentationKernel_iff
        (ℓ := ℓ) (G := G) (x := x)).1 hx
    have hi := congrArg
      (primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i) hx0
    change
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
          (primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x) = 0
    have hz :
        primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
            (Zero.zero : PrimePowerCompletedCoeff ℓ G) = 0 :=
      primePowerCompletedCoeffProjection_zero (ℓ := ℓ) (G := G) i
    rw [hz] at hi
    exact hi
  · intro hx
    rw [mem_primePowerCompletedGroupAlgebraAugmentationKernel_iff]
    apply (primePowerCompletedCoeffSystem ℓ G).ext
    intro i
    change
      primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i
          (primePowerCompletedGroupAlgebraAugmentation (ℓ := ℓ) (G := G) x) =
        primePowerCompletedCoeffProjection (ℓ := ℓ) (G := G) i 0
    rw [primePowerCompletedCoeffProjection_zero]
    exact hx i

/-- The transition maps on the prime-power finite-stage augmentation ideals. -/
def primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j) :
    primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j →
      primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i := by
  intro x
  refine ⟨primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij x.1, ?_⟩
  rw [mem_primePowerCompletedGroupAlgebraStageAugmentationIdeal_iff]
  have hcomp := congrFun
    (congrArg DFunLike.coe
      (primePowerCompletedGroupAlgebraStageAugmentation_comp_transition
        (ℓ := ℓ) (G := G) hij))
    x.1
  rw [RingHom.comp_apply] at hcomp
  have hx0 :
      modNCompletedGroupAlgebraStageAugmentation (ℓ ^ j.1) G j.2 x.1 = 0 :=
    (mem_primePowerCompletedGroupAlgebraStageAugmentationIdeal_iff
      (ℓ := ℓ) (G := G) (i := j) (x := x.1)).1 x.2
  simpa [hx0] using hcomp

omit [Fact (0 < ℓ)] in
/--
The transition map between finite-stage augmentation ideals is evaluated by the corresponding
stage transition.
-/
@[simp]
theorem primePowerCompletedGroupAlgebraStageAugmentationIdealTransition_val
    {i j : PrimePowerCompletedGroupAlgebraIndex G} (hij : i ≤ j)
    (x : primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j) :
    ((primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
        (ℓ := ℓ) (G := G) hij x :
          primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i) :
      PrimePowerCompletedGroupAlgebraStage ℓ G i) =
      primePowerCompletedGroupAlgebraTransition (ℓ := ℓ) (G := G) hij x.1 := rfl

/-- The inverse system of prime-power finite-stage augmentation ideals. -/
def primePowerCompletedGroupAlgebraAugmentationIdealSystem :
    InverseSystem (I := PrimePowerCompletedGroupAlgebraIndex G) where
  X := fun i => ↥(primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i)
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij =>
    primePowerCompletedGroupAlgebraStageAugmentationIdealTransition
      (ℓ := ℓ) (G := G) hij
  continuous_map := by
    intro i j hij
    let : TopologicalSpace
        (primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i) := ⊥
    let : TopologicalSpace
        (primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j) := ⊥
    let : DiscreteTopology
        (primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) j) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext x
    apply Subtype.ext
    exact congrFun
      (congrArg DFunLike.coe
        (primePowerCompletedGroupAlgebraTransition_id (ℓ := ℓ) (G := G) i)) x.1
  map_comp := by
    intro i j k hij hjk
    funext x
    apply Subtype.ext
    exact congrFun
      (congrArg DFunLike.coe
        (primePowerCompletedGroupAlgebraTransition_comp (ℓ := ℓ) (G := G) hij hjk))
      x.1

/-- The inverse-limit object of the prime-power augmentation-ideal system. -/
abbrev PrimePowerCompletedGroupAlgebraAugmentationIdeal :=
  (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).inverseLimit

/-- The projection from the prime-power augmentation-ideal inverse limit to one stage. -/
abbrev primePowerCompletedGroupAlgebraAugmentationIdealProjection
    (i : PrimePowerCompletedGroupAlgebraIndex G) :
    PrimePowerCompletedGroupAlgebraAugmentationIdeal ℓ G →
      primePowerCompletedGroupAlgebraStageAugmentationIdeal (ℓ := ℓ) (G := G) i :=
  (primePowerCompletedGroupAlgebraAugmentationIdealSystem ℓ G).projection i

end

end FoxDifferential
