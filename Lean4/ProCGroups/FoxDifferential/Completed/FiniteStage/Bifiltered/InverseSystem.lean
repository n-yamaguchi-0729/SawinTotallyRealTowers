import ProCGroups.FoxDifferential.Completed.FiniteStage.Bifiltered.System

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — bifiltered — inverse system

The principal declarations in this module are:

- `foxAlgebraicStageBifilteredSemidirectFamilyTransition`
  Transition in a bifiltered family of finite Fox semidirect stages. For i \(\le\) j, the j-stage is
  finer: its normal subgroup is contained in the i-stage normal subgroup and its coefficient modulus
  is divisible by the i-stage modulus.
- `foxAlgebraicStageBifilteredSemidirectSystem`
  The inverse system associated with a bifiltered family of finite Fox semidirect stages.
- `foxAlgebraicStageBifilteredSemidirectFamilyTransition_left`
  The left coordinate of the finite-stage semidirect point is the specified derivative component.
- `foxAlgebraicStageBifilteredSemidirectFamilyTransition_right`
  The right coordinate of the finite-stage semidirect point is the corresponding quotient component.
-/

namespace FoxDifferential

noncomputable section

open scoped Topology
open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u v

section BifilteredFamilySystem

variable {X : Type u} [DecidableEq X]
variable {J : Type v} [Preorder J]
variable (Nstage : J → Subgroup (FreeGroup X)) [∀ j, (Nstage j).Normal]
variable (nstage : J → ℕ) [∀ j, Fact (0 < nstage j)]

/--
Transition in a bifiltered family of finite Fox semidirect stages. For i \(\le\) j, the j-stage
is finer: its normal subgroup is contained in the i-stage normal subgroup and its coefficient
modulus is divisible by the i-stage modulus.
-/
def foxAlgebraicStageBifilteredSemidirectFamilyTransition
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    {i j : J} (hij : i ≤ j) :
    FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j) →*
      FoxAlgebraicStageSemidirect (X := X) (Nstage i) (nstage i) :=
  foxAlgebraicStageBifilteredSemidirectMap (X := X) (hN hij) (hn hij)

omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/--
The left coordinate of the finite-stage semidirect point is the specified derivative component.
-/
@[simp]
theorem foxAlgebraicStageBifilteredSemidirectFamilyTransition_left
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    {i j : J} (hij : i ≤ j)
    (y : FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j)) :
    (foxAlgebraicStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij y).left =
      foxAlgebraicStageBifilteredCoordinateVectorMap (X := X) (hN hij) (hn hij) y.left :=
  rfl

omit [DecidableEq X] [∀ (j : J), Fact (0 < nstage j)] in
/--
The right coordinate of the finite-stage semidirect point is the corresponding quotient
component.
-/
@[simp]
theorem foxAlgebraicStageBifilteredSemidirectFamilyTransition_right
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    {i j : J} (hij : i ≤ j)
    (y : FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j)) :
    (foxAlgebraicStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij y).right =
      foxAlgebraicStageTargetQuotientMap (X := X) (hN hij) y.right :=
  rfl

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)] in
/-- The bifiltered family transition along reflexivity is the identity. -/
@[simp]
theorem foxAlgebraicStageBifilteredSemidirectFamilyTransition_rfl
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    (i : J) :
    foxAlgebraicStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn (le_rfl : i ≤ i) =
      MonoidHom.id (FoxAlgebraicStageSemidirect (X := X) (Nstage i) (nstage i)) := by
  have hNid : hN (le_rfl : i ≤ i) = (le_rfl : Nstage i ≤ Nstage i) :=
    Subsingleton.elim _ _
  have hnid : hn (le_rfl : i ≤ i) = (dvd_rfl : nstage i ∣ nstage i) :=
    Subsingleton.elim _ _
  change foxAlgebraicStageBifilteredSemidirectMap
      (X := X) (hN (le_rfl : i ≤ i)) (hn (le_rfl : i ≤ i)) =
    MonoidHom.id (FoxAlgebraicStageSemidirect (X := X) (Nstage i) (nstage i))
  simp only [foxAlgebraicStageBifilteredSemidirectMap_rfl]

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)] in
/-- Bifiltered family transitions compose. -/
@[simp 900]
theorem foxAlgebraicStageBifilteredSemidirectFamilyTransition_comp
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    {i j k : J} (hij : i ≤ j) (hjk : j ≤ k) :
    (foxAlgebraicStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hij).comp
      (foxAlgebraicStageBifilteredSemidirectFamilyTransition
        (X := X) Nstage nstage hN hn hjk) =
    foxAlgebraicStageBifilteredSemidirectFamilyTransition
      (X := X) Nstage nstage hN hn (hij.trans hjk) := by
  have hNcomp : le_trans (hN hjk) (hN hij) = hN (hij.trans hjk) :=
    Subsingleton.elim _ _
  have hncomp : dvd_trans (hn hij) (hn hjk) = hn (hij.trans hjk) :=
    Subsingleton.elim _ _
  change
    (foxAlgebraicStageBifilteredSemidirectMap (X := X) (hN hij) (hn hij)).comp
      (foxAlgebraicStageBifilteredSemidirectMap (X := X) (hN hjk) (hn hjk)) =
    foxAlgebraicStageBifilteredSemidirectMap (X := X) (hN (hij.trans hjk))
      (hn (hij.trans hjk))
  rw [foxAlgebraicStageBifilteredSemidirectMap_comp
    (X := X) (N₀ := Nstage k) (N₁ := Nstage j) (N₂ := Nstage i)
    (n₀ := nstage i) (n₁ := nstage j) (n₂ := nstage k)
    (hN hjk) (hN hij) (hn hij) (hn hjk)]

/-- The inverse system associated with a bifiltered family of finite Fox semidirect stages. -/
def foxAlgebraicStageBifilteredSemidirectSystem
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j) :
    InverseSystem (I := J) where
  X := fun j => FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j)
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij =>
    foxAlgebraicStageBifilteredSemidirectFamilyTransition
      (X := X) Nstage nstage hN hn hij
  continuous_map := by
    intro i j hij
    let : TopologicalSpace (FoxAlgebraicStageSemidirect (X := X) (Nstage i) (nstage i)) := ⊥
    let : TopologicalSpace (FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j)) := ⊥
    let : DiscreteTopology (FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j)) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro i
    funext y
    exact congrArg (fun f : FoxAlgebraicStageSemidirect (X := X) (Nstage i) (nstage i) →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage i) (nstage i) => f y)
      (foxAlgebraicStageBifilteredSemidirectFamilyTransition_rfl
        (X := X) Nstage nstage hN hn i)
  map_comp := by
    intro i j k hij hjk
    funext y
    exact congrArg (fun f : FoxAlgebraicStageSemidirect (X := X) (Nstage k) (nstage k) →*
        FoxAlgebraicStageSemidirect (X := X) (Nstage i) (nstage i) => f y)
      (foxAlgebraicStageBifilteredSemidirectFamilyTransition_comp
        (X := X) Nstage nstage hN hn hij hjk)

/-- The finite-stage semidirect system carries its group structure. -/
instance instGroupFoxAlgebraicStageBifilteredSemidirectSystemX
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j) (j : J) :
    Group ((foxAlgebraicStageBifilteredSemidirectSystem (X := X) Nstage nstage hN hn).X j) := by
  dsimp [foxAlgebraicStageBifilteredSemidirectSystem]
  infer_instance

/-- The finite-stage semidirect system is a compatible group system. -/
instance instIsGroupSystemFoxAlgebraicStageBifilteredSemidirectSystem
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j) :
    IsGroupSystem (foxAlgebraicStageBifilteredSemidirectSystem (X := X) Nstage nstage hN hn) where
  map_one := by
    intro i j hij
    exact map_one (foxAlgebraicStageBifilteredSemidirectFamilyTransition
      (X := X) Nstage nstage hN hn hij)
  map_mul := by
    intro i j hij x y
    exact map_mul (foxAlgebraicStageBifilteredSemidirectFamilyTransition
      (X := X) Nstage nstage hN hn hij) x y
  map_inv := by
    intro i j hij x
    exact map_inv (foxAlgebraicStageBifilteredSemidirectFamilyTransition
      (X := X) Nstage nstage hN hn hij) x

/-- The inverse limit of a bifiltered finite Fox semidirect system. -/
abbrev FoxAlgebraicStageBifilteredSemidirectLimit
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j) : Type _ :=
  (foxAlgebraicStageBifilteredSemidirectSystem (X := X) Nstage nstage hN hn).inverseLimit

/-- The projection from the bifiltered inverse limit to a finite Fox semidirect stage. -/
def foxAlgebraicStageBifilteredSemidirectLimitProjection
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    (j : J) :
    FoxAlgebraicStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn →
      FoxAlgebraicStageSemidirect (X := X) (Nstage j) (nstage j) :=
  (foxAlgebraicStageBifilteredSemidirectSystem (X := X) Nstage nstage hN hn).projection j

omit [DecidableEq X] [∀ j, Fact (0 < nstage j)] in
/--
The bifiltered semidirect inverse-limit projection returns the coordinate at the selected stage.
-/
@[simp]
theorem foxAlgebraicStageBifilteredSemidirectLimitProjection_apply
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    (j : J)
    (y : FoxAlgebraicStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn) :
    foxAlgebraicStageBifilteredSemidirectLimitProjection
        (X := X) Nstage nstage hN hn j y = y.1 j :=
  rfl

/--
Boundary-cycle membership in the bifiltered inverse limit is stagewise boundary-cycle
membership.
-/
def foxAlgebraicStageBifilteredSemidirectLimitBoundaryCycleSet
    [Fintype X]
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j) :
    Set (FoxAlgebraicStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn) :=
  {y | ∀ j : J,
    foxAlgebraicStageBifilteredSemidirectLimitProjection
      (X := X) Nstage nstage hN hn j y ∈
        foxAlgebraicStageSemidirectBoundaryCycleSet (X := X) (Nstage j) (nstage j)}

/-- A relation word gives a compatible point in the bifiltered finite Fox semidirect limit. -/
def foxAlgebraicStageBifilteredSemidirectKernelWordPointLimit
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    (w : FreeGroup X) :
    FoxAlgebraicStageBifilteredSemidirectLimit (X := X) Nstage nstage hN hn :=
  ⟨fun j => foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w, by
    intro i j hij
    exact foxAlgebraicStageBifilteredSemidirectMap_kernelWordPoint
      (X := X) (hN hij) (hn hij) w⟩

omit [∀ j, Fact (0 < nstage j)] in
/--
Projection of the bifiltered semidirect kernel-word limit gives the corresponding finite-stage
kernel-word point.
-/
@[simp]
theorem foxAlgebraicStageBifilteredSemidirectKernelWordPointLimit_projection
    (hN : ∀ {i j : J}, i ≤ j → Nstage j ≤ Nstage i)
    (hn : ∀ {i j : J}, i ≤ j → nstage i ∣ nstage j)
    (j : J) (w : FreeGroup X) :
    foxAlgebraicStageBifilteredSemidirectLimitProjection
        (X := X) Nstage nstage hN hn j
        (foxAlgebraicStageBifilteredSemidirectKernelWordPointLimit
          (X := X) Nstage nstage hN hn w) =
      foxAlgebraicStageSemidirectKernelWordPoint (X := X) (Nstage j) (nstage j) w :=
  rfl

end BifilteredFamilySystem

end

end FoxDifferential
