import ProCGroups.FoxDifferential.Completed.FreeProC.SemidirectLift

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — density

The principal declarations in this module are:

- `HasLeftOpenSubgroupNeighbourhoodBasis`
  Left open subgroup neighborhood basis, expressed as a proposition rather than a structure. For
  every neighborhood \(U\) of \(y\), one can find an open subgroup \(V\) such that the left coset
  \(yV\) is contained in \(U\). This is the topological input used to pass from finite or
  open-subgroup approximations to ordinary closure.
- `HasLeftOpenNormalSubgroupNeighbourhoodBasis`
  This is the normal-subgroup version of the left open-subgroup neighborhood basis: in a profinite
  group, every identity neighborhood can be refined by an open normal subgroup.
- `subset_closure_of_open_neighbourhood_approximation`
  A point belongs to the set-theoretic closure of \(S\) when every open neighborhood of it contains
  an algebraic point of \(S\).
- `HasLeftOpenNormalSubgroupNeighbourhoodBasis.to_subgroup_basis`
  The normal-subgroup basis implies the subgroup basis.
-/

namespace FoxDifferential

noncomputable section

universe u v

section GenericClosureAPI

variable {Y : Type u} [TopologicalSpace Y]
variable {S T : Set Y}

/--
A point belongs to the set-theoretic closure of \(S\) when every open neighborhood of it
contains an algebraic point of \(S\).
-/
theorem subset_closure_of_open_neighbourhood_approximation
    (happrox :
      ∀ y : Y, y ∈ T → ∀ U : Set Y, IsOpen U → y ∈ U →
        ∃ s : Y, s ∈ S ∧ s ∈ U) :
    T ⊆ closure S := by
  intro y hy
  rw [mem_closure_iff]
  intro U hU hyU
  rcases happrox y hy U hU hyU with ⟨s, hsS, hsU⟩
  exact ⟨s, hsU, hsS⟩

end GenericClosureAPI

section OpenSubgroupClosureAPI

variable {Y : Type u} [Group Y] [TopologicalSpace Y]
variable {S T : Set Y}

/--
Left open subgroup neighborhood basis, expressed as a proposition rather than a structure. For
every neighborhood \(U\) of \(y\), one can find an open subgroup \(V\) such that the left coset
\(yV\) is contained in \(U\). This is the topological input used to pass from finite or
open-subgroup approximations to ordinary closure.
-/
def HasLeftOpenSubgroupNeighbourhoodBasis (Y : Type u) [Group Y] [TopologicalSpace Y] : Prop :=
  ∀ (y : Y) (U : Set Y), IsOpen U → y ∈ U →
    ∃ V : Subgroup Y, IsOpen ((V : Subgroup Y) : Set Y) ∧
      ∀ z : Y, z ∈ V → y * z ∈ U

/--
This is the normal-subgroup version of the left open-subgroup neighborhood basis: in a profinite
group, every identity neighborhood can be refined by an open normal subgroup.
-/
def HasLeftOpenNormalSubgroupNeighbourhoodBasis
    (Y : Type u) [Group Y] [TopologicalSpace Y] : Prop :=
  ∀ (y : Y) (U : Set Y), IsOpen U → y ∈ U →
    ∃ V : Subgroup Y, V.Normal ∧ IsOpen ((V : Subgroup Y) : Set Y) ∧
      ∀ z : Y, z ∈ V → y * z ∈ U

/-- The normal-subgroup basis implies the subgroup basis. -/
theorem HasLeftOpenNormalSubgroupNeighbourhoodBasis.to_subgroup_basis
    (hbasis : HasLeftOpenNormalSubgroupNeighbourhoodBasis Y) :
    HasLeftOpenSubgroupNeighbourhoodBasis Y := by
  intro y U hU hyU
  rcases hbasis y U hU hyU with ⟨V, _hVnormal, hVopen, hVcoset⟩
  exact ⟨V, hVopen, hVcoset⟩

/--
If for every \(y \in T\) and every open subgroup \(V\) there is \(s \in S\) with \(y^{-1}s \in
V\), then \(T\) is contained in the closure of \(S\).
-/
theorem subset_closure_of_openSubgroup_approximation
    (hbasis : HasLeftOpenSubgroupNeighbourhoodBasis Y)
    (happrox :
      ∀ y : Y, y ∈ T → ∀ V : Subgroup Y,
        IsOpen ((V : Subgroup Y) : Set Y) →
          ∃ s : Y, s ∈ S ∧ y⁻¹ * s ∈ V) :
    T ⊆ closure S := by
  refine subset_closure_of_open_neighbourhood_approximation ?_
  intro y hy U hU hyU
  rcases hbasis y U hU hyU with ⟨V, hVopen, hVcoset⟩
  rcases happrox y hy V hVopen with ⟨s, hsS, hsV⟩
  refine ⟨s, hsS, ?_⟩
  have hcoset : y * (y⁻¹ * s) ∈ U := hVcoset (y⁻¹ * s) hsV
  simpa [mul_assoc] using hcoset

/--
The completed Fox graph or boundary-cycle set lies in the required closed generated submodule by
finite-stage separation.
-/
theorem subset_closure_of_openNormalSubgroup_approximation
    (hbasis : HasLeftOpenNormalSubgroupNeighbourhoodBasis Y)
    (happrox :
      ∀ y : Y, y ∈ T → ∀ V : Subgroup Y,
        V.Normal → IsOpen ((V : Subgroup Y) : Set Y) →
          ∃ s : Y, s ∈ S ∧ y⁻¹ * s ∈ V) :
    T ⊆ closure S := by
  refine subset_closure_of_open_neighbourhood_approximation ?_
  intro y hy U hU hyU
  rcases hbasis y U hU hyU with ⟨V, hVnormal, hVopen, hVcoset⟩
  rcases happrox y hy V hVnormal hVopen with ⟨s, hsS, hsV⟩
  refine ⟨s, hsS, ?_⟩
  have hcoset : y * (y⁻¹ * s) ∈ U := hVcoset (y⁻¹ * s) hsV
  simpa [mul_assoc] using hcoset

/-- Coset approximation gives a pointwise closure statement. -/
theorem mem_closure_of_openSubgroup_approximation
    (hbasis : HasLeftOpenSubgroupNeighbourhoodBasis Y)
    {y : Y}
    (happrox :
      ∀ V : Subgroup Y, IsOpen ((V : Subgroup Y) : Set Y) →
        ∃ s : Y, s ∈ S ∧ y⁻¹ * s ∈ V) :
    y ∈ closure S := by
  rw [mem_closure_iff]
  intro U hU hyU
  rcases hbasis y U hU hyU with ⟨V, hVopen, hVcoset⟩
  rcases happrox V hVopen with ⟨s, hsS, hsV⟩
  refine ⟨s, ?_, hsS⟩
  have hcoset : y * (y⁻¹ * s) ∈ U := hVcoset (y⁻¹ * s) hsV
  simpa [mul_assoc] using hcoset

end OpenSubgroupClosureAPI

section QuotientKernelClosureAPI

variable {Y : Type u} [Group Y] [TopologicalSpace Y]
variable {S T : Set Y}

/--
A left neighborhood basis expressed directly by kernels of quotient maps. This is the form
produced by finite-stage maps: every open neighborhood of \(y\) contains a left coset
\(y\ker(\pi_j)\).
-/
def HasLeftQuotientKernelNeighbourhoodBasis
    {J : Type v} {Q : J → Type*} [∀ j, Group (Q j)]
    (π : ∀ j : J, Y →* Q j) : Prop :=
  ∀ (y : Y) (U : Set Y), IsOpen U → y ∈ U →
    ∃ j : J, ∀ z : Y, z ∈ (π j).ker → y * z ∈ U

/--
If quotient kernels form a left neighborhood basis, then equality at every quotient stage gives
closure. This is the abstract topology step for the remaining Crowell density theorem: finite
quotient exactness supplies \(s\in S\) with \(\pi_j s = \pi_j y\); the quotient-kernel basis
turns this into ordinary topological approximation.
-/
theorem subset_closure_of_quotientKernel_approximation
    {J : Type v} {Q : J → Type*} [∀ j, Group (Q j)]
    (π : ∀ j : J, Y →* Q j)
    (hbasis : HasLeftQuotientKernelNeighbourhoodBasis (Y := Y) π)
    (happrox :
      ∀ y : Y, y ∈ T → ∀ j : J,
        ∃ s : Y, s ∈ S ∧ π j s = π j y) :
    T ⊆ closure S := by
  refine subset_closure_of_open_neighbourhood_approximation ?_
  intro y hy U hU hyU
  rcases hbasis y U hU hyU with ⟨j, hj⟩
  rcases happrox y hy j with ⟨s, hsS, hπ⟩
  have hker : y⁻¹ * s ∈ (π j).ker := by
    change π j (y⁻¹ * s) = 1
    rw [map_mul, map_inv, hπ]
    simp only [inv_mul_cancel]
  refine ⟨s, hsS, ?_⟩
  have hsU : y * (y⁻¹ * s) ∈ U := hj (y⁻¹ * s) hker
  simpa [mul_assoc] using hsU

end QuotientKernelClosureAPI

section CompletedFoxDensity

open scoped Topology

variable {C : ProCGroups.FiniteGroupClass}
variable {X H : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [DecidableEq X]
variable [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
variable [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)]

/--
The semidirect point \((D w, 1)\) attached to an abstract free-group kernel-word candidate. The
word may or may not actually lie in the kernel; kernel membership is recorded separately by the
corresponding kernel-cycle-set lemma.
-/
def freeProCZCCompletedFoxSemidirectKernelWordPoint (φ : X → H) (w : FreeGroup X) :
    ZCCompletedFoxSemidirect C X H :=
  { left :=
      zcFreeGroupFoxDerivativeVector C (FreeGroup.lift φ) w,
    right := (1 : H) }

omit [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] in
/--
The left coordinate of a completed Fox semidirect kernel-word point is its completed Fox
derivative vector.
-/
@[simp]
theorem freeProCZCCompletedFoxSemidirectKernelWordPoint_left
    (φ : X → H) (w : FreeGroup X) :
    (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w).left =
      zcFreeGroupFoxDerivativeVector C (FreeGroup.lift φ) w :=
  rfl

omit [TopologicalSpace (ZCCompletedFoxSemidirect C X H)] [IsTopologicalGroup
    (ZCCompletedFoxSemidirect C X H)] in
/-- The right coordinate of a completed Fox semidirect kernel-word point is the identity element. -/
@[simp]
theorem freeProCZCCompletedFoxSemidirectKernelWordPoint_right
    (φ : X → H) (w : FreeGroup X) :
    (freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w).right = 1 :=
  rfl

omit [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/-- A genuine kernel word gives an element of the algebraic kernel-word cycle set. -/
theorem freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet
    (φ : X → H) {w : FreeGroup X} (hw : FreeGroup.lift φ w = 1) :
    freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w ∈
      freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ := by
  exact ⟨w, hw, rfl⟩

omit [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
Membership in the completed Fox semidirect kernel-cycle set is equivalent to vanishing of the
corresponding finite-stage coordinate.
-/
theorem mem_freeProCZCCompletedFoxSemidirectKernelCycleSet_iff
    {φ : X → H}
    {y : ZCCompletedFoxSemidirect C X H} :
    y ∈ freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ ↔
      ∃ w : FreeGroup X, FreeGroup.lift φ w = 1 ∧
        y = freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w := by
  constructor
  · intro hy
    rcases hy with ⟨w, hw, hy⟩
    exact ⟨w, hw, hy⟩
  · rintro ⟨w, hw, hy⟩
    rw [hy]
    exact freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet
      (C := C) φ hw

omit [TopologicalSpace (ZCCompletedFoxSemidirect C X H)]
  [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
omit [DecidableEq X] in
/-- Boundary-cycle membership for a point of the form \((v,1)\). -/
theorem freeProCZCCompletedFoxSemidirectBoundaryCycleSet_mk_iff
    [Fintype X] {φ : X → H}
    {v : ZCFreeFoxCoordinates C (X := X) (H := H)} :
    ({ left := v, right := (1 : H) } :
        ZCCompletedFoxSemidirect C X H) ∈
      freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ↔
        zcFreeGroupFoxBoundary C (FreeGroup.lift φ) v = 0 := by
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨rfl, h⟩

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
Quotient-kernel approximation form of the completed Fox density statement. This is the
finite-stage attack surface for the remaining density theorem: once finite quotient exactness
produces, for every finite quotient stage j, a kernel word whose semidirect point has the same
j-th quotient image as the boundary cycle, the completed density statement follows.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_quotKernel_approx
    [Fintype X] (φ : X → H)
    {J : Type v} {Q : J → Type*} [∀ j, Group (Q j)]
    (π : ∀ j : J,
      ZCCompletedFoxSemidirect C X H →* Q j)
    (hbasis :
      HasLeftQuotientKernelNeighbourhoodBasis
        (Y := ZCCompletedFoxSemidirect C X H) π)
    (happrox :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ j : J,
            ∃ w : FreeGroup X,
              FreeGroup.lift φ w = 1 ∧
                π j (freeProCZCCompletedFoxSemidirectKernelWordPoint
                    (C := C) φ w) = π j y) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) := by
  refine subset_closure_of_quotientKernel_approximation
    (Y := ZCCompletedFoxSemidirect C X H)
    (S := freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ)
    (T := freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ)
    π hbasis ?_
  intro y hy j
  rcases happrox y hy j with ⟨w, hw, hπ⟩
  exact
    ⟨freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w,
      freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet
        (C := C) φ hw,
      hπ⟩

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
For every boundary cycle and every open neighborhood in the completed semidirect product, there
is a genuine kernel word whose point \((D w, 1)\) lies in that neighborhood; this is the density
statement used by Crowell middle exactness.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_open_neighbourhood_approx
    [Fintype X] (φ : X → H)
    (happrox :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ U : Set (ZCCompletedFoxSemidirect C X H),
            IsOpen U → y ∈ U →
              ∃ w : FreeGroup X,
                FreeGroup.lift φ w = 1 ∧
                freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w ∈ U) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) := by
  refine subset_closure_of_open_neighbourhood_approximation ?_
  intro y hy U hU hyU
  rcases happrox y hy U hU hyU with ⟨w, hw, hUmem⟩
  refine ⟨freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w, ?_, hUmem⟩
  exact freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet
    (C := C) φ hw

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
For every open subgroup \(V\) of the completed Fox semidirect group, a boundary cycle \(y\) is
approximated by a kernel-word cycle point modulo the left coset \(yV\).
-/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_openSubgroup_approx
    [Fintype X] (φ : X → H)
    (hbasis :
      HasLeftOpenSubgroupNeighbourhoodBasis
        (ZCCompletedFoxSemidirect C X H))
    (happrox :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ V : Subgroup (ZCCompletedFoxSemidirect C X H),
            IsOpen ((V : Subgroup
              (ZCCompletedFoxSemidirect C X H)) : Set
              (ZCCompletedFoxSemidirect C X H)) →
              ∃ w : FreeGroup X,
                FreeGroup.lift φ w = 1 ∧
                y⁻¹ * freeProCZCCompletedFoxSemidirectKernelWordPoint
                    (C := C) φ w ∈ V) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) := by
  refine subset_closure_of_openSubgroup_approximation
    (Y := ZCCompletedFoxSemidirect C X H)
    (S := freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ)
    (T := freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ)
    hbasis ?_
  intro y hy V hVopen
  rcases happrox y hy V hVopen with ⟨w, hw, hVmem⟩
  exact
    ⟨freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w,
      freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet
        (C := C) φ hw,
      hVmem⟩

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/-- Open-normal-subgroup approximation form of the completed Fox density statement. -/
theorem freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_openNormalSubgroup_approx
    [Fintype X] (φ : X → H)
    (hbasis :
      HasLeftOpenNormalSubgroupNeighbourhoodBasis
        (ZCCompletedFoxSemidirect C X H))
    (happrox :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ V : Subgroup (ZCCompletedFoxSemidirect C X H),
            V.Normal →
            IsOpen ((V : Subgroup
              (ZCCompletedFoxSemidirect C X H)) : Set
              (ZCCompletedFoxSemidirect C X H)) →
              ∃ w : FreeGroup X,
                FreeGroup.lift φ w = 1 ∧
                y⁻¹ * freeProCZCCompletedFoxSemidirectKernelWordPoint
                    (C := C) φ w ∈ V) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) := by
  refine subset_closure_of_openNormalSubgroup_approximation
    (Y := ZCCompletedFoxSemidirect C X H)
    (S := freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ)
    (T := freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ)
    hbasis ?_
  intro y hy V hVnormal hVopen
  rcases happrox y hy V hVnormal hVopen with ⟨w, hw, hVmem⟩
  exact
    ⟨freeProCZCCompletedFoxSemidirectKernelWordPoint (C := C) φ w,
      freeProCZCCompletedFoxSemidirectKernelWordPoint_mem_kernelCycleSet
        (C := C) φ hw,
      hVmem⟩

/--
Open-subgroup approximation places every completed boundary cycle inside the closed generated
Fox graph target.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_openSubgroup_approx
    [Fintype X] (φ : X → H)
    (hbasis :
      HasLeftOpenSubgroupNeighbourhoodBasis
        (ZCCompletedFoxSemidirect C X H))
    (happrox :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ V : Subgroup (ZCCompletedFoxSemidirect C X H),
            IsOpen ((V : Subgroup
              (ZCCompletedFoxSemidirect C X H)) : Set
              (ZCCompletedFoxSemidirect C X H)) →
              ∃ w : FreeGroup X,
                FreeGroup.lift φ w = 1 ∧
                y⁻¹ * freeProCZCCompletedFoxSemidirectKernelWordPoint
                    (C := C) φ w ∈ V) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density (C := C) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_openSubgroup_approx
        (C := C) φ hbasis happrox)

/--
Open-normal-subgroup approximation places every completed boundary cycle inside the closed
generated Fox graph target.
-/
theorem freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_openNormalSubgroup_approx
    [Fintype X] (φ : X → H)
    (hbasis :
      HasLeftOpenNormalSubgroupNeighbourhoodBasis
        (ZCCompletedFoxSemidirect C X H))
    (happrox :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ V : Subgroup (ZCCompletedFoxSemidirect C X H),
            V.Normal →
            IsOpen ((V : Subgroup
              (ZCCompletedFoxSemidirect C X H)) : Set
              (ZCCompletedFoxSemidirect C X H)) →
              ∃ w : FreeGroup X,
                FreeGroup.lift φ w = 1 ∧
                y⁻¹ * freeProCZCCompletedFoxSemidirectKernelWordPoint
                    (C := C) φ w ∈ V) :
    freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ ⊆
      ((freeProCZCCompletedFoxSemidirectClosedGeneratedTarget (C := C) φ : Subgroup
          (ZCCompletedFoxSemidirect C X H)) : Set
          (ZCCompletedFoxSemidirect C X H)) := by
  exact
    freeProCZCFoxBoundaryCycles_subset_closedGenTarget_of_density (C := C) φ
      (freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_openNormalSubgroup_approx
        (C := C) φ hbasis happrox)

omit [IsTopologicalGroup (ZCCompletedFoxSemidirect C X H)] in
/--
Under the standard continuity inputs, open-subgroup approximation upgrades the one-sided closure
statement to the equality between boundary cycles and the closure of kernel-word cycles.
-/
theorem closure_freeProCZCFoxSemiKernelCycleSet_eq_boundaryCycleSet_of_openSubgroup_approx
    [Fintype X] [T1Space H]
    [TopologicalSpace (ZCCompletedGroupAlgebra C H)]
    [T1Space (ZCCompletedGroupAlgebra C H)]
    (φ : X → H)
    (hleft :
      Continuous
        (fun y : ZCCompletedFoxSemidirect C X H => y.left))
    (hright :
      Continuous
        (fun y : ZCCompletedFoxSemidirect C X H => y.right))
    (hboundary :
      Continuous
        (zcFreeGroupFoxBoundary C (FreeGroup.lift φ)))
    (hbasis :
      HasLeftOpenSubgroupNeighbourhoodBasis
        (ZCCompletedFoxSemidirect C X H))
    (happrox :
      ∀ y : ZCCompletedFoxSemidirect C X H,
        y ∈ freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ →
          ∀ V : Subgroup (ZCCompletedFoxSemidirect C X H),
            IsOpen ((V : Subgroup
              (ZCCompletedFoxSemidirect C X H)) : Set
              (ZCCompletedFoxSemidirect C X H)) →
              ∃ w : FreeGroup X,
                FreeGroup.lift φ w = 1 ∧
                y⁻¹ * freeProCZCCompletedFoxSemidirectKernelWordPoint
                    (C := C) φ w ∈ V) :
    closure (freeProCZCCompletedFoxSemidirectKernelCycleSet (C := C) φ) =
      freeProCZCCompletedFoxSemidirectBoundaryCycleSet (C := C) φ := by
  exact
    (closure_freeProCZCFoxSemiKernelCycleSet_eq_boundaryCycleSet_iff_density (C := C) (φ := φ)
        hleft hright hboundary).2
      (freeProCZCFoxBoundaryCycles_subset_closure_kernelCycleSet_of_openSubgroup_approx
        (C := C) φ hbasis happrox)

end CompletedFoxDensity

end

end FoxDifferential
