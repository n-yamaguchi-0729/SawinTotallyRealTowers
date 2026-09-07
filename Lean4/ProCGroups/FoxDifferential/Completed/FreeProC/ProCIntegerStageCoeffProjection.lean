import ProCGroups.FoxDifferential.Completed.FreeProC.BifilteredCoefficientStageProjection
import ProCGroups.FoxDifferential.Completed.ProCIntegerCoefficients.Core

set_option autoImplicit false

/-!
# Fox differential: completed — free pro-\(C\) — pro c integer stage coeff projection

The principal declarations in this module are:

- `zcCompletedGroupAlgebraStageToFoxAlgebraicStage`
  A finite stage of \(\mathbb{Z}_C\llbracket H\rrbracket\) maps to a finite Fox target group algebra
  once its coefficient modulus dominates \(n\) and its finite quotient maps to \(F/N\).
- `zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap`
  The resulting completed-to-finite coefficient map.
- `zcCompletedGroupAlgebraStageToFoxAlgebraicStage_of`
  Evaluation on a completed group-algebra stage basis element.
- `zcCompletedGroupAlgebraStageToFoxAlgebraicStage_single`
  Evaluation on a single coefficient at a stage quotient element.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v

section OneStageToFiniteFox

variable {C : ProCGroups.FiniteGroupClass}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable (N : Subgroup (FreeGroup X)) [N.Normal]
variable (n : ℕ) [Fact (0 < n)]
variable (i : ZCCompletedGroupAlgebraIndex C H)

/--
A finite stage of \(\mathbb{Z}_C\llbracket H\rrbracket\) maps to a finite Fox target group
algebra once its coefficient modulus dominates \(n\) and its finite quotient maps to \(F/N\).
-/
def zcCompletedGroupAlgebraStageToFoxAlgebraicStage
    (hmod : n ∣ i.1.modulus)
    (qmap : CompletedGroupAlgebraQuotientInClass H C i.2 →*
      foxAlgebraicStageTargetQuotient (X := X) N) :
    ZCCompletedGroupAlgebraStage C H i →+*
      foxAlgebraicStageTargetGroupAlgebra (X := X) N n := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  letI : Algebra (ModNCompletedCoeff i.1.modulus) (ModNCompletedCoeff n) :=
    ZMod.algebra' (R := ModNCompletedCoeff n) (m := n) (n := i.1.modulus) hmod
  letI : Algebra (ModNCompletedCoeff i.1.modulus)
      (foxAlgebraicStageTargetGroupAlgebra (X := X) N n) := inferInstance
  exact
    (MonoidAlgebra.lift (ModNCompletedCoeff i.1.modulus)
      (foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
      (CompletedGroupAlgebraQuotientInClass H C i.2)
      ((MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N)).comp qmap)).toRingHom

omit [DecidableEq X] [Fact (0 < n)] in
/-- Evaluation on a completed group-algebra stage basis element. -/
@[simp]
theorem zcCompletedGroupAlgebraStageToFoxAlgebraicStage_of
    (hmod : n ∣ i.1.modulus)
    (qmap : CompletedGroupAlgebraQuotientInClass H C i.2 →*
      foxAlgebraicStageTargetQuotient (X := X) N)
    (q : CompletedGroupAlgebraQuotientInClass H C i.2) :
    zcCompletedGroupAlgebraStageToFoxAlgebraicStage
        (C := C) (X := X) (H := H) N n i hmod qmap
        (MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
          (CompletedGroupAlgebraQuotientInClass H C i.2) q) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N) (qmap q) := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  simp only [zcCompletedGroupAlgebraStageToFoxAlgebraicStage, AlgHom.toRingHom_eq_coe,
      MonoidAlgebra.of_apply,
  RingHom.coe_coe, MonoidAlgebra.lift_single, MonoidHom.coe_comp, Function.comp_apply,
      MonoidAlgebra.smul_single,
  one_smul]

omit [DecidableEq X] [Fact (0 < n)] in
/-- Evaluation on a single coefficient at a stage quotient element. -/
theorem zcCompletedGroupAlgebraStageToFoxAlgebraicStage_single
    (hmod : n ∣ i.1.modulus)
    (qmap : CompletedGroupAlgebraQuotientInClass H C i.2 →*
      foxAlgebraicStageTargetQuotient (X := X) N)
    (q : CompletedGroupAlgebraQuotientInClass H C i.2)
    (a : ModNCompletedCoeff i.1.modulus) :
    zcCompletedGroupAlgebraStageToFoxAlgebraicStage
        (C := C) (X := X) (H := H) N n i hmod qmap
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single (qmap q)
        (modNCompletedCoeffMap (n := n) (m := i.1.modulus) hmod a) := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  let : Algebra (ModNCompletedCoeff i.1.modulus) (ModNCompletedCoeff n) :=
    ZMod.algebra' (R := ModNCompletedCoeff n) (m := n) (n := i.1.modulus) hmod
  have hcoeff :
      algebraMap (ModNCompletedCoeff i.1.modulus) (ModNCompletedCoeff n) a =
        modNCompletedCoeffMap (n := n) (m := i.1.modulus) hmod a := by
    rfl
  change
    MonoidAlgebra.lift (ModNCompletedCoeff i.1.modulus)
        (foxAlgebraicStageTargetGroupAlgebra (X := X) N n)
        (CompletedGroupAlgebraQuotientInClass H C i.2)
        ((MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N)).comp qmap)
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single (qmap q)
        (modNCompletedCoeffMap (n := n) (m := i.1.modulus) hmod a)
  rw [MonoidAlgebra.lift_single]
  change
    algebraMap (ModNCompletedCoeff i.1.modulus) (ModNCompletedCoeff n) a •
        MonoidAlgebra.of (ModNCompletedCoeff n)
          (foxAlgebraicStageTargetQuotient (X := X) N) (qmap q) =
      MonoidAlgebra.single (qmap q)
        (modNCompletedCoeffMap (n := n) (m := i.1.modulus) hmod a)
  rw [hcoeff, MonoidAlgebra.smul_of]

omit [DecidableEq X] in
/--
If no coefficient reduction is taken and the target quotient comparison is injective, then the
finite-stage map from the completed group-algebra stage to the finite Fox target group algebra
is injective.
-/
theorem zcCompletedGroupAlgebraStageToFoxAlgebraicStage_self_injective
    (qmap : CompletedGroupAlgebraQuotientInClass H C i.2 →*
      foxAlgebraicStageTargetQuotient (X := X) N)
    (hqmap : Function.Injective qmap) :
    Function.Injective
      (zcCompletedGroupAlgebraStageToFoxAlgebraicStage
        (C := C) (X := X) (H := H) N i.1.modulus i dvd_rfl qmap) := by
  classical
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  have hstage :
      zcCompletedGroupAlgebraStageToFoxAlgebraicStage
          (C := C) (X := X) (H := H) N i.1.modulus i dvd_rfl qmap =
        MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff i.1.modulus) qmap := by
    apply MonoidAlgebra.ringHom_ext
    · intro r
      rw [zcCompletedGroupAlgebraStageToFoxAlgebraicStage_single]
      rw [modNCompletedCoeffMap_rfl, RingHom.id_apply,
        MonoidAlgebra.mapDomainRingHom_apply,
        MonoidAlgebra.mapDomain_single, map_one]
    · intro q
      rw [← MonoidAlgebra.of_apply,
        zcCompletedGroupAlgebraStageToFoxAlgebraicStage_of]
      rw [MonoidAlgebra.mapDomainRingHom_apply]
      change
        MonoidAlgebra.single (qmap q) 1 =
          MonoidAlgebra.mapDomain qmap (MonoidAlgebra.single q 1)
      exact MonoidAlgebra.mapDomain_single.symm
  rw [hstage]
  intro x y hxy
  exact (MonoidAlgebra.mapDomain_injective
    (R := ModNCompletedCoeff i.1.modulus) hqmap) (by
      simpa [MonoidAlgebra.mapDomainRingHom_apply] using hxy)

/-- The resulting completed-to-finite coefficient map. -/
def zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap
    (hmod : n ∣ i.1.modulus)
    (qmap : CompletedGroupAlgebraQuotientInClass H C i.2 →*
      foxAlgebraicStageTargetQuotient (X := X) N) :
    ZCCompletedGroupAlgebra C H →+*
      foxAlgebraicStageTargetGroupAlgebra (X := X) N n :=
  (zcCompletedGroupAlgebraStageToFoxAlgebraicStage
    (C := C) (X := X) (H := H) N n i hmod qmap).comp
    (zcCompletedGroupAlgebraProjectionRingHom C H i)

omit [DecidableEq X] [Fact (0 < n)] in
/--
The Fox algebraic stage coefficient map evaluates a completed element by stage projection followed
by the prescribed target quotient and coefficient maps.
-/
@[simp]
theorem zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap_apply
    (hmod : n ∣ i.1.modulus)
    (qmap : CompletedGroupAlgebraQuotientInClass H C i.2 →*
      foxAlgebraicStageTargetQuotient (X := X) N)
    (a : ZCCompletedGroupAlgebra C H) :
    zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap
        (C := C) (X := X) (H := H) N n i hmod qmap a =
      zcCompletedGroupAlgebraStageToFoxAlgebraicStage
        (C := C) (X := X) (H := H) N n i hmod qmap
        (zcCompletedGroupAlgebraProjection C H i a) :=
  rfl

omit [DecidableEq X] [Fact (0 < n)] in
/-- Group-like formula for the completed-to-finite coefficient map. -/
theorem zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap_groupLike
    (hmod : n ∣ i.1.modulus)
    (qmap : CompletedGroupAlgebraQuotientInClass H C i.2 →*
      foxAlgebraicStageTargetQuotient (X := X) N)
    (h : H) :
    zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap
        (C := C) (X := X) (H := H) N n i hmod qmap
        (zcGroupLike C H h) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N)
        (qmap (QuotientGroup.mk h)) := by
  rw [zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap_apply,
    zcCompletedGroupAlgebraProjection_groupLike]
  erw [zcCompletedGroupAlgebraStageToFoxAlgebraicStage_of]

omit [DecidableEq X] [Fact (0 < n)] in
/-- Group-like formula rewritten through a named finite right quotient map. -/
theorem zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap_groupLike_eq_stageRight
    (hmod : n ∣ i.1.modulus)
    (qmap : CompletedGroupAlgebraQuotientInClass H C i.2 →*
      foxAlgebraicStageTargetQuotient (X := X) N)
    (stageRight : H →* foxAlgebraicStageTargetQuotient (X := X) N)
    (hqmap : ∀ h : H, qmap (QuotientGroup.mk h) = stageRight h)
    (h : H) :
    zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap
        (C := C) (X := X) (H := H) N n i hmod qmap
        (zcGroupLike C H h) =
      MonoidAlgebra.of (ModNCompletedCoeff n)
        (foxAlgebraicStageTargetQuotient (X := X) N) (stageRight h) := by
  rw [zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap_groupLike]
  rw [hqmap h]

end OneStageToFiniteFox

section SingleCoefficientTransitions

variable {X : Type u} [DecidableEq X]
variable {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
variable (hNM : N ≤ M)
variable {n m : ℕ} [Fact (0 < n)] [Fact (0 < m)]
variable (hnm : n ∣ m)

omit [DecidableEq X] [Fact (0 < n)] in
/-- Target quotient maps send a single group-algebra coefficient to the mapped basis element. -/
theorem foxAlgebraicStageTargetGroupAlgebraMap_single_apply
    (q : foxAlgebraicStageTargetQuotient (X := X) N)
    (a : ModNCompletedCoeff n) :
    foxAlgebraicStageTargetGroupAlgebraMap (X := X) hNM n
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single (foxAlgebraicStageTargetQuotientMap (X := X) hNM q) a := by
  rw [foxAlgebraicStageTargetGroupAlgebraMap]
  rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/-- The bifiltered target transition on a single group-algebra coefficient. -/
theorem foxAlgebraicStageBifilteredTargetGroupAlgebraMap_single_apply
    (q : foxAlgebraicStageTargetQuotient (X := X) N)
    (a : ModNCompletedCoeff m) :
    foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
        (MonoidAlgebra.single q a) =
      MonoidAlgebra.single (foxAlgebraicStageTargetQuotientMap (X := X) hNM q)
        (modNCompletedCoeffMap (n := n) (m := m) hnm a) := by
  rw [foxAlgebraicStageBifilteredTargetGroupAlgebraMap_apply,
    foxAlgebraicStageTargetGroupAlgebraCoeffMap_single_apply,
    foxAlgebraicStageTargetGroupAlgebraMap_single_apply]

end SingleCoefficientTransitions

section Transition

variable {C : ProCGroups.FiniteGroupClass}
variable {X H : Type u}
variable [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable {N M : Subgroup (FreeGroup X)} [N.Normal] [M.Normal]
variable (hNM : N ≤ M)
variable {n m : ℕ} [Fact (0 < n)] [Fact (0 < m)]
variable (hnm : n ∣ m)
variable {i j : ZCCompletedGroupAlgebraIndex C H}
variable (hij : i ≤ j)

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/--
Stage-to-finite maps commute with completed-group-algebra transitions when the coefficient
reductions and quotient maps commute.
-/
theorem zcCompletedGroupAlgebraStageToFoxAlgebraicStage_transition
    (hmod_i : n ∣ i.1.modulus)
    (hmod_j : m ∣ j.1.modulus)
    (hcoeff : ∀ a : ModNCompletedCoeff j.1.modulus,
      modNCompletedCoeffMap (n := n) (m := i.1.modulus) hmod_i
          (modNCompletedCoeffMap (n := i.1.modulus) (m := j.1.modulus) hij.1 a) =
        modNCompletedCoeffMap (n := n) (m := m) hnm
          (modNCompletedCoeffMap (n := m) (m := j.1.modulus) hmod_j a))
    (qmap_i : CompletedGroupAlgebraQuotientInClass H C i.2 →*
      foxAlgebraicStageTargetQuotient (X := X) M)
    (qmap_j : CompletedGroupAlgebraQuotientInClass H C j.2 →*
      foxAlgebraicStageTargetQuotient (X := X) N)
    (hqmap : ∀ q : CompletedGroupAlgebraQuotientInClass H C j.2,
      qmap_i
          ((OpenNormalSubgroupInClass.map
            (C := C) (G := H)
            (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q) =
        foxAlgebraicStageTargetQuotientMap (X := X) hNM (qmap_j q))
    (x : ZCCompletedGroupAlgebraStage C H j) :
    foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
        (zcCompletedGroupAlgebraStageToFoxAlgebraicStage
          (C := C) (X := X) (H := H) N m j hmod_j qmap_j x) =
      zcCompletedGroupAlgebraStageToFoxAlgebraicStage
        (C := C) (X := X) (H := H) M n i hmod_i qmap_i
        (zcCompletedGroupAlgebraTransition C H hij x) := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  let : Fact (0 < j.1.modulus) := ⟨j.1.positive⟩
  refine MonoidAlgebra.induction_linear
    (motive := fun x : ZCCompletedGroupAlgebraStage C H j =>
      foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
          (zcCompletedGroupAlgebraStageToFoxAlgebraicStage
            (C := C) (X := X) (H := H) N m j hmod_j qmap_j x) =
        zcCompletedGroupAlgebraStageToFoxAlgebraicStage
          (C := C) (X := X) (H := H) M n i hmod_i qmap_i
          (zcCompletedGroupAlgebraTransition C H hij x))
    x ?_ ?_ ?_
  · rw [map_zero, map_zero, map_zero]
    exact (map_zero
      (zcCompletedGroupAlgebraStageToFoxAlgebraicStage
        (C := C) (X := X) (H := H) M n i hmod_i qmap_i)).symm
  · intro x y hx hy
    rw [map_add, map_add, map_add, hx, hy]
    exact (map_add
      (zcCompletedGroupAlgebraStageToFoxAlgebraicStage
        (C := C) (X := X) (H := H) M n i hmod_i qmap_i)
      ((zcCompletedGroupAlgebraTransition C H hij) x)
      ((zcCompletedGroupAlgebraTransition C H hij) y)).symm
  · intro q a
    calc
      foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
          (zcCompletedGroupAlgebraStageToFoxAlgebraicStage
            (C := C) (X := X) (H := H) N m j hmod_j qmap_j
            (MonoidAlgebra.single q a)) =
        MonoidAlgebra.single
          (foxAlgebraicStageTargetQuotientMap (X := X) hNM (qmap_j q))
          (modNCompletedCoeffMap (n := n) (m := m) hnm
            (modNCompletedCoeffMap
              (n := m) (m := j.1.modulus) hmod_j a)) := by
          rw [zcCompletedGroupAlgebraStageToFoxAlgebraicStage_single,
            foxAlgebraicStageBifilteredTargetGroupAlgebraMap_single_apply]
      _ = MonoidAlgebra.single
          (qmap_i
            ((OpenNormalSubgroupInClass.map
              (C := C) (G := H)
              (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q))
          (modNCompletedCoeffMap (n := n) (m := i.1.modulus) hmod_i
            (modNCompletedCoeffMap
              (n := i.1.modulus) (m := j.1.modulus) hij.1 a)) := by
          rw [hqmap q, hcoeff a]
      _ = zcCompletedGroupAlgebraStageToFoxAlgebraicStage
          (C := C) (X := X) (H := H) M n i hmod_i qmap_i
          (MonoidAlgebra.single
            ((OpenNormalSubgroupInClass.map
              (C := C) (G := H)
              (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q)
            (modNCompletedCoeffMap
              (n := i.1.modulus) (m := j.1.modulus) hij.1 a)) := by
          erw [zcCompletedGroupAlgebraStageToFoxAlgebraicStage_single]
      _ = zcCompletedGroupAlgebraStageToFoxAlgebraicStage
          (C := C) (X := X) (H := H) M n i hmod_i qmap_i
          (zcCompletedGroupAlgebraTransition C H hij
            (MonoidAlgebra.single q a)) := by
          exact congrArg
            (zcCompletedGroupAlgebraStageToFoxAlgebraicStage
              (C := C) (X := X) (H := H) M n i hmod_i qmap_i)
            (zcCompletedGroupAlgebraTransition_single C H hij q a).symm

omit [DecidableEq X] [Fact (0 < n)] [Fact (0 < m)] in
/--
The completed coefficient maps built from stage projections are compatible on completed points
once the underlying finite-stage maps commute with transitions.
-/
theorem zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap_transition
    (hmod_i : n ∣ i.1.modulus)
    (hmod_j : m ∣ j.1.modulus)
    (hcoeff : ∀ a : ModNCompletedCoeff j.1.modulus,
      modNCompletedCoeffMap (n := n) (m := i.1.modulus) hmod_i
          (modNCompletedCoeffMap (n := i.1.modulus) (m := j.1.modulus) hij.1 a) =
        modNCompletedCoeffMap (n := n) (m := m) hnm
          (modNCompletedCoeffMap (n := m) (m := j.1.modulus) hmod_j a))
    (qmap_i : CompletedGroupAlgebraQuotientInClass H C i.2 →*
      foxAlgebraicStageTargetQuotient (X := X) M)
    (qmap_j : CompletedGroupAlgebraQuotientInClass H C j.2 →*
      foxAlgebraicStageTargetQuotient (X := X) N)
    (hqmap : ∀ q : CompletedGroupAlgebraQuotientInClass H C j.2,
      qmap_i
          ((OpenNormalSubgroupInClass.map
            (C := C) (G := H)
            (U := OrderDual.ofDual i.2) (V := OrderDual.ofDual j.2) hij.2) q) =
        foxAlgebraicStageTargetQuotientMap (X := X) hNM (qmap_j q))
    (a : ZCCompletedGroupAlgebra C H) :
    foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
        (zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap
          (C := C) (X := X) (H := H) N m j hmod_j qmap_j a) =
      zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap
        (C := C) (X := X) (H := H) M n i hmod_i qmap_i a := by
    rw [zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap_apply,
      zcCompletedGroupAlgebraFoxAlgebraicStageCoeffMap_apply]
    change foxAlgebraicStageBifilteredTargetGroupAlgebraMap (X := X) hNM hnm
        (zcCompletedGroupAlgebraStageToFoxAlgebraicStage
          (C := C) (X := X) (H := H) N m j hmod_j qmap_j (a.1 j)) =
      zcCompletedGroupAlgebraStageToFoxAlgebraicStage
        (C := C) (X := X) (H := H) M n i hmod_i qmap_i (a.1 i)
    rw [← a.2 i j hij]
    exact zcCompletedGroupAlgebraStageToFoxAlgebraicStage_transition
      (C := C) (X := X) (H := H) hNM hnm hij hmod_i hmod_j hcoeff
      qmap_i qmap_j hqmap
      (a.1 j)

end Transition

end

end FoxDifferential
