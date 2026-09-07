import ProCGroups.FoxDifferential.Completed.Continuous.Universal.System

set_option autoImplicit false

/-!
# Fox differential: completed — continuous — universal — natural topology

The principal declarations in this module are:

- `zcCompletedDifferentialModuleStageProjectionAdd`
  The additive finite-stage projection from the algebraic completed differential module.
- `zcCompletedDifferentialModuleStageProjectionProduct`
  The product of all finite source/target/coefficient projections of the algebraic quotient.
- `zcCompletedDifferentialModuleStageProjectionAdd_apply`
  The additive stage projection has the same underlying function as the unbundled completed
  differential-module stage projection.
- `zcCompletedDifferentialModuleStageProjectionAdd_universal`
  The additive finite-stage projection sends the universal differential to the corresponding
  finite-stage differential.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.Completion
open ProCGroups.ProC
open scoped commutatorElement

universe u

variable (C : ProCGroups.FiniteGroupClass.{u})
variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable (ψ : G →* H)

/-- The additive finite-stage projection from the algebraic completed differential module. -/
def zcCompletedDifferentialModuleStageProjectionAdd
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    ZCCompletedDifferentialModule C ψ →+
      ZCCompletedDifferentialModuleStage C ψ i :=
  (zcCompletedDifferentialModuleStageProjection C ψ i).toAddMonoidHom

omit [IsTopologicalGroup G] in
/--
The additive stage projection has the same underlying function as the unbundled completed
differential-module stage projection.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageProjectionAdd_apply
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (a : ZCCompletedDifferentialModule C ψ) :
    zcCompletedDifferentialModuleStageProjectionAdd C ψ i a =
      zcCompletedDifferentialModuleStageProjection C ψ i a :=
  rfl

omit [IsTopologicalGroup G] in
/--
The additive finite-stage projection sends the universal differential to the corresponding
finite-stage differential.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageProjectionAdd_universal
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcCompletedDifferentialModuleStageProjectionAdd C ψ i
        (zcUniversalDifferential C ψ g) =
      zcCompletedDifferentialModuleStageDifferential C ψ i g :=
  zcCompletedDifferentialModuleStageProjection_universal C ψ i g

/-- The product of all finite source/target/coefficient projections of the algebraic quotient. -/
def zcCompletedDifferentialModuleStageProjectionProduct :
    ZCCompletedDifferentialModule C ψ →
      ∀ i : ZCCompletedDifferentialModuleIndex C ψ,
        ZCCompletedDifferentialModuleStage C ψ i :=
  fun a i => zcCompletedDifferentialModuleStageProjectionAdd C ψ i a

omit [IsTopologicalGroup G] in
/-- The product of additive stage projections evaluates at `i` as the additive projection at `i`. -/
@[simp]
theorem zcCompletedDifferentialModuleStageProjectionProduct_apply
    (a : ZCCompletedDifferentialModule C ψ)
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    zcCompletedDifferentialModuleStageProjectionProduct C ψ a i =
      zcCompletedDifferentialModuleStageProjectionAdd C ψ i a :=
  rfl

/--
The finite-stage completed topology on the algebraic completed differential module. This
topology is named deliberately: it is not installed as a global instance.
-/
@[implicit_reducible]
def zcCompletedDifferentialModuleNaturalTopology :
    TopologicalSpace (ZCCompletedDifferentialModule C ψ) :=
  TopologicalSpace.induced
    (zcCompletedDifferentialModuleStageProjectionProduct C ψ) inferInstance

omit [IsTopologicalGroup G] in
/-- The product map defining the finite-stage completed topology is continuous. -/
theorem continuous_zcCompletedDifferentialModuleStageProjectionProduct_naturalTopology :
    @Continuous (ZCCompletedDifferentialModule C ψ)
      (∀ i : ZCCompletedDifferentialModuleIndex C ψ,
        ZCCompletedDifferentialModuleStage C ψ i)
      (zcCompletedDifferentialModuleNaturalTopology C ψ) inferInstance
      (zcCompletedDifferentialModuleStageProjectionProduct C ψ) :=
  continuous_induced_dom

omit [IsTopologicalGroup G] in
/-- Each finite-stage projection is continuous for the finite-stage completed topology. -/
theorem continuous_zcCompletedDifferentialModuleStageProjectionAdd_naturalTopology
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    @Continuous (ZCCompletedDifferentialModule C ψ)
      (ZCCompletedDifferentialModuleStage C ψ i)
      (zcCompletedDifferentialModuleNaturalTopology C ψ) inferInstance
      (zcCompletedDifferentialModuleStageProjectionAdd C ψ i) := by
  change @Continuous (ZCCompletedDifferentialModule C ψ)
      (ZCCompletedDifferentialModuleStage C ψ i)
      (zcCompletedDifferentialModuleNaturalTopology C ψ) inferInstance
      (zcCompletedDifferentialModuleStageProjection C ψ i)
  have hprod :=
    continuous_zcCompletedDifferentialModuleStageProjectionProduct_naturalTopology C ψ
  simpa [zcCompletedDifferentialModuleStageProjectionProduct, Function.comp_def] using
    (@Continuous.comp
      (ZCCompletedDifferentialModule C ψ)
      (∀ i : ZCCompletedDifferentialModuleIndex C ψ,
        ZCCompletedDifferentialModuleStage C ψ i)
      (ZCCompletedDifferentialModuleStage C ψ i)
      (zcCompletedDifferentialModuleNaturalTopology C ψ) inferInstance inferInstance
      (f := zcCompletedDifferentialModuleStageProjectionProduct C ψ)
      (g := fun x => x i)
      (continuous_apply i) hprod)

omit [IsTopologicalGroup G] in
/--
Continuity of the completed differential-module stage projection is characterized by the natural
topology.
-/
theorem continuous_zcCompletedDifferentialModuleStageProjection_naturalTopology
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    @Continuous (ZCCompletedDifferentialModule C ψ)
      (ZCCompletedDifferentialModuleStage C ψ i)
      (zcCompletedDifferentialModuleNaturalTopology C ψ) inferInstance
      (zcCompletedDifferentialModuleStageProjection C ψ i) := by
  change @Continuous (ZCCompletedDifferentialModule C ψ)
      (ZCCompletedDifferentialModuleStage C ψ i)
      (zcCompletedDifferentialModuleNaturalTopology C ψ) inferInstance
      (zcCompletedDifferentialModuleStageProjectionAdd C ψ i)
  exact continuous_zcCompletedDifferentialModuleStageProjectionAdd_naturalTopology C ψ i

/--
A named predicate for the algebraic separation still needed to make the natural topology
Hausdorff. It is false for arbitrary sources without a residual finite-stage hypothesis.
-/
def zcCompletedDifferentialModuleStageProjectionsSeparate : Prop :=
  Function.Injective (zcCompletedDifferentialModuleStageProjectionProduct C ψ)

/--
Pre-quotient finite-stage separation says that elements killed by every finite-stage
crossed-differential projection are exactly the defining crossed-differential relations.
-/
def zcCompletedDifferentialModulePreStageProjectionsSeparate : Prop :=
  ∀ x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G,
    (∀ i : ZCCompletedDifferentialModuleIndex C ψ,
      crossedDifferentialModuleLiftLinear
        (R := ZCCompletedGroupAlgebra C H)
        (zcCompletedDifferentialModuleStageDifferential C ψ i) x = 0) →
    x ∈ crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ)

/-- The kernel on the pre-module cut out by one finite source/target/coefficient stage. -/
def zcCompletedDifferentialModulePreStageKernel
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    Submodule (ZCCompletedGroupAlgebra C H)
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
  LinearMap.ker
    (crossedDifferentialModuleLiftLinear
      (R := ZCCompletedGroupAlgebra C H)
      (zcCompletedDifferentialModuleStageDifferential C ψ i))

omit [IsTopologicalGroup G] in
/--
Membership in a completed differential-module pre-stage kernel is equivalent to vanishing of the
corresponding finite-stage coordinate.
-/
@[simp]
theorem mem_zcCompletedDifferentialModulePreStageKernel_iff
    {C : ProCGroups.FiniteGroupClass.{u}} {ψ : G →* H}
    {i : ZCCompletedDifferentialModuleIndex C ψ}
    {x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G} :
    x ∈ zcCompletedDifferentialModulePreStageKernel C ψ i ↔
      crossedDifferentialModuleLiftLinear
        (R := ZCCompletedGroupAlgebra C H)
        (zcCompletedDifferentialModuleStageDifferential C ψ i) x = 0 :=
  Iff.rfl

omit [IsTopologicalGroup G] in
/--
Membership in a finite pre-stage kernel is equivalently membership of the explicit
source-and-coefficient reduction in the finite crossed-differential relation submodule.
-/
theorem mem_zcDiffModulePreStageKernel_iff_preStageMap_mem_relSubmodule
    {C : ProCGroups.FiniteGroupClass.{u}} {ψ : G →* H}
    {i : ZCCompletedDifferentialModuleIndex C ψ}
    {x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G} :
    x ∈ zcCompletedDifferentialModulePreStageKernel C ψ i ↔
      zcCompletedDifferentialModulePreStageMap C ψ i x ∈
        crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i) := by
  constructor
  · intro hx
    have hq :
        (crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
            (zcCompletedDifferentialModulePreStageMap C ψ i x) = 0 := by
      rw [zcCompletedDifferentialModulePreStageMap_mkQ]
      exact hx
    exact
      (Submodule.Quotient.mk_eq_zero
        (p := crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i))
        (x := zcCompletedDifferentialModulePreStageMap C ψ i x)).1 hq
  · intro hx
    have hq :
        (crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
            (zcCompletedDifferentialModulePreStageMap C ψ i x) = 0 :=
      (Submodule.Quotient.mk_eq_zero
        (p := crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i))
        (x := zcCompletedDifferentialModulePreStageMap C ψ i x)).2 hx
    rw [mem_zcCompletedDifferentialModulePreStageKernel_iff]
    rw [← zcCompletedDifferentialModulePreStageMap_mkQ]
    exact hq

omit [IsTopologicalGroup G] in
/-- Every defining crossed-differential relation is killed by every finite stage. -/
theorem crossedDiffRelSubmodule_le_zcDiffModulePreStageKernel
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) ≤
      zcCompletedDifferentialModulePreStageKernel C ψ i := by
  simpa [zcCompletedDifferentialModulePreStageKernel] using
    crossedHomRelationSubmodule_le_ker
      (A := ZCCompletedDifferentialModuleStage C ψ i)
      (zcCompletedGroupAlgebraScalar C ψ)
      (zcCompletedDifferentialModuleStageDifferential C ψ i)

omit [IsTopologicalGroup G] in
/--
The explicit finite pre-stage map sends completed crossed-differential relations to finite
crossed-differential relations.
-/
theorem zcCompletedDifferentialModulePreStageMap_mem_relationSubmodule_of_mem
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    {x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G}
    (hx : x ∈ crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ)) :
    zcCompletedDifferentialModulePreStageMap C ψ i x ∈
      crossedDifferentialRelationSubmodule
        (zcCompletedDifferentialModuleStageScalar C ψ i) :=
  (mem_zcDiffModulePreStageKernel_iff_preStageMap_mem_relSubmodule (C := C) (ψ := ψ) (i := i) (x
      := x)).1
    (crossedDiffRelSubmodule_le_zcDiffModulePreStageKernel
      (C := C) (ψ := ψ) i hx)

/-- The common finite-stage kernel on the pre-module. -/
def zcCompletedDifferentialModulePreStageKernelIntersection :
    Submodule (ZCCompletedGroupAlgebra C H)
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
  ⨅ i : ZCCompletedDifferentialModuleIndex C ψ,
    zcCompletedDifferentialModulePreStageKernel C ψ i

omit [IsTopologicalGroup G] in
/--
Membership in the intersection of completed differential-module pre-stage kernels is equivalent
to vanishing of the corresponding finite-stage coordinate.
-/
theorem mem_zcCompletedDifferentialModulePreStageKernelIntersection_iff
    {C : ProCGroups.FiniteGroupClass.{u}} {ψ : G →* H}
    {x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G} :
    x ∈ zcCompletedDifferentialModulePreStageKernelIntersection C ψ ↔
      ∀ i : ZCCompletedDifferentialModuleIndex C ψ,
        zcCompletedDifferentialModulePreStageMap C ψ i x ∈
          crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψ i) := by
  rw [zcCompletedDifferentialModulePreStageKernelIntersection, Submodule.mem_iInf]
  constructor
  · intro hx i
    exact
      (mem_zcDiffModulePreStageKernel_iff_preStageMap_mem_relSubmodule (C := C) (ψ := ψ) (i :=
          i) (x := x)).1 (hx i)
  · intro hx i
    exact
      (mem_zcDiffModulePreStageKernel_iff_preStageMap_mem_relSubmodule (C := C) (ψ := ψ) (i :=
          i) (x := x)).2 (hx i)

/--
The finite-stage closed relation submodule defining the separated completed
\(\psi\)-differential module.
-/
abbrev zcCompletedDifferentialRelationFiniteClosedSubmodule :
    Submodule (ZCCompletedGroupAlgebra C H)
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
  zcCompletedDifferentialModulePreStageKernelIntersection C ψ

/--
The separated completed \(\psi\)-differential module. This is the finite-stage separated
quotient used for the profinite Crowell middle term.
-/
abbrev ZCSeparatedCompletedDifferentialModule : Type u :=
  CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G ⧸
    zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ

/--
Mathematical Crowell module \(A_{\psi}(C)\). By convention in this development, \(A_{\psi}(C)\)
is the closed/separated finite-stage quotient, not the algebraic quotient of the
\(\mathbb{Z}_C\)-completed differential module.
-/
abbrev ZCApsi : Type u :=
  ZCSeparatedCompletedDifferentialModule C ψ

omit [IsTopologicalGroup G] in
/-- Algebraic crossed-differential relations vanish in the finite-stage separated quotient. -/
theorem crossedDifferentialRelationSubmodule_le_finiteClosedSubmodule :
    crossedDifferentialRelationSubmodule
      (zcCompletedGroupAlgebraScalar C ψ) ≤
    zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ := by
  intro x hx
  rw [zcCompletedDifferentialRelationFiniteClosedSubmodule,
    mem_zcCompletedDifferentialModulePreStageKernelIntersection_iff]
  intro i
  exact zcCompletedDifferentialModulePreStageMap_mem_relationSubmodule_of_mem C ψ i hx

/-- The universal crossed differential into the separated completed quotient. -/
def zcSeparatedUniversalDifferential :
    ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCSeparatedCompletedDifferentialModule C ψ) where
  toFun g :=
    (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ
      (Finsupp.single g 1)
  map_mul' := by
    intro g h
    let δ : G → ZCSeparatedCompletedDifferentialModule C ψ := fun x =>
      (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ
        (Finsupp.single x 1)
    change δ (g * h) = δ g + zcCompletedGroupAlgebraScalar C ψ g • δ h
    have hzero :
        (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ
            (crossedDifferentialRelationElement
              (zcCompletedGroupAlgebraScalar C ψ) g h) = 0 := by
      exact
        (Submodule.Quotient.mk_eq_zero
          (p := zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ)
          (x := crossedDifferentialRelationElement
            (zcCompletedGroupAlgebraScalar C ψ) g h)).2
          (crossedDifferentialRelationSubmodule_le_finiteClosedSubmodule C ψ
            (crossedDifferentialRelationElement_mem
              (zcCompletedGroupAlgebraScalar C ψ) g h))
    have hzero' :
        δ (g * h) -
            (δ g +
              (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ
                (zcCompletedGroupAlgebraScalar C ψ g • Finsupp.single h 1)) = 0 := by
      simpa [δ, crossedDifferentialRelationElement] using hzero
    have hsmul :
        (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ
            (zcCompletedGroupAlgebraScalar C ψ g • Finsupp.single h 1) =
          zcCompletedGroupAlgebraScalar C ψ g • δ h := by
      simpa [δ, Submodule.mkQ_apply] using
        (Submodule.Quotient.mk_smul
          (p := zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ)
          (r := zcCompletedGroupAlgebraScalar C ψ g)
          (x := Finsupp.single h 1))
    rw [hsmul] at hzero'
    exact sub_eq_zero.mp hzero'

omit [IsTopologicalGroup G] in
/--
Commutator formula for the separated universal differential when the right factor lies in the
kernel of the target homomorphism.
-/
theorem zcSeparatedUniversalDifferential_commutator_right_kernel
    (g h : G) (hh : ψ h = 1) :
    zcSeparatedUniversalDifferential C ψ ⁅g, h⁆ =
      (zcGroupLike C H (ψ g) - 1) •
        zcSeparatedUniversalDifferential C ψ h := by
  let δ := zcSeparatedUniversalDifferential C ψ
  let coeff := zcCompletedGroupAlgebraScalar C ψ
  have hcomm := (zcSeparatedUniversalDifferential C ψ).map_commutator g h
  have hconj : ψ (g * h * g⁻¹) = 1 := by
    simp only [map_mul, hh, mul_one, map_inv, mul_inv_cancel]
  have hcommKer : ψ ⁅g, h⁆ = 1 := by
    simp only [commutatorElement_def, map_mul, hh, mul_one, map_inv, mul_inv_cancel, inv_one]
  calc
    δ ⁅g, h⁆ =
        δ g + zcGroupLike C H (ψ g) • δ h - δ g - δ h := by
      simpa only [δ, coeff, zcCompletedGroupAlgebraScalar_apply, hconj,
        hcommKer, map_one, one_smul] using hcomm
    _ = zcGroupLike C H (ψ g) • δ h - δ h := by
      abel
    _ = (zcGroupLike C H (ψ g) - 1) • δ h := by
      rw [sub_smul, one_smul]

omit [IsTopologicalGroup G] in
/--
A representative is zero in the separated quotient exactly when all finite reductions are finite
crossed-differential relations.
-/
theorem zcSeparatedCompletedDifferentialModule_mk_eq_zero_iff
    {C : ProCGroups.FiniteGroupClass.{u}} {ψ : G →* H}
    {x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G} :
    (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ x =
        (0 : ZCSeparatedCompletedDifferentialModule C ψ) ↔
      ∀ i : ZCCompletedDifferentialModuleIndex C ψ,
        zcCompletedDifferentialModulePreStageMap C ψ i x ∈
          crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψ i) := by
  constructor
  · intro hx
    exact
      (mem_zcCompletedDifferentialModulePreStageKernelIntersection_iff (C := C) (ψ := ψ) (x := x)).1
        ((Submodule.Quotient.mk_eq_zero
          (p := zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ)
          (x := x)).1 hx)
  · intro hx
    exact
      (Submodule.Quotient.mk_eq_zero
        (p := zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ)
        (x := x)).2
        ((mem_zcCompletedDifferentialModulePreStageKernelIntersection_iff (C := C) (ψ := ψ) (x
            := x)).2 hx)

/-- Finite-stage projection from the separated completed quotient. -/
def zcSeparatedCompletedDifferentialModuleStageProjectionAdd
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    ZCSeparatedCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedDifferentialModuleStage C ψ i :=
  (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).liftQ
    (crossedDifferentialModuleLiftLinear
      (R := ZCCompletedGroupAlgebra C H)
      (zcCompletedDifferentialModuleStageDifferential C ψ i))
    (by
      intro x hx
      rw [LinearMap.mem_ker]
      have hxstage :
          zcCompletedDifferentialModulePreStageMap C ψ i x ∈
            crossedDifferentialRelationSubmodule
              (zcCompletedDifferentialModuleStageScalar C ψ i) :=
        (mem_zcCompletedDifferentialModulePreStageKernelIntersection_iff (C := C) (ψ := ψ) (x :=
            x)).1
          (by
            simpa [zcCompletedDifferentialRelationFiniteClosedSubmodule] using hx) i
      have hq :
          (crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
              (zcCompletedDifferentialModulePreStageMap C ψ i x) = 0 :=
        (Submodule.Quotient.mk_eq_zero
          (p := crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψ i))
          (x := zcCompletedDifferentialModulePreStageMap C ψ i x)).2 hxstage
      rw [zcCompletedDifferentialModulePreStageMap_mkQ] at hq
      exact hq)

omit [IsTopologicalGroup G] in
/--
The separated finite-stage projection of a quotient representative is the finite-stage
crossed-differential lift of that representative.
-/
@[simp]
theorem zcSeparatedCompletedDifferentialModuleStageProjectionAdd_mkQ
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :
    zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i
        ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ x) =
      crossedDifferentialModuleLiftLinear
        (R := ZCCompletedGroupAlgebra C H)
        (zcCompletedDifferentialModuleStageDifferential C ψ i) x := by
  rw [zcSeparatedCompletedDifferentialModuleStageProjectionAdd, Submodule.mkQ_apply,
    Submodule.liftQ_apply]

omit [IsTopologicalGroup G] in
/--
The separated finite-stage projection sends the separated universal differential to the
corresponding finite-stage differential.
-/
@[simp]
theorem zcSeparatedCompletedDifferentialModuleStageProjectionAdd_universal
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i
        (zcSeparatedUniversalDifferential C ψ g) =
      zcCompletedDifferentialModuleStageDifferential C ψ i g := by
  change
    zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i
        ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ
          (Finsupp.single g 1)) =
      zcCompletedDifferentialModuleStageDifferential C ψ i g
  rw [zcSeparatedCompletedDifferentialModuleStageProjectionAdd_mkQ]
  simp only [crossedDifferentialModuleLiftLinear_single, one_smul]

/-- The product of all finite-stage projections from the separated completed quotient. -/
def zcSeparatedCompletedDifferentialModuleStageProjectionProduct :
    ZCSeparatedCompletedDifferentialModule C ψ →
      ∀ i : ZCCompletedDifferentialModuleIndex C ψ,
        ZCCompletedDifferentialModuleStage C ψ i :=
  fun a i => zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i a

omit [IsTopologicalGroup G] in
/--
The product projection from the separated completed differential module evaluates at `i` as its
additive stage projection.
-/
@[simp]
theorem zcSeparatedCompletedDifferentialModuleStageProjectionProduct_apply
    (a : ZCSeparatedCompletedDifferentialModule C ψ)
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    zcSeparatedCompletedDifferentialModuleStageProjectionProduct C ψ a i =
      zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i a :=
  rfl

omit [IsTopologicalGroup G] in
/-- The finite-stage projections separate points of the separated completed quotient. -/
theorem zcSeparatedCompletedDifferentialModuleStageProjectionsSeparate :
    ∀ x : ZCSeparatedCompletedDifferentialModule C ψ,
      (∀ i : ZCCompletedDifferentialModuleIndex C ψ,
        zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i x = 0) →
      x = 0 := by
  intro x
  refine Submodule.Quotient.induction_on
    (p := zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ)
    (C := fun x =>
      (∀ i : ZCCompletedDifferentialModuleIndex C ψ,
        zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i x = 0) →
      x = 0)
    x ?_
  intro y hy
  apply
    (Submodule.Quotient.mk_eq_zero
      (p := zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ)
      (x := y)).2
  exact
    (mem_zcCompletedDifferentialModulePreStageKernelIntersection_iff (C := C) (ψ := ψ) (x := y)).2
      (by
        intro i
        have hlin :
            crossedDifferentialModuleLiftLinear
              (R := ZCCompletedGroupAlgebra C H)
              (zcCompletedDifferentialModuleStageDifferential C ψ i) y = 0 := by
          have hyi := hy i
          change zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i
              ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ y) = 0 at hyi
          rw [zcSeparatedCompletedDifferentialModuleStageProjectionAdd_mkQ] at hyi
          exact hyi
        have hq :
            (crossedDifferentialRelationSubmodule
              (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
                (zcCompletedDifferentialModulePreStageMap C ψ i y) = 0 := by
          rw [zcCompletedDifferentialModulePreStageMap_mkQ]
          exact hlin
        exact
          (Submodule.Quotient.mk_eq_zero
            (p := crossedDifferentialRelationSubmodule
              (zcCompletedDifferentialModuleStageScalar C ψ i))
            (x := zcCompletedDifferentialModulePreStageMap C ψ i y)).1 hq)

omit [IsTopologicalGroup G] in
/-- The finite-stage projection product is injective on the separated completed quotient. -/
theorem zcSeparatedCompletedDifferentialModuleStageProjectionProduct_injective :
    Function.Injective
      (zcSeparatedCompletedDifferentialModuleStageProjectionProduct C ψ) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply zcSeparatedCompletedDifferentialModuleStageProjectionsSeparate C ψ
  intro i
  have hi :
      zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i x =
        zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i y := by
    simpa [zcSeparatedCompletedDifferentialModuleStageProjectionProduct] using congrFun hxy i
  rw [map_sub, hi, sub_self]

omit [IsTopologicalGroup G] in
/-- Extensionality for the separated completed quotient by finite-stage projections. -/
theorem zcSeparatedCompletedDifferentialModuleStageProjection_ext
    {a b : ZCSeparatedCompletedDifferentialModule C ψ}
    (h : ∀ i : ZCCompletedDifferentialModuleIndex C ψ,
      zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i a =
        zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i b) :
    a = b :=
  zcSeparatedCompletedDifferentialModuleStageProjectionProduct_injective C ψ
    (funext h)

/-- The natural map from the algebraic quotient to the finite-stage separated quotient. -/
def zcCompletedDifferentialModuleToSeparated :
    ZCCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H]
      ZCSeparatedCompletedDifferentialModule C ψ :=
  (crossedDifferentialRelationSubmodule
    (zcCompletedGroupAlgebraScalar C ψ)).liftQ
    (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ
    (by
      intro x hx
      rw [LinearMap.mem_ker]
      exact
        (Submodule.Quotient.mk_eq_zero
          (p := zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ)
          (x := x)).2
          (crossedDifferentialRelationSubmodule_le_finiteClosedSubmodule C ψ hx))

omit [IsTopologicalGroup G] in
/--
The quotient map to the separated completed module sends the universal differential to the
separated universal differential.
-/
@[simp]
theorem zcCompletedDifferentialModuleToSeparated_universal (g : G) :
    zcCompletedDifferentialModuleToSeparated C ψ
      (zcUniversalDifferential C ψ g) =
    zcSeparatedUniversalDifferential C ψ g := by
  change
    zcCompletedDifferentialModuleToSeparated C ψ
        ((crossedDifferentialRelationSubmodule
          (zcCompletedGroupAlgebraScalar C ψ)).mkQ (Finsupp.single g 1)) =
      (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ
        (Finsupp.single g 1)
  rw [zcCompletedDifferentialModuleToSeparated, Submodule.mkQ_apply,
    Submodule.liftQ_apply]

omit [IsTopologicalGroup G] in
/--
The pre-quotient completed boundary kills the finite-stage closed relation submodule. This is
the descent input for the separated boundary \(A_{\psi}(C)_{\mathrm{sep}} \to
\mathbb{Z}_C\llbracket H\rrbracket\).
-/
theorem crossedDifferentialBoundaryLiftLinear_kills_finiteClosedSubmodule
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψc : ContinuousMonoidHom G H)
    {x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G}
    (hx : x ∈ zcCompletedDifferentialRelationFiniteClosedSubmodule C ψc.toMonoidHom) :
    crossedDifferentialModuleLiftLinear
        (R := ZCCompletedGroupAlgebra C H)
        (zcCompletedGroupAlgebraBoundary C ψc.toMonoidHom) x = 0 := by
  apply zcCompletedGroupAlgebraProjection_ext
  intro j
  let i := zcCompletedDifferentialModuleComapIndex C hC ψc j
  have hxall :
      ∀ i : ZCCompletedDifferentialModuleIndex C ψc.toMonoidHom,
        zcCompletedDifferentialModulePreStageMap C ψc.toMonoidHom i x ∈
          crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψc.toMonoidHom i) := by
    rw [zcCompletedDifferentialRelationFiniteClosedSubmodule] at hx
    exact
      (mem_zcCompletedDifferentialModulePreStageKernelIntersection_iff (C := C) (ψ :=
          ψc.toMonoidHom) (x := x)).1 hx
  have hxstage :
      zcCompletedDifferentialModulePreStageMap C ψc.toMonoidHom i x ∈
        crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψc.toMonoidHom i) :=
    hxall i
  have hstage_zero :
      zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap C ψc.toMonoidHom i
          ((crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψc.toMonoidHom i)).mkQ
              (zcCompletedDifferentialModulePreStageMap C ψc.toMonoidHom i x)) = 0 := by
    have hq :
        (crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψc.toMonoidHom i)).mkQ
          (zcCompletedDifferentialModulePreStageMap C ψc.toMonoidHom i x) = 0 :=
      (Submodule.Quotient.mk_eq_zero
        (p := crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψc.toMonoidHom i))
        (x := zcCompletedDifferentialModulePreStageMap C ψc.toMonoidHom i x)).2 hxstage
    rw [hq, map_zero]
  have hcompat :=
    congrArg
      (fun f =>
        f
          ((crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom)).mkQ x))
      (zcDiffModuleStageBoundaryCompletedLinearMap_comp_stageProj
        C ψc.toMonoidHom i)
  have hstage_proj :
      zcCompletedDifferentialModuleStageProjection C ψc.toMonoidHom i
          ((crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom)).mkQ x) =
        (crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψc.toMonoidHom i)).mkQ
            (zcCompletedDifferentialModulePreStageMap C ψc.toMonoidHom i x) := by
    rw [zcCompletedDifferentialModuleStageProjection_mkQ]
    exact
      (zcCompletedDifferentialModulePreStageMap_mkQ
        C ψc.toMonoidHom i x).symm
  have hboundary_quot :
      zcToCompletedGroupAlgebra C ψc.toMonoidHom
          ((crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom)).mkQ x) =
        crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H)
          (zcCompletedGroupAlgebraBoundary C ψc.toMonoidHom) x := by
    rfl
  have hproj_eq :
      zcCompletedGroupAlgebraProjection C H j
          (crossedDifferentialModuleLiftLinear
            (R := ZCCompletedGroupAlgebra C H)
            (zcCompletedGroupAlgebraBoundary C ψc.toMonoidHom) x) =
        zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap C ψc.toMonoidHom i
          ((crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψc.toMonoidHom i)).mkQ
              (zcCompletedDifferentialModulePreStageMap C ψc.toMonoidHom i x)) := by
    have hfirst :
      zcCompletedGroupAlgebraProjection C H j
          (crossedDifferentialModuleLiftLinear
            (R := ZCCompletedGroupAlgebra C H)
            (zcCompletedGroupAlgebraBoundary C ψc.toMonoidHom) x) =
        zcCompletedGroupAlgebraProjection C H i.target
          (zcToCompletedGroupAlgebra C ψc.toMonoidHom
            ((crossedDifferentialRelationSubmodule
              (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom)).mkQ x)) := by
      rw [hboundary_quot]
      simp only [ContinuousMonoidHom.coe_toMonoidHom,
          zcCompletedDifferentialModuleComapIndex, i]
    have hsecond :
        zcCompletedGroupAlgebraProjection C H i.target
            (zcToCompletedGroupAlgebra C ψc.toMonoidHom
              ((crossedDifferentialRelationSubmodule
                (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom)).mkQ x)) =
        zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap C ψc.toMonoidHom i
          (zcCompletedDifferentialModuleStageProjection C ψc.toMonoidHom i
            ((crossedDifferentialRelationSubmodule
              (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom)).mkQ x)) := by
      change
        zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap C ψc.toMonoidHom i
            (zcCompletedDifferentialModuleStageProjection C ψc.toMonoidHom i
              ((crossedDifferentialRelationSubmodule
                (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom)).mkQ x)) =
          zcCompletedGroupAlgebraProjectionLinearMap C H i.target
            (zcToCompletedGroupAlgebra C ψc.toMonoidHom
              ((crossedDifferentialRelationSubmodule
                (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom)).mkQ x))
        at hcompat
      exact hcompat.symm
    have hthird :
        zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap C ψc.toMonoidHom i
            (zcCompletedDifferentialModuleStageProjection C ψc.toMonoidHom i
              ((crossedDifferentialRelationSubmodule
                (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom)).mkQ x)) =
        zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap C ψc.toMonoidHom i
          ((crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψc.toMonoidHom i)).mkQ
              (zcCompletedDifferentialModulePreStageMap C ψc.toMonoidHom i x)) := by
      rw [hstage_proj]
    exact Eq.trans hfirst (Eq.trans hsecond hthird)
  rw [hproj_eq, hstage_zero]
  simp only [zcCompletedGroupAlgebraProjection_zero]
  rfl

/-- The completed boundary descends to the separated completed differential module. -/
def zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψc : ContinuousMonoidHom G H) :
    ZCSeparatedCompletedDifferentialModule C ψc.toMonoidHom →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedGroupAlgebra C H :=
  (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψc.toMonoidHom).liftQ
    (crossedDifferentialModuleLiftLinear
      (R := ZCCompletedGroupAlgebra C H)
      (zcCompletedGroupAlgebraBoundary C ψc.toMonoidHom))
    (by
      intro x hx
      rw [LinearMap.mem_ker]
      exact crossedDifferentialBoundaryLiftLinear_kills_finiteClosedSubmodule
        C hC ψc hx)

omit [IsTopologicalGroup G] in
/--
The universal completed Fox map from the separated completed differential module to the
completed group algebra is characterized by finite-stage Fox coordinate formulas.
-/
@[simp]
theorem zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra_universal
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψc : ContinuousMonoidHom G H)
    (g : G) :
    zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra C hC ψc
        (zcSeparatedUniversalDifferential C ψc.toMonoidHom g) =
      zcCompletedGroupAlgebraBoundary C ψc.toMonoidHom g := by
  change
    zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra C hC ψc
        ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψc.toMonoidHom).mkQ
          (Finsupp.single g 1)) =
      zcCompletedGroupAlgebraBoundary C ψc.toMonoidHom g
  rw [zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra,
    Submodule.mkQ_apply, Submodule.liftQ_apply]
  simp only [ContinuousMonoidHom.coe_toMonoidHom,
    crossedDifferentialModuleLiftLinear_single, one_smul]

omit [IsTopologicalGroup G] in
/--
The completed Fox map to the completed group algebra agrees with the separated quotient map on
finite-stage coordinates.
-/
theorem zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra_comp_toSeparated
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψc : ContinuousMonoidHom G H) :
    (zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra C hC ψc).comp
      (zcCompletedDifferentialModuleToSeparated C ψc.toMonoidHom) =
    zcToCompletedGroupAlgebra C ψc.toMonoidHom := by
  apply crossedDifferentialModuleHom_ext
    (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom)
  intro g
  change
    zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra C hC ψc
        (zcCompletedDifferentialModuleToSeparated C ψc.toMonoidHom
          (zcUniversalDifferential C ψc.toMonoidHom g)) =
      zcToCompletedGroupAlgebra C ψc.toMonoidHom
        (zcUniversalDifferential C ψc.toMonoidHom g)
  rw [zcCompletedDifferentialModuleToSeparated_universal,
    zcSeparatedCompletedDifferentialModuleToCompletedGroupAlgebra_universal,
    zcToCompletedGroupAlgebra_universal]

/--
Algebraic relation-reflection form of finite-stage separation: if every finite source, target,
and coefficient reduction of a completed pre-module element is a finite crossed-differential
relation, then the original element is already in the raw completed crossed-differential
relation submodule. This is an algebraic compatibility predicate for the
\(\mathbb{Z}_C\)-completed differential module, not an input for the final separated profinite
Crowell middle term.
-/
def zcCompletedDifferentialModuleFiniteRelationReductionsReflectRelations : Prop :=
  ∀ x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G,
    (∀ i : ZCCompletedDifferentialModuleIndex C ψ,
      zcCompletedDifferentialModulePreStageMap C ψ i x ∈
        crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i)) →
    x ∈ crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ)

/--
The finite-stage topology on the completed pre-module, before quotienting by the
crossed-differential relations.
-/
@[implicit_reducible]
def zcCompletedDifferentialPreModuleNaturalTopology :
    TopologicalSpace (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
  TopologicalSpace.induced
    (zcCompletedDifferentialPreModuleStageFamilyMap C ψ) inferInstance

omit [IsTopologicalGroup G] in
/--
Each finite pre-stage reduction is continuous for the finite-stage topology on the completed
pre-module.
-/
theorem continuous_zcCompletedDifferentialModulePreStageMap_naturalTopology
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    @Continuous
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      (CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ i)
        (zcCompletedDifferentialModuleStageSource C ψ i))
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
      (⊥ : TopologicalSpace
        (CrossedDifferentialPreModule
          (zcCompletedDifferentialModuleStageRing C ψ i)
          (zcCompletedDifferentialModuleStageSource C ψ i)))
      (zcCompletedDifferentialModulePreStageMap C ψ i) := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  let S := zcCompletedDifferentialPreModuleStageSystem C ψ
  have hfamily :
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (ZCCompletedDifferentialPreModuleStageFamily C ψ)
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
        inferInstance
        (zcCompletedDifferentialPreModuleStageFamilyMap C ψ) :=
    continuous_induced_dom
  have hproj := (S.continuous_projection i).comp hfamily
  change
    @Continuous
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      (CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ i)
        (zcCompletedDifferentialModuleStageSource C ψ i))
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ) ⊥
      (zcCompletedDifferentialModulePreStageMap C ψ i) at hproj
  exact hproj

/--
The separated completed module carries the quotient topology induced from the finite-stage
topology on the completed pre-module.
-/
@[implicit_reducible]
def zcSeparatedCompletedDifferentialModuleNaturalTopology :
    TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
  TopologicalSpace.coinduced
    (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ
    (zcCompletedDifferentialPreModuleNaturalTopology C ψ)

omit [IsTopologicalGroup G] in
/--
The quotient map to the separated completed module is continuous for the finite-stage pre-module
topology and the separated quotient topology.
-/
theorem continuous_zcSeparatedCompletedDifferentialModule_mkQ_naturalTopology :
    @Continuous
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      (ZCSeparatedCompletedDifferentialModule C ψ)
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
      (zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ)
      (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ :=
  continuous_coinduced_rng

omit [IsTopologicalGroup G] in
/--
The quotient map defining the separated completed module is a quotient map for the finite-stage
pre-module topology.
-/
theorem isQuotientMap_zcSeparatedCompletedDifferentialModule_mkQ_naturalTopology :
    letI : TopologicalSpace
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
      zcCompletedDifferentialPreModuleNaturalTopology C ψ
    letI : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
      zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ
    Topology.IsQuotientMap (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
    zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ
  rw [Topology.isQuotientMap_iff]
  constructor
  · exact ⟨rfl⟩
  · exact
      Submodule.Quotient.mk_surjective
        (p := zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ)

omit [IsTopologicalGroup G] in
/--
Continuity out of the separated completed module can be tested after precomposing with the
defining quotient map.
-/
theorem continuous_zcSeparatedCompletedDifferentialModule_iff_comp_mkQ
    {C : ProCGroups.FiniteGroupClass.{u}} {ψ : G →* H}
    {A : Type u} [TopologicalSpace A]
    {f : ZCSeparatedCompletedDifferentialModule C ψ → A} :
    @Continuous
        (ZCSeparatedCompletedDifferentialModule C ψ) A
        (zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ) inferInstance f ↔
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) A
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ) inferInstance
        (fun x => f ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ x)) := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
    zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ
  simpa [Function.comp_def] using
    (isQuotientMap_zcSeparatedCompletedDifferentialModule_mkQ_naturalTopology
      C ψ).continuous_iff (g := f)

omit [IsTopologicalGroup G] in
/--
Each finite-stage projection from the separated completed quotient is continuous for the
separated quotient topology.
-/
theorem continuous_zcSepDiffModuleStageProjAdd_naturalTopology
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    @Continuous
      (ZCSeparatedCompletedDifferentialModule C ψ)
      (ZCCompletedDifferentialModuleStage C ψ i)
      (zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ)
      inferInstance
      (zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i) := by
  let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
    zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  rw [continuous_coinduced_dom]
  change
    @Continuous
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      (ZCCompletedDifferentialModuleStage C ψ i)
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
      inferInstance
      (fun x =>
        zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i
          ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ x))
  let : TopologicalSpace
      (CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ i)
        (zcCompletedDifferentialModuleStageSource C ψ i)) :=
    ⊥
  let : DiscreteTopology
      (CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ i)
        (zcCompletedDifferentialModuleStageSource C ψ i)) :=
    ⟨rfl⟩
  have hpre :
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (CrossedDifferentialPreModule
          (zcCompletedDifferentialModuleStageRing C ψ i)
          (zcCompletedDifferentialModuleStageSource C ψ i))
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
        inferInstance
        (zcCompletedDifferentialModulePreStageMap C ψ i) :=
    continuous_zcCompletedDifferentialModulePreStageMap_naturalTopology C ψ i
  let : TopologicalSpace (ZCCompletedDifferentialModuleStage C ψ i) := inferInstance
  let : DiscreteTopology (ZCCompletedDifferentialModuleStage C ψ i) := inferInstance
  have hq :
      Continuous
        (fun y :
            CrossedDifferentialPreModule
              (zcCompletedDifferentialModuleStageRing C ψ i)
              (zcCompletedDifferentialModuleStageSource C ψ i) =>
          (crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ y) :=
    continuous_of_discreteTopology
  have hcoord :
      (fun x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
        zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i
          ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ x)) =
      (fun x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
        (crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
            (zcCompletedDifferentialModulePreStageMap C ψ i x)) := by
    funext x
    rw [zcSeparatedCompletedDifferentialModuleStageProjectionAdd_mkQ,
      ← zcCompletedDifferentialModulePreStageMap_mkQ]
  rw [hcoord]
  exact hq.comp hpre

omit [IsTopologicalGroup G] in
/--
The separated finite-stage projection product is continuous for the separated quotient topology.
-/
theorem continuous_zcSepDiffModuleStageProjProduct_naturalTopology :
    @Continuous
      (ZCSeparatedCompletedDifferentialModule C ψ)
      (∀ i : ZCCompletedDifferentialModuleIndex C ψ,
        ZCCompletedDifferentialModuleStage C ψ i)
      (zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ)
      inferInstance
      (zcSeparatedCompletedDifferentialModuleStageProjectionProduct C ψ) := by
  let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
    zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ
  exact
    continuous_pi fun i =>
      by
        simpa [zcSeparatedCompletedDifferentialModuleStageProjectionProduct] using
          continuous_zcSepDiffModuleStageProjAdd_naturalTopology C ψ i

omit [IsTopologicalGroup G] in
/--
The separated completed quotient is Hausdorff for the separated finite-stage quotient topology.
-/
theorem t2Space_zcSeparatedCompletedDifferentialModuleNaturalTopology :
    @T2Space
      (ZCSeparatedCompletedDifferentialModule C ψ)
      (zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ) := by
  let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
    zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ
  exact T2Space.of_injective_continuous
    (zcSeparatedCompletedDifferentialModuleStageProjectionProduct_injective C ψ)
    (continuous_zcSepDiffModuleStageProjProduct_naturalTopology C ψ)

omit [IsTopologicalGroup G] in
/--
In the directed finite-stage situation, the separated quotient topology is exactly the topology
induced by all finite-stage separated projections.
-/
theorem zcSepDiffModuleNaturalTopology_eq_induced_stageProjProduct
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ)) :
    zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ =
      TopologicalSpace.induced
        (zcSeparatedCompletedDifferentialModuleStageProjectionProduct C ψ) inferInstance := by
  ext U
  constructor
  · intro hU
    let Tind : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
      TopologicalSpace.induced
        (zcSeparatedCompletedDifferentialModuleStageProjectionProduct C ψ) inferInstance
    rw [@isOpen_iff_forall_mem_open
      (ZCSeparatedCompletedDifferentialModule C ψ) Tind U]
    intro x hxU
    refine Submodule.Quotient.induction_on
      (p := zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ)
      (C := fun x =>
        x ∈ U → ∃ t, t ⊆ U ∧ @IsOpen
          (ZCSeparatedCompletedDifferentialModule C ψ) Tind t ∧ x ∈ t)
      x ?_ hxU
    intro a haU
    let q :
        CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G →
          ZCSeparatedCompletedDifferentialModule C ψ :=
      (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ
    have hpreOpen :
        @IsOpen
          (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
          (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
          (q ⁻¹' U) := by
      change
        @IsOpen
          (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
          (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
          (q ⁻¹' U) at hU
      exact hU
    rcases isOpen_induced_iff.mp hpreOpen with ⟨V, hVopen, hVeq⟩
    have haV : zcCompletedDifferentialPreModuleStageFamilyMap C ψ a ∈ V := by
      have haU' : a ∈ q ⁻¹' U := haU
      rwa [← hVeq] at haU'
    let S := zcCompletedDifferentialPreModuleStageSystem C ψ
    rcases S.exists_projection_preimage_subset hdir hVopen haV with
      ⟨i, W, hWopen, haW, hWV⟩
    let t : Set (ZCSeparatedCompletedDifferentialModule C ψ) :=
      {z | zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i z =
        zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i (q a)}
    refine ⟨t, ?_, ?_, ?_⟩
    · intro z hz
      refine Submodule.Quotient.induction_on
        (p := zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ)
        (C := fun z => z ∈ t → z ∈ U) z ?_ hz
      intro b hb
      have hcoord :
          zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i (q b) =
            zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i (q a) := hb
      have hstageRel :
          zcCompletedDifferentialModulePreStageMap C ψ i (b - a) ∈
            crossedDifferentialRelationSubmodule
              (zcCompletedDifferentialModuleStageScalar C ψ i) := by
        apply (Submodule.Quotient.mk_eq_zero
          (p := crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψ i))
          (x := zcCompletedDifferentialModulePreStageMap C ψ i (b - a))).1
        have hq :
            (crossedDifferentialRelationSubmodule
              (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
                (zcCompletedDifferentialModulePreStageMap C ψ i (b - a)) = 0 := by
          have hbq :
              (crossedDifferentialRelationSubmodule
                (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
                  (zcCompletedDifferentialModulePreStageMap C ψ i b) =
                (crossedDifferentialRelationSubmodule
                  (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
                  (zcCompletedDifferentialModulePreStageMap C ψ i a) := by
            change
              zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i
                  ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ b) =
                zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i
                  ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ a)
              at hcoord
            rw [zcSeparatedCompletedDifferentialModuleStageProjectionAdd_mkQ,
              zcSeparatedCompletedDifferentialModuleStageProjectionAdd_mkQ] at hcoord
            rw [zcCompletedDifferentialModulePreStageMap_mkQ,
              zcCompletedDifferentialModulePreStageMap_mkQ]
            exact hcoord
          have hzero :
              (crossedDifferentialRelationSubmodule
                (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
                  (zcCompletedDifferentialModulePreStageMap C ψ i b) -
                (crossedDifferentialRelationSubmodule
                  (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
                  (zcCompletedDifferentialModulePreStageMap C ψ i a) = 0 :=
            sub_eq_zero.mpr hbq
          simpa [map_sub] using hzero
        exact hq
      rcases zcCompletedDifferentialModulePreStageMap_relationSubmodule_surjective
          C ψ i hstageRel with
        ⟨r, hr, hrstage⟩
      have hqa : q (b - r) = q b := by
        have hrclosed : r ∈ zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ :=
          crossedDifferentialRelationSubmodule_le_finiteClosedSubmodule C ψ hr
        apply (Submodule.Quotient.eq
          (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ)).2
        change (b - r) - b ∈ zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ
        have hdiff : (b - r) - b = -r := by
          abel
        rw [hdiff]
        exact (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).neg_mem hrclosed
      have hpre_eq :
          zcCompletedDifferentialModulePreStageMap C ψ i (b - r) =
            zcCompletedDifferentialModulePreStageMap C ψ i a := by
        have hcalc :
            zcCompletedDifferentialModulePreStageMap C ψ i (b - a) =
              zcCompletedDifferentialModulePreStageMap C ψ i r := hrstage.symm
        have hsub :
            zcCompletedDifferentialModulePreStageMap C ψ i b -
              zcCompletedDifferentialModulePreStageMap C ψ i a =
                zcCompletedDifferentialModulePreStageMap C ψ i r := by
          simpa [map_sub] using hcalc
        rw [map_sub]
        rw [← hsub]
        abel
      have hbW : S.projection i
          (zcCompletedDifferentialPreModuleStageFamilyMap C ψ (b - r)) ∈ W := by
        change zcCompletedDifferentialModulePreStageMap C ψ i (b - r) ∈ W
        rw [hpre_eq]
        change zcCompletedDifferentialModulePreStageMap C ψ i a ∈ W at haW
        exact haW
      have hbV : zcCompletedDifferentialPreModuleStageFamilyMap C ψ (b - r) ∈ V := hWV hbW
      have hbU : q (b - r) ∈ U := by
        have hbV' :
            (b - r) ∈ zcCompletedDifferentialPreModuleStageFamilyMap C ψ ⁻¹' V := hbV
        rwa [hVeq] at hbV'
      rwa [hqa] at hbU
    · let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) := Tind
      have hprod :
          Continuous (zcSeparatedCompletedDifferentialModuleStageProjectionProduct C ψ) :=
        continuous_induced_dom
      have hcoord :
          Continuous (fun z : ZCSeparatedCompletedDifferentialModule C ψ =>
            zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i z) := by
        have hi := (continuous_apply i).comp hprod
        change
          Continuous
            (zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i) at hi
        exact hi
      have : DiscreteTopology (ZCCompletedDifferentialModuleStage C ψ i) := inferInstance
      exact (isOpen_discrete
        ({zcSeparatedCompletedDifferentialModuleStageProjectionAdd C ψ i (q a)} :
          Set (ZCCompletedDifferentialModuleStage C ψ i))).preimage hcoord
    · exact rfl
  · intro hU
    let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
      zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ
    rcases isOpen_induced_iff.mp hU with ⟨V, hVopen, hVU⟩
    rw [← hVU]
    exact hVopen.preimage
      (continuous_zcSepDiffModuleStageProjProduct_naturalTopology C ψ)

/--
The pre-module generator map g \(\mapsto\) dg is continuous for the finite-stage pre-module
topology.
-/
theorem continuous_zcCompletedDifferentialPreModule_single_one_naturalTopology :
    @Continuous G
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      inferInstance
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
      (fun g : G => Finsupp.single g (1 : ZCCompletedGroupAlgebra C H)) := by
  rw [continuous_induced_rng]
  let S := zcCompletedDifferentialPreModuleStageSystem C ψ
  let preSingle :
      ∀ i : ZCCompletedDifferentialModuleIndex C ψ,
        G →
          CrossedDifferentialPreModule
            (zcCompletedDifferentialModuleStageRing C ψ i)
            (zcCompletedDifferentialModuleStageSource C ψ i) := fun i g =>
        zcCompletedDifferentialModulePreStageMap C ψ i
          (Finsupp.single g (1 : ZCCompletedGroupAlgebra C H))
  have hpreSingle_continuous :
      ∀ i : ZCCompletedDifferentialModuleIndex C ψ,
        @Continuous G
          (CrossedDifferentialPreModule
            (zcCompletedDifferentialModuleStageRing C ψ i)
            (zcCompletedDifferentialModuleStageSource C ψ i))
          inferInstance
          ((zcCompletedDifferentialPreModuleStageSystem C ψ).topologicalSpace i)
          (preSingle i) := by
    intro i
    have hsource :
        Continuous (zcCompletedDifferentialModuleStageSourceProj C ψ i) := by
      exact QuotientGroup.continuous_mk
    have hsingle :
        @Continuous
          (zcCompletedDifferentialModuleStageSource C ψ i)
          (CrossedDifferentialPreModule
            (zcCompletedDifferentialModuleStageRing C ψ i)
            (zcCompletedDifferentialModuleStageSource C ψ i))
          inferInstance
          ((zcCompletedDifferentialPreModuleStageSystem C ψ).topologicalSpace i)
          (fun q => Finsupp.single q
            (1 : zcCompletedDifferentialModuleStageRing C ψ i)) :=
      @continuous_of_discreteTopology
        (zcCompletedDifferentialModuleStageSource C ψ i)
        inferInstance inferInstance
        (CrossedDifferentialPreModule
          (zcCompletedDifferentialModuleStageRing C ψ i)
          (zcCompletedDifferentialModuleStageSource C ψ i))
        ((zcCompletedDifferentialPreModuleStageSystem C ψ).topologicalSpace i)
        (fun q => Finsupp.single q
          (1 : zcCompletedDifferentialModuleStageRing C ψ i))
    have hcomp :
        @Continuous G
          (CrossedDifferentialPreModule
            (zcCompletedDifferentialModuleStageRing C ψ i)
            (zcCompletedDifferentialModuleStageSource C ψ i))
          inferInstance
          ((zcCompletedDifferentialPreModuleStageSystem C ψ).topologicalSpace i)
          ((fun q => Finsupp.single q
              (1 : zcCompletedDifferentialModuleStageRing C ψ i)) ∘
            zcCompletedDifferentialModuleStageSourceProj C ψ i) :=
      @Continuous.comp
        G
        (zcCompletedDifferentialModuleStageSource C ψ i)
        (CrossedDifferentialPreModule
          (zcCompletedDifferentialModuleStageRing C ψ i)
          (zcCompletedDifferentialModuleStageSource C ψ i))
        inferInstance inferInstance
        ((zcCompletedDifferentialPreModuleStageSystem C ψ).topologicalSpace i)
        (f := zcCompletedDifferentialModuleStageSourceProj C ψ i)
        (g := fun q => Finsupp.single q
          (1 : zcCompletedDifferentialModuleStageRing C ψ i))
        hsingle hsource
    have hfun :
        ((fun q => Finsupp.single q
            (1 : zcCompletedDifferentialModuleStageRing C ψ i)) ∘
          zcCompletedDifferentialModuleStageSourceProj C ψ i) =
            preSingle i := by
      funext g
      simp only [Function.comp_apply, preSingle,
        zcCompletedDifferentialModulePreStageMap_single,
        zcCompletedGroupAlgebraProjection_one]
    exact hfun ▸ hcomp
  have hpreSingle_compat : S.CompatibleMaps preSingle := by
    intro i j hij
    funext g
    exact
      congrFun
        (zcCompletedDifferentialPreModuleStageSystem_compatible_preStageMap C ψ i j hij)
        (Finsupp.single g (1 : ZCCompletedGroupAlgebra C H))
  have hLift : Continuous (S.inverseLimitLift preSingle hpreSingle_compat) :=
    S.continuous_inverseLimitLift preSingle hpreSingle_continuous hpreSingle_compat
  have hEq :
      zcCompletedDifferentialPreModuleStageFamilyMap C ψ ∘
          (fun g : G => Finsupp.single g (1 : ZCCompletedGroupAlgebra C H)) =
        S.inverseLimitLift preSingle hpreSingle_compat := by
    apply S.inverseLimitLift_unique preSingle hpreSingle_compat
    intro i
    funext g
    rfl
  rw [hEq]
  exact hLift

/--
The separated universal differential is continuous for the separated finite-stage quotient
topology.
-/
theorem continuous_zcSeparatedUniversalDifferential_naturalTopology :
    @Continuous G
      (ZCSeparatedCompletedDifferentialModule C ψ)
      inferInstance
      (zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ)
      (zcSeparatedUniversalDifferential C ψ) := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  exact
    (continuous_zcSeparatedCompletedDifferentialModule_mkQ_naturalTopology C ψ).comp
      (continuous_zcCompletedDifferentialPreModule_single_one_naturalTopology C ψ)

omit [IsTopologicalGroup G] in
/--
A pre-quotient linear lift is continuous for the finite-stage pre-module topology when it
factors through one finite pre-stage reduction. This is the standard way to discharge the
hprelift input in applications where the target data is already finite-stage.
-/
theorem continuous_crossedDifferentialModuleLiftLinear_of_preStageMap_factor
    {A : Type u} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
    [TopologicalSpace A]
    (delta : G → A)
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (L :
      CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ i)
        (zcCompletedDifferentialModuleStageSource C ψ i) → A)
    (hfactor :
      ∀ x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G,
        crossedDifferentialModuleLiftLinear
            (R := ZCCompletedGroupAlgebra C H) delta x =
          L (zcCompletedDifferentialModulePreStageMap C ψ i x)) :
    @Continuous
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      A
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
      inferInstance
      (crossedDifferentialModuleLiftLinear
        (R := ZCCompletedGroupAlgebra C H) delta) := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  let : TopologicalSpace
      (CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ i)
        (zcCompletedDifferentialModuleStageSource C ψ i)) :=
    ⊥
  let : DiscreteTopology
      (CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ i)
        (zcCompletedDifferentialModuleStageSource C ψ i)) :=
    ⟨rfl⟩
  have hpre :
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (CrossedDifferentialPreModule
          (zcCompletedDifferentialModuleStageRing C ψ i)
          (zcCompletedDifferentialModuleStageSource C ψ i))
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
        inferInstance
        (zcCompletedDifferentialModulePreStageMap C ψ i) :=
    continuous_zcCompletedDifferentialModulePreStageMap_naturalTopology C ψ i
  have hL : Continuous L := continuous_of_discreteTopology
  have hfun :
      (fun x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
        crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H) delta x) =
      fun x => L (zcCompletedDifferentialModulePreStageMap C ψ i x) := by
    funext x
    exact hfactor x
  change
    @Continuous
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      A
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
      inferInstance
      (fun x =>
        crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H) delta x)
  rw [hfun]
  exact hL.comp hpre

omit [IsTopologicalGroup G] in
/--
The canonical lift to a finite differential-module stage is continuous for the finite-stage
pre-module topology.
-/
theorem continuous_crossedDifferentialModuleLiftLinear_stageDifferential
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    @Continuous
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      (ZCCompletedDifferentialModuleStage C ψ i)
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
      inferInstance
      (crossedDifferentialModuleLiftLinear
        (R := ZCCompletedGroupAlgebra C H)
        (zcCompletedDifferentialModuleStageDifferential C ψ i)) := by
  exact
    continuous_crossedDifferentialModuleLiftLinear_of_preStageMap_factor
      C ψ
      (zcCompletedDifferentialModuleStageDifferential C ψ i)
      i
      (fun y =>
        (crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ y)
      (by
        intro x
        exact (zcCompletedDifferentialModulePreStageMap_mkQ C ψ i x).symm)

/--
The raw algebraic crossed-differential relation submodule is closed for the finite-stage
topology on the completed pre-module. This closedness condition makes the algebraic quotient
separated; the separated quotient construction records this condition structurally.
-/
def zcCompletedDifferentialModuleRelationSubmoduleClosed : Prop :=
  @IsClosed
    (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
    (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
    ((crossedDifferentialRelationSubmodule
      (zcCompletedGroupAlgebraScalar C ψ) :
        Submodule (ZCCompletedGroupAlgebra C H)
          (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) : Set
            (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G))

omit [IsTopologicalGroup G] in
/--
A useful non-circular closedness criterion. If a Hausdorff/\(T_1\) target receives an injective
linear map from the algebraic completed differential module, and the composite from the
completed pre-module is continuous for the finite-stage pre-module topology, then the defining
crossed-differential relation submodule is closed. In applications the target is usually a
finite coordinate module \(\mathbb{Z}_C\llbracket H\rrbracket^{X}\). The formulation isolates
the real topological input: continuity of the pre-quotient coordinate map.
-/
theorem zcDiffModuleRelSubmoduleClosed_of_inj_continuous_comp_mkQ
    {M : Type u} [AddCommGroup M] [Module (ZCCompletedGroupAlgebra C H) M]
    [TopologicalSpace M] [T1Space M]
    (L :
      ZCCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H] M)
    (hLinj : Function.Injective L)
    (hcont :
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        M
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
        inferInstance
        (fun x =>
          L
            ((crossedDifferentialRelationSubmodule
              (zcCompletedGroupAlgebraScalar C ψ)).mkQ x))) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed C ψ := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  change IsClosed
    ((crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) :
      Submodule (ZCCompletedGroupAlgebra C H)
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
      Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G))
  have hpreimage :
      ((crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) :
        Submodule (ZCCompletedGroupAlgebra C H)
          (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
        Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) =
      (fun x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
        L
          ((crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C ψ)).mkQ x)) ⁻¹' ({0} : Set M) := by
    ext x
    constructor
    · intro hx
      have hq :
          ((crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C ψ)).mkQ x :
              ZCCompletedDifferentialModule C ψ) = 0 :=
        (Submodule.Quotient.mk_eq_zero
          (p := crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C ψ))
          (x := x)).2 hx
      change
        L
          ((crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C ψ)).mkQ x) = 0
      rw [hq]
      exact map_zero L
    · intro hx
      have hq :
          ((crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C ψ)).mkQ x :
              ZCCompletedDifferentialModule C ψ) = 0 := by
        apply hLinj
        simpa using hx
      exact
        (Submodule.Quotient.mk_eq_zero
          (p := crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C ψ))
          (x := x)).1 hq
  rw [hpreimage]
  exact isClosed_singleton.preimage hcont

omit [IsTopologicalGroup G] in
/--
The quotient map from the completed pre-module to the algebraic quotient is continuous for the
finite-stage topologies.
-/
theorem continuous_zcCompletedDifferentialModule_mkQ_naturalTopology :
    @Continuous
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      (ZCCompletedDifferentialModule C ψ)
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
      (zcCompletedDifferentialModuleNaturalTopology C ψ)
      (crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ)).mkQ := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  let : TopologicalSpace (ZCCompletedDifferentialModule C ψ) :=
    zcCompletedDifferentialModuleNaturalTopology C ψ
  rw [continuous_induced_rng]
  change Continuous
    (fun x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
      fun i : ZCCompletedDifferentialModuleIndex C ψ =>
        zcCompletedDifferentialModuleStageProjectionAdd C ψ i
          ((crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C ψ)).mkQ x))
  refine continuous_pi fun i => ?_
  let S := zcCompletedDifferentialPreModuleStageSystem C ψ
  let : TopologicalSpace
      (CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ i)
        (zcCompletedDifferentialModuleStageSource C ψ i)) :=
    ⊥
  let : DiscreteTopology
      (CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ i)
        (zcCompletedDifferentialModuleStageSource C ψ i)) :=
    ⟨rfl⟩
  have hpre :
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (CrossedDifferentialPreModule
          (zcCompletedDifferentialModuleStageRing C ψ i)
          (zcCompletedDifferentialModuleStageSource C ψ i))
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ) inferInstance
        (zcCompletedDifferentialModulePreStageMap C ψ i) := by
    have hfamily :
        @Continuous
          (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
          (ZCCompletedDifferentialPreModuleStageFamily C ψ)
          (zcCompletedDifferentialPreModuleNaturalTopology C ψ) inferInstance
          (zcCompletedDifferentialPreModuleStageFamilyMap C ψ) :=
      continuous_induced_dom
    have hproj := (S.continuous_projection i).comp hfamily
    change
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (CrossedDifferentialPreModule
          (zcCompletedDifferentialModuleStageRing C ψ i)
          (zcCompletedDifferentialModuleStageSource C ψ i))
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ) inferInstance
        (zcCompletedDifferentialModulePreStageMap C ψ i) at hproj
    exact hproj
  let : TopologicalSpace (ZCCompletedDifferentialModuleStage C ψ i) := inferInstance
  let : DiscreteTopology (ZCCompletedDifferentialModuleStage C ψ i) := inferInstance
  have hq :
      Continuous
        (fun y :
            CrossedDifferentialPreModule
              (zcCompletedDifferentialModuleStageRing C ψ i)
              (zcCompletedDifferentialModuleStageSource C ψ i) =>
          (crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ y) :=
    continuous_of_discreteTopology
  have hcomp := hq.comp hpre
  have hcoord :
      (fun x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
        zcCompletedDifferentialModuleStageProjectionAdd C ψ i
          ((crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C ψ)).mkQ x)) =
        (fun x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
          (crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
              (zcCompletedDifferentialModulePreStageMap C ψ i x)) := by
    funext x
    rw [zcCompletedDifferentialModuleStageProjectionAdd_apply,
      zcCompletedDifferentialModuleStageProjection_mkQ,
      ← zcCompletedDifferentialModulePreStageMap_mkQ]
  rw [hcoord]
  exact hcomp

omit [IsTopologicalGroup G] in
/--
If the finite-stage natural topology on the algebraic quotient is already \(T_1\), then the
defining crossed-differential relation submodule is closed in the completed pre-module
finite-stage topology. This is the quotient-topology reflection statement: the relation
submodule is the preimage of \({0}\) under the continuous algebraic quotient map.
-/
theorem zcCompletedDifferentialModuleRelationSubmoduleClosed_of_t1_naturalTopology
    (hT1 :
      @T1Space (ZCCompletedDifferentialModule C ψ)
        (zcCompletedDifferentialModuleNaturalTopology C ψ)) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed C ψ := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  let : TopologicalSpace (ZCCompletedDifferentialModule C ψ) :=
    zcCompletedDifferentialModuleNaturalTopology C ψ
  let : T1Space (ZCCompletedDifferentialModule C ψ) := hT1
  change IsClosed
    ((crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) :
      Submodule (ZCCompletedGroupAlgebra C H)
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
      Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G))
  have hpreimage :
      ((crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) :
        Submodule (ZCCompletedGroupAlgebra C H)
          (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
        Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) =
      (fun x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
        (crossedDifferentialRelationSubmodule
          (zcCompletedGroupAlgebraScalar C ψ)).mkQ x) ⁻¹'
        ({0} : Set (ZCCompletedDifferentialModule C ψ)) := by
    ext x
    simp only [SetLike.mem_coe, Submodule.mkQ_apply, Set.mem_preimage, Set.mem_singleton_iff,
  Submodule.Quotient.mk_eq_zero]
  rw [hpreimage]
  exact isClosed_singleton.preimage
    (continuous_zcCompletedDifferentialModule_mkQ_naturalTopology C ψ)

omit [IsTopologicalGroup G] in
/--
A quotient-level non-circular closedness criterion. If the algebraic completed differential
module admits an injective continuous map from its finite-stage natural topology to a \(T_1\)
target, then the defining crossed-differential relation submodule is closed in the pre-module
finite-stage topology. This packages the topological reflection step through the continuous
algebraic quotient map from the pre-module.
-/
theorem zcDiffModuleRelSubmoduleClosed_of_inj_continuous_naturalTopology
    {M : Type u} [AddCommGroup M] [Module (ZCCompletedGroupAlgebra C H) M]
    [TopologicalSpace M] [T1Space M]
    (L :
      ZCCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H] M)
    (hLinj : Function.Injective L)
    (hcont :
      @Continuous
        (ZCCompletedDifferentialModule C ψ) M
        (zcCompletedDifferentialModuleNaturalTopology C ψ) inferInstance
        L) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed C ψ :=
  zcDiffModuleRelSubmoduleClosed_of_inj_continuous_comp_mkQ
    C ψ L hLinj
    (@Continuous.comp
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      (ZCCompletedDifferentialModule C ψ) M
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
      (zcCompletedDifferentialModuleNaturalTopology C ψ) inferInstance
      (f := (crossedDifferentialRelationSubmodule
        (zcCompletedGroupAlgebraScalar C ψ)).mkQ)
      (g := L) hcont
      (continuous_zcCompletedDifferentialModule_mkQ_naturalTopology C ψ))

omit [IsTopologicalGroup G] in
/--
Finite relation-valued reductions put a pre-module element in the finite-stage closure of the
completed crossed-differential relation submodule.
-/
theorem zcDiffModuleFiniteRelationReductions_mem_closure_relSubmodule
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ))
    (x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
    (hx : ∀ i : ZCCompletedDifferentialModuleIndex C ψ,
      zcCompletedDifferentialModulePreStageMap C ψ i x ∈
        crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i)) :
    x ∈ @closure
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
      ((crossedDifferentialRelationSubmodule
        (zcCompletedGroupAlgebraScalar C ψ) :
          Submodule (ZCCompletedGroupAlgebra C H)
            (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) : Set
              (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  rw [mem_closure_iff]
  intro U hU hxU
  rcases isOpen_induced_iff.mp hU with ⟨V, hVopen, hVeq⟩
  have hxV : zcCompletedDifferentialPreModuleStageFamilyMap C ψ x ∈ V := by
    rw [← hVeq] at hxU
    exact hxU
  let S := zcCompletedDifferentialPreModuleStageSystem C ψ
  rcases S.exists_projection_preimage_subset hdir hVopen hxV with
    ⟨i, W, hWopen, hxW, hWU⟩
  rcases zcCompletedDifferentialModuleFiniteRelationReductions_finiteStageApproximation
      C ψ hdir ({i} : Finset (ZCCompletedDifferentialModuleIndex C ψ)) x hx with
    ⟨r, hr, hrstage⟩
  refine ⟨r, ?_, hr⟩
  have hri : zcCompletedDifferentialModulePreStageMap C ψ i r =
      zcCompletedDifferentialModulePreStageMap C ψ i x := by
    exact hrstage i (by simp only [Finset.mem_singleton])
  have hrW :
      S.projection i (zcCompletedDifferentialPreModuleStageFamilyMap C ψ r) ∈ W := by
    change zcCompletedDifferentialModulePreStageMap C ψ i r ∈ W
    rw [hri]
    change zcCompletedDifferentialModulePreStageMap C ψ i x ∈ W at hxW
    exact hxW
  have hrV : zcCompletedDifferentialPreModuleStageFamilyMap C ψ r ∈ V := hWU hrW
  rw [← hVeq]
  exact hrV

omit [IsTopologicalGroup G] in
/--
Each finite-stage pre-kernel is closed for the finite-stage topology on the completed
pre-module.
-/
theorem isClosed_zcCompletedDifferentialModulePreStageKernel_naturalTopology
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    @IsClosed
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
      ((zcCompletedDifferentialModulePreStageKernel C ψ i :
        Submodule (ZCCompletedGroupAlgebra C H)
          (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
        Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  let S := zcCompletedDifferentialPreModuleStageSystem C ψ
  let : TopologicalSpace
      (CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ i)
        (zcCompletedDifferentialModuleStageSource C ψ i)) :=
    ⊥
  let : DiscreteTopology
      (CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ i)
        (zcCompletedDifferentialModuleStageSource C ψ i)) :=
    ⟨rfl⟩
  have hpre :
      Continuous (zcCompletedDifferentialModulePreStageMap C ψ i) := by
    have hfamily :
        @Continuous
          (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
          (ZCCompletedDifferentialPreModuleStageFamily C ψ)
          (zcCompletedDifferentialPreModuleNaturalTopology C ψ) inferInstance
          (zcCompletedDifferentialPreModuleStageFamilyMap C ψ) :=
      continuous_induced_dom
    have hproj := (S.continuous_projection i).comp hfamily
    change
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (CrossedDifferentialPreModule
          (zcCompletedDifferentialModuleStageRing C ψ i)
          (zcCompletedDifferentialModuleStageSource C ψ i))
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ) inferInstance
        (zcCompletedDifferentialModulePreStageMap C ψ i) at hproj
    exact hproj
  have hpreimage :
      IsClosed
        ((zcCompletedDifferentialModulePreStageMap C ψ i) ⁻¹'
          (((crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψ i)) :
              Submodule
                (zcCompletedDifferentialModuleStageRing C ψ i)
                (CrossedDifferentialPreModule
                  (zcCompletedDifferentialModuleStageRing C ψ i)
                  (zcCompletedDifferentialModuleStageSource C ψ i))) :
            Set (CrossedDifferentialPreModule
              (zcCompletedDifferentialModuleStageRing C ψ i)
              (zcCompletedDifferentialModuleStageSource C ψ i)))) := by
    exact
      (isClosed_discrete
        (((crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i)) :
            Submodule
              (zcCompletedDifferentialModuleStageRing C ψ i)
              (CrossedDifferentialPreModule
                (zcCompletedDifferentialModuleStageRing C ψ i)
                (zcCompletedDifferentialModuleStageSource C ψ i))) :
          Set (CrossedDifferentialPreModule
            (zcCompletedDifferentialModuleStageRing C ψ i)
            (zcCompletedDifferentialModuleStageSource C ψ i)))).preimage hpre
  have hset :
      ((zcCompletedDifferentialModulePreStageKernel C ψ i :
        Submodule (ZCCompletedGroupAlgebra C H)
          (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
        Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) =
      ((zcCompletedDifferentialModulePreStageMap C ψ i) ⁻¹'
        (((crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i)) :
            Submodule
              (zcCompletedDifferentialModuleStageRing C ψ i)
              (CrossedDifferentialPreModule
                (zcCompletedDifferentialModuleStageRing C ψ i)
                (zcCompletedDifferentialModuleStageSource C ψ i))) :
          Set (CrossedDifferentialPreModule
            (zcCompletedDifferentialModuleStageRing C ψ i)
            (zcCompletedDifferentialModuleStageSource C ψ i)))) := by
    ext x
    exact
      mem_zcDiffModulePreStageKernel_iff_preStageMap_mem_relSubmodule (C := C) (ψ := ψ) (i := i)
          (x := x)
  simpa [hset] using hpreimage

omit [IsTopologicalGroup G] in
/--
The finite-stage closed relation denominator is closed for the finite-stage pre-module topology.
-/
theorem isClosed_zcCompletedDifferentialRelationFiniteClosedSubmodule_naturalTopology :
    @IsClosed
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
      ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ :
        Submodule (ZCCompletedGroupAlgebra C H)
          (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
        Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  change IsClosed
    ((zcCompletedDifferentialModulePreStageKernelIntersection C ψ :
      Submodule (ZCCompletedGroupAlgebra C H)
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
      Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G))
  rw [zcCompletedDifferentialModulePreStageKernelIntersection]
  simpa [Submodule.coe_iInf] using
    (isClosed_iInter
      (fun i =>
        isClosed_zcCompletedDifferentialModulePreStageKernel_naturalTopology
          C ψ i))

omit [IsTopologicalGroup G] in
/--
The zero class is closed in the separated completed differential module for the finite-stage
quotient topology.
-/
theorem isClosed_zero_zcSeparatedCompletedDifferentialModuleNaturalTopology :
    @IsClosed (ZCSeparatedCompletedDifferentialModule C ψ)
      (zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ)
      ({0} : Set (ZCSeparatedCompletedDifferentialModule C ψ)) := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  rw [zcSeparatedCompletedDifferentialModuleNaturalTopology, isClosed_coinduced]
  have hpreimage :
      ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ ⁻¹'
        ({0} : Set (ZCSeparatedCompletedDifferentialModule C ψ))) =
      ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ :
        Submodule (ZCCompletedGroupAlgebra C H)
          (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
        Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) := by
    ext x
    simp only [Set.mem_preimage, Submodule.mkQ_apply, Set.mem_singleton_iff,
        Submodule.Quotient.mk_eq_zero,
  SetLike.mem_coe]
  rw [hpreimage]
  exact isClosed_zcCompletedDifferentialRelationFiniteClosedSubmodule_naturalTopology C ψ

omit [IsTopologicalGroup G] in
/--
The finite-stage closed relation denominator is exactly the closure of the algebraic
crossed-differential relation submodule for the finite-stage pre-module topology.
-/
theorem closure_crossedDifferentialRelationSubmodule_eq_finiteClosedSubmodule
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ)) :
    @closure
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
      ((crossedDifferentialRelationSubmodule
        (zcCompletedGroupAlgebraScalar C ψ) :
          Submodule (ZCCompletedGroupAlgebra C H)
            (CrossedDifferentialPreModule
              (ZCCompletedGroupAlgebra C H) G)) :
        Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) =
    (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ :
      Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  apply Set.Subset.antisymm
  · intro x hxcl
    change x ∈ zcCompletedDifferentialModulePreStageKernelIntersection C ψ
    exact
      (mem_zcCompletedDifferentialModulePreStageKernelIntersection_iff (C := C) (ψ := ψ) (x := x)).2
        (by
          intro i
          have hclosed_i :=
            isClosed_zcCompletedDifferentialModulePreStageKernel_naturalTopology C ψ i
          have hsubset_i :
              ((crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) :
                Submodule (ZCCompletedGroupAlgebra C H)
                  (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
                Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) ⊆
              ((zcCompletedDifferentialModulePreStageKernel C ψ i :
                Submodule (ZCCompletedGroupAlgebra C H)
                  (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
                Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) := by
            intro y hy
            exact
              crossedDiffRelSubmodule_le_zcDiffModulePreStageKernel
                (C := C) (ψ := ψ) i hy
          have hxker : x ∈ zcCompletedDifferentialModulePreStageKernel C ψ i :=
            closure_minimal hsubset_i hclosed_i hxcl
          exact
            (mem_zcDiffModulePreStageKernel_iff_preStageMap_mem_relSubmodule (C := C) (ψ := ψ)
                (i := i) (x := x)).1 hxker)
  · intro x hxhat
    have hxstage :
        ∀ i : ZCCompletedDifferentialModuleIndex C ψ,
          zcCompletedDifferentialModulePreStageMap C ψ i x ∈
            crossedDifferentialRelationSubmodule
              (zcCompletedDifferentialModuleStageScalar C ψ i) :=
      (mem_zcCompletedDifferentialModulePreStageKernelIntersection_iff (C := C) (ψ := ψ) (x := x)).1
        (by
          simpa [zcCompletedDifferentialRelationFiniteClosedSubmodule] using hxhat)
    exact
      zcDiffModuleFiniteRelationReductions_mem_closure_relSubmodule
        C ψ hdir x hxstage

omit [IsTopologicalGroup G] in
/--
A continuous pre-quotient lift to a \(T_1\) target kills the finite-stage closed relation
denominator. This is the general descent criterion for maps out of the separated completed
universal module.
-/
theorem crossedDifferentialModuleLiftLinear_kills_finiteClosedSubmodule_of_continuous
    {A : Type u} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
    [TopologicalSpace A] [T1Space A]
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ))
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ) A)
    (hcont :
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        A
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H) delta))
    {x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G}
    (hx : x ∈ zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ) :
    crossedDifferentialModuleLiftLinear
      (R := ZCCompletedGroupAlgebra C H) delta x = 0 := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  have hxcl :
      x ∈ closure
        ((crossedDifferentialRelationSubmodule
          (zcCompletedGroupAlgebraScalar C ψ) :
            Submodule (ZCCompletedGroupAlgebra C H)
              (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
          Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) := by
    have hEq :=
      closure_crossedDifferentialRelationSubmodule_eq_finiteClosedSubmodule
        C ψ hdir
    rw [hEq]
    exact hx
  have hker_closed :
      IsClosed
        ((fun y : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
          crossedDifferentialModuleLiftLinear
            (R := ZCCompletedGroupAlgebra C H) delta y) ⁻¹'
          ({0} : Set A)) :=
    isClosed_singleton.preimage hcont
  have hrel_subset_ker :
      ((crossedDifferentialRelationSubmodule
        (zcCompletedGroupAlgebraScalar C ψ) :
          Submodule (ZCCompletedGroupAlgebra C H)
            (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
        Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) ⊆
      ((fun y : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
        crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H) delta y) ⁻¹'
        ({0} : Set A)) := by
    intro y hy
    exact
      (crossedHomRelationSubmodule_le_ker
        (A := A) (zcCompletedGroupAlgebraScalar C ψ)
        delta) hy
  exact closure_minimal hrel_subset_ker hker_closed hxcl

/--
The separated universal lift induced by a crossed differential whose pre-quotient lift is
continuous for the finite-stage topology.
-/
def zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift
    {A : Type u} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
    [TopologicalSpace A] [T1Space A]
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ))
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ) A)
    (hcont :
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        A
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H) delta)) :
    ZCSeparatedCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H] A :=
  (zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).liftQ
    (crossedDifferentialModuleLiftLinear
      (R := ZCCompletedGroupAlgebra C H) delta)
    (by
      intro x hx
      rw [LinearMap.mem_ker]
      exact
        crossedDifferentialModuleLiftLinear_kills_finiteClosedSubmodule_of_continuous
          C ψ hdir delta hcont hx)

omit [IsTopologicalGroup G] in
/--
The separated lift of a continuous crossed-differential prelift sends the separated universal
differential of \(g\) to \(\delta(g)\).
-/
@[simp 900]
theorem zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift_universal
    {A : Type u} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
    [TopologicalSpace A] [T1Space A]
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ))
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ) A)
    (hcont :
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        A
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H) delta))
    (g : G) :
    zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift
        C ψ hdir delta hcont
        (zcSeparatedUniversalDifferential C ψ g) =
      delta g := by
  change
    zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift
        C ψ hdir delta hcont
        ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ
          (Finsupp.single g 1)) =
      delta g
  rw [zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift,
    Submodule.mkQ_apply, Submodule.liftQ_apply]
  simp only [crossedDifferentialModuleLiftLinear_single, one_smul]

omit [IsTopologicalGroup G] in
/--
Linear maps out of the separated completed differential module are equal when they agree on all
separated universal differentials.
-/
@[ext]
theorem zcSeparatedCompletedDifferentialModuleHom_ext
    {A : Type u} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
    {f h : ZCSeparatedCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H] A}
    (hfh : ∀ g, f (zcSeparatedUniversalDifferential C ψ g) =
      h (zcSeparatedUniversalDifferential C ψ g)) :
    f = h := by
  apply Submodule.linearMap_qext _
  apply Finsupp.lhom_ext
  intro g r
  have hsingle :
      ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ
          (Finsupp.single g r) :
        ZCSeparatedCompletedDifferentialModule C ψ) =
        r • zcSeparatedUniversalDifferential C ψ g := by
    rw [← Finsupp.smul_single_one]
    rfl
  change f ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ
      (Finsupp.single g r)) =
    h ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ
      (Finsupp.single g r))
  simpa [hsingle, map_smul] using congrArg (fun z => r • z) (hfh g)

omit [IsTopologicalGroup G] in
/--
The separated lift of a continuous crossed differential is unique among linear maps with the
prescribed values on separated universal differentials.
-/
theorem zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift_unique
    {A : Type u} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
    [TopologicalSpace A] [T1Space A]
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ))
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ) A)
    (hcont :
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        A
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H) delta))
    (f : ZCSeparatedCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H] A)
    (hf : ∀ g, f (zcSeparatedUniversalDifferential C ψ g) = delta g) :
    f =
      zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift
        C ψ hdir delta hcont := by
  apply zcSeparatedCompletedDifferentialModuleHom_ext C ψ
  intro g
  rw [hf g, zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift_universal]

/--
The separated universal lift is bundled as a continuous linear map for the separated quotient
topology.
-/
def zcSeparatedCompletedDifferentialModuleLiftContinuousLinearMapOfContinuousPrelift
    {A : Type u} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
    [TopologicalSpace A] [T1Space A]
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ))
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ) A)
    (hcont :
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        A
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H) delta)) :
    letI : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
      zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ
    ZCSeparatedCompletedDifferentialModule C ψ →L[ZCCompletedGroupAlgebra C H] A := by
  letI : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
    zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ
  refine
    { toLinearMap :=
        zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift
          C ψ hdir delta hcont
      cont := ?_ }
  rw [continuous_coinduced_dom]
  change
    @Continuous
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      A
      (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
      inferInstance
      (fun x =>
        zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift
          C ψ hdir delta hcont
          ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ x))
  have hcomp :
      (fun x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
        zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift
          C ψ hdir delta hcont
          ((zcCompletedDifferentialRelationFiniteClosedSubmodule C ψ).mkQ x)) =
      crossedDifferentialModuleLiftLinear
        (R := ZCCompletedGroupAlgebra C H) delta := by
    funext x
    rw [zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift,
      Submodule.mkQ_apply, Submodule.liftQ_apply]
  rw [hcomp]
  exact hcont

omit [IsTopologicalGroup G] in
/--
The separated completed differential-module lift is evaluated after projection to the relevant
finite-stage separated quotient.
-/
@[simp 900]
theorem zcSepDiffModuleLiftContinuousLinearMapOfContinuousPrelift_apply
    {A : Type u} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
    [TopologicalSpace A] [T1Space A]
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ))
    (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ) A)
    (hcont :
      @Continuous
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        A
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
        inferInstance
        (crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H) delta))
    (m : ZCSeparatedCompletedDifferentialModule C ψ) :
    zcSeparatedCompletedDifferentialModuleLiftContinuousLinearMapOfContinuousPrelift
        C ψ hdir delta hcont m =
      zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift
        C ψ hdir delta hcont m :=
  rfl

/--
This is the continuous representation theorem for the separated completed module, parameterized
by the topological input that turns a continuous crossed differential into a continuous
pre-quotient linear lift.
-/
def zcSeparatedCompletedContinuousCrossedDifferentialEquivContinuousLinearMap
    {A : Type u} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
    [TopologicalSpace A] [T1Space A]
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ))
    (hprelift :
      ∀ (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ) A),
        Continuous delta →
          @Continuous
            (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
            A
            (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
            inferInstance
            (crossedDifferentialModuleLiftLinear
              (R := ZCCompletedGroupAlgebra C H) delta)) :
    {delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ) A //
        Continuous delta} ≃
      (letI : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
        zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ
      ZCSeparatedCompletedDifferentialModule C ψ →L[ZCCompletedGroupAlgebra C H] A) where
  toFun delta :=
    zcSeparatedCompletedDifferentialModuleLiftContinuousLinearMapOfContinuousPrelift
      C ψ hdir delta.1 (hprelift delta.1 delta.2)
  invFun f := by
    letI : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
      zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ
    exact
      ⟨(zcSeparatedUniversalDifferential C ψ).mapLinear f.toLinearMap,
        f.cont.comp (continuous_zcSeparatedUniversalDifferential_naturalTopology C ψ)⟩
  left_inv delta := by
    apply Subtype.ext
    apply CrossedHom.ext
    intro g
    exact
      zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift_universal
        C ψ hdir delta.1 (hprelift delta.1 delta.2) g
  right_inv f := by
    let : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
      zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ
    let delta :=
      (zcSeparatedUniversalDifferential C ψ).mapLinear f.toLinearMap
    have hcontinuous_delta : Continuous delta :=
      f.cont.comp (continuous_zcSeparatedUniversalDifferential_naturalTopology C ψ)
    have hlin :
        f.toLinearMap =
          zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift
            C ψ hdir delta (hprelift delta hcontinuous_delta) := by
      apply zcSeparatedCompletedDifferentialModuleLiftOfContinuousPrelift_unique
        C ψ hdir
      intro g
      rfl
    apply ContinuousLinearMap.ext
    intro m
    exact congrFun (congrArg DFunLike.coe hlin.symm) m

/--
Continuous representation theorem with the finite-stage index nonemptiness and directedness
supplied from a continuous homomorphism and the finite quotient-class hypotheses. The only
remaining topological input is the pre-quotient lift continuity.
-/
def zcSepContCrossedDiffEquivCLM
    {A : Type u} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
    [TopologicalSpace A] [T1Space A]
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (ψc : ContinuousMonoidHom G H)
    (hprelift :
      ∀ (delta : ScalarCrossedHom
          (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom) A),
        Continuous delta →
          @Continuous
            (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
            A
            (zcCompletedDifferentialPreModuleNaturalTopology C ψc.toMonoidHom)
            inferInstance
            (crossedDifferentialModuleLiftLinear
              (R := ZCCompletedGroupAlgebra C H) delta)) :
    {delta : ScalarCrossedHom
        (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom) A //
        Continuous delta} ≃
      (letI : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψc.toMonoidHom) :=
        zcSeparatedCompletedDifferentialModuleNaturalTopology C ψc.toMonoidHom
      ZCSeparatedCompletedDifferentialModule C ψc.toMonoidHom →L[ZCCompletedGroupAlgebra C H] A)
          := by
  letI : Nonempty (ZCCompletedDifferentialModuleIndex C ψc.toMonoidHom) :=
    nonempty_zcCompletedDifferentialModuleIndex C hC ψc
  exact
    zcSeparatedCompletedContinuousCrossedDifferentialEquivContinuousLinearMap
      C ψc.toMonoidHom
      (directed_zcCompletedDifferentialModuleIndex C hForm hC ψc)
      hprelift

/--
This is the continuous representation theorem for the separated completed module when every
continuous crossed differential under consideration has a pre-quotient lift that factors through
a finite pre-stage. This packages the finite-stage factorization criterion into the universal
property, so the public theorem no longer takes the raw hprelift continuity hypothesis.
-/
def zcSepCompletedContCrossedDiffEquivContinuousLinearMapOfFiniteStageFactorization
    {A : Type u} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
    [TopologicalSpace A] [T1Space A]
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ))
    (hfactor :
      ∀ (delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ) A),
        Continuous delta →
          ∃ i : ZCCompletedDifferentialModuleIndex C ψ,
            ∃ L :
              CrossedDifferentialPreModule
                (zcCompletedDifferentialModuleStageRing C ψ i)
                (zcCompletedDifferentialModuleStageSource C ψ i) → A,
              ∀ x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G,
                crossedDifferentialModuleLiftLinear
                    (R := ZCCompletedGroupAlgebra C H) delta x =
                  L (zcCompletedDifferentialModulePreStageMap C ψ i x)) :
    {delta : ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ) A //
        Continuous delta} ≃
      (letI : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψ) :=
        zcSeparatedCompletedDifferentialModuleNaturalTopology C ψ
      ZCSeparatedCompletedDifferentialModule C ψ →L[ZCCompletedGroupAlgebra C H] A) := by
  refine
    zcSeparatedCompletedContinuousCrossedDifferentialEquivContinuousLinearMap
      C ψ hdir ?_
  intro delta hcont
  rcases hfactor delta hcont with ⟨i, L, hL⟩
  exact
    continuous_crossedDifferentialModuleLiftLinear_of_preStageMap_factor
      C ψ delta i L hL

/--
Continuous representation theorem with finite-stage index data supplied from a continuous
homomorphism and raw pre-lift continuity discharged by finite-stage factorization.
-/
def zcSepContCrossedDiffEquivCLMOfFiniteStage
    {A : Type u} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
    [TopologicalSpace A] [T1Space A]
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (ψc : ContinuousMonoidHom G H)
    (hfactor :
      ∀ (delta : ScalarCrossedHom
          (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom) A),
        Continuous delta →
          ∃ i : ZCCompletedDifferentialModuleIndex C ψc.toMonoidHom,
            ∃ L :
              CrossedDifferentialPreModule
                (zcCompletedDifferentialModuleStageRing C ψc.toMonoidHom i)
                (zcCompletedDifferentialModuleStageSource C ψc.toMonoidHom i) → A,
              ∀ x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G,
                crossedDifferentialModuleLiftLinear
                    (R := ZCCompletedGroupAlgebra C H) delta x =
                  L (zcCompletedDifferentialModulePreStageMap C ψc.toMonoidHom i x)) :
    {delta : ScalarCrossedHom
        (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom) A //
        Continuous delta} ≃
      (letI : TopologicalSpace (ZCSeparatedCompletedDifferentialModule C ψc.toMonoidHom) :=
        zcSeparatedCompletedDifferentialModuleNaturalTopology C ψc.toMonoidHom
      ZCSeparatedCompletedDifferentialModule C ψc.toMonoidHom →L[ZCCompletedGroupAlgebra C H] A)
          := by
  letI : Nonempty (ZCCompletedDifferentialModuleIndex C ψc.toMonoidHom) :=
    nonempty_zcCompletedDifferentialModuleIndex C hC ψc
  exact
    zcSepCompletedContCrossedDiffEquivContinuousLinearMapOfFiniteStageFactorization
      C ψc.toMonoidHom
      (directed_zcCompletedDifferentialModuleIndex C hForm hC ψc)
      hfactor

/--
The \(\mathbb{Z}_C\llbracket H\rrbracket\)-action on a finite discrete target factors through
one finite coefficient-and-H stage.
-/
theorem zcCompletedGroupAlgebra_smul_factor_through_finite_stage
    {A : Type u} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
    [TopologicalSpace A] [Finite A] [DiscreteTopology A]
    [ContinuousSMul (ZCCompletedGroupAlgebra C H) A]
    (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    ∃ j : ZCCompletedGroupAlgebraIndex C H,
      ∃ act : ZCCompletedGroupAlgebraStage C H j → A → A,
        ∀ (r : ZCCompletedGroupAlgebra C H) (a : A),
          act (zcCompletedGroupAlgebraProjection C H j r) a = r • a := by
  classical
  let : Fintype A := Fintype.ofFinite A
  let : ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C :=
    hForm.containsTrivialQuotients
  let : Nonempty (ProCIntegerIndex C) :=
    ⟨ProCIntegerIndex.terminal (C := C) inferInstance⟩
  let : Nonempty (CompletedGroupAlgebraIndexInClass H C) :=
    ⟨_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndexInClass (G := H) C⟩
  let : Nonempty (ZCCompletedGroupAlgebraIndex C H) := inferInstance
  let : Finite (A → A) := Finite.of_fintype (A → A)
  let S := zcCompletedGroupAlgebraSystem C H
  let : ∀ i : ZCCompletedGroupAlgebraIndex C H, TopologicalSpace (S.X i) :=
    S.topologicalSpace
  let : ∀ i : ZCCompletedGroupAlgebraIndex C H, CompactSpace (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    change @CompactSpace (ZCCompletedGroupAlgebraStage C H i) ⊥
    let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
    let : Finite (ZCCompletedGroupAlgebraStage C H i) :=
      finite_modNCompletedGroupAlgebraStageInClass
        (n := i.1.modulus) (G := H) C i.2
    exact Finite.compactSpace
  let : ∀ i : ZCCompletedGroupAlgebraIndex C H, T2Space (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    change @T2Space (ZCCompletedGroupAlgebraStage C H i) ⊥
    exact @DiscreteTopology.toT2Space _ ⊥ ⟨rfl⟩
  let : ∀ i : ZCCompletedGroupAlgebraIndex C H, TotallyDisconnectedSpace (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    change @TotallyDisconnectedSpace (ZCCompletedGroupAlgebraStage C H i) ⊥
    exact @TotallySeparatedSpace.totallyDisconnectedSpace _ ⊥
      (@TotallySeparatedSpace.of_discrete _ ⊥ ⟨rfl⟩)
  let ρ : ZCCompletedGroupAlgebra C H → A → A := fun r a => r • a
  have hρ : Continuous ρ := by
    change Continuous (fun r : ZCCompletedGroupAlgebra C H => fun a : A => r • a)
    exact continuous_pi fun a => continuous_id.smul continuous_const
  rcases S.factors_through_projection_finite
      (directed_zcCompletedGroupAlgebraIndex_of_formation C (H := H) hForm)
      ρ hρ with
    ⟨j, act, _hact_continuous, hact⟩
  refine ⟨j, act, ?_⟩
  intro r a
  have h := congrFun (congrFun hact r) a
  change ((act ∘ S.projection j) r) a = ρ r a
  exact h.symm

omit [IsTopologicalGroup G] in
/--
A finite discrete target crossed differential has a pre-quotient lift factoring through one
finite source/target/coefficient stage.
-/
theorem crossedDifferentialModuleLiftLinear_factors_finite_discrete
    {A : Type u} [AddCommGroup A] [Module (ZCCompletedGroupAlgebra C H) A]
    [TopologicalSpace A] [Finite A] [DiscreteTopology A]
    [ContinuousSMul (ZCCompletedGroupAlgebra C H) A]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (ψc : ContinuousMonoidHom G H)
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C G)
    (delta : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom) A)
    (hcont : Continuous delta) :
    ∃ i : ZCCompletedDifferentialModuleIndex C ψc.toMonoidHom,
      ∃ L :
        CrossedDifferentialPreModule
          (zcCompletedDifferentialModuleStageRing C ψc.toMonoidHom i)
          (zcCompletedDifferentialModuleStageSource C ψc.toMonoidHom i) → A,
        ∀ x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G,
          crossedDifferentialModuleLiftLinear
              (R := ZCCompletedGroupAlgebra C H) delta x =
            L (zcCompletedDifferentialModulePreStageMap C ψc.toMonoidHom i x) := by
  classical
  let : Fintype A := Fintype.ofFinite A
  rcases zcCompletedGroupAlgebra_smul_factor_through_finite_stage
      (C := C) (H := H) (A := A) hForm with
    ⟨target, act, hact⟩
  have hdelta_one : delta 1 = 0 :=
    delta.map_one
  let W : Set G := {g | delta g = 0}
  have hWopen : IsOpen W := by
    change IsOpen (delta ⁻¹' ({0} : Set A))
    exact (isOpen_discrete _).preimage hcont
  have h1W : (1 : G) ∈ W := by
    change delta 1 = 0
    exact hdelta_one
  rcases hG.exists_openNormalSubgroupInClass_sub_open_nhds_of_one hWopen h1W with
    ⟨V0, hV0W⟩
  let comapSource : OpenNormalSubgroupInClass C G :=
    OrderDual.ofDual
      (completedGroupAlgebraComapIndexInClass
        (G := G) (H := H) C hC ψc target.2)
  let source : OpenNormalSubgroupInClass C G :=
    ⟨V0.1 ⊓ comapSource.1,
      ProCGroups.FiniteGroupClass.Formation.quotient_inf_mem
        (C := C) (G := G) hForm V0.1 comapSource.1 V0.2 comapSource.2⟩
  let i : ZCCompletedDifferentialModuleIndex C ψc.toMonoidHom :=
    { source := source
      target := target
      compatible := by
        intro g hg
        have hgcomap : g ∈ (comapSource.1 : Subgroup G) := hg.2
        change ψc.toMonoidHom g ∈
          ((((OrderDual.ofDual target.2).1 : OpenNormalSubgroup H) : Subgroup H))
        simpa [comapSource, completedGroupAlgebraComapIndexInClass] using hgcomap }
  have hsource_delta_zero :
      ∀ g : G, g ∈ (source.1 : Subgroup G) → delta g = 0 := by
    intro g hg
    exact hV0W hg.1
  let deltaBar : zcCompletedDifferentialModuleStageSource C ψc.toMonoidHom i → A :=
    Quotient.lift delta (by
      intro a b hab
      have hab_source : a⁻¹ * b ∈ (source.1 : Subgroup G) :=
        (QuotientGroup.leftRel_apply).1 hab
      have hab_zero : delta (a⁻¹ * b) = 0 :=
        hsource_delta_zero (a⁻¹ * b) hab_source
      have hprod := delta.map_mul a (a⁻¹ * b)
      have hrewrite : a * (a⁻¹ * b) = b := by simp only [mul_inv_cancel_left]
      have hb : delta b =
          delta a + zcCompletedGroupAlgebraScalar C ψc.toMonoidHom a •
            delta (a⁻¹ * b) := by
        simpa [hrewrite] using hprod
      rw [hab_zero, smul_zero, add_zero] at hb
      exact hb.symm)
  let coeffMap :
      zcCompletedDifferentialModuleStageSource C ψc.toMonoidHom i →
        zcCompletedDifferentialModuleStageRing C ψc.toMonoidHom i →+ A :=
    fun q =>
      { toFun := fun a => act a (deltaBar q)
        map_zero' := by
          have h := hact (0 : ZCCompletedGroupAlgebra C H) (deltaBar q)
          simpa using h
        map_add' := by
          intro a b
          rcases zcCompletedGroupAlgebraProjection_surjective C H target a with ⟨ra, hra⟩
          rcases zcCompletedGroupAlgebraProjection_surjective C H target b with ⟨rb, hrb⟩
          calc
            act (a + b) (deltaBar q)
                = act (zcCompletedGroupAlgebraProjection C H target (ra + rb)) (deltaBar q) := by
                  simp only [ContinuousMonoidHom.coe_toMonoidHom,
                      zcCompletedGroupAlgebraProjection_add, hra, hrb]
            _ = (ra + rb) • deltaBar q := hact (ra + rb) (deltaBar q)
            _ = ra • deltaBar q + rb • deltaBar q := add_smul ra rb (deltaBar q)
            _ = act a (deltaBar q) + act b (deltaBar q) := by
                  rw [← hact ra (deltaBar q), ← hact rb (deltaBar q), hra, hrb] }
  let Llin :
      CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψc.toMonoidHom i)
        (zcCompletedDifferentialModuleStageSource C ψc.toMonoidHom i) →ₗ[ℕ] A :=
    Finsupp.lsum ℕ fun q => (coeffMap q).toNatLinearMap
  refine ⟨i, (fun y => Llin y), ?_⟩
  intro x
  refine Finsupp.induction_linear x ?zero ?add ?single
  · simp only [crossedDifferentialModuleLiftLinear, map_zero, ContinuousMonoidHom.coe_toMonoidHom,
      zcCompletedDifferentialModulePreStageMap]
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy
  · intro g a
    rw [crossedDifferentialModuleLiftLinear_single]
    rw [zcCompletedDifferentialModulePreStageMap_single]
    change a • delta g =
      Llin
        (Finsupp.single (zcCompletedDifferentialModuleStageSourceProj C ψc.toMonoidHom i g)
          (zcCompletedGroupAlgebraProjection C H i.target a))
    rw [Finsupp.lsum_single]
    change a • delta g =
      act (zcCompletedGroupAlgebraProjection C H target a)
        (deltaBar (zcCompletedDifferentialModuleStageSourceProj C ψc.toMonoidHom i g))
    simpa [deltaBar, zcCompletedDifferentialModuleStageSourceProj] using
      (hact a (delta g)).symm

omit [IsTopologicalGroup G] in
/--
For a profinite target module, continuity of the crossed differential forces continuity of its
pre-quotient linear lift for the finite-stage topology.
-/
theorem continuous_crossedDifferentialModuleLiftLinear_of_profiniteTarget
    {M : Type u} [AddCommGroup M] [Module (ZCCompletedGroupAlgebra C H) M]
    [TopologicalSpace M]
    [IsTopologicalRing (ZCCompletedGroupAlgebra C H)]
    [CompactSpace (ZCCompletedGroupAlgebra C H)]
    [IsTopologicalAddGroup M] [ContinuousSMul (ZCCompletedGroupAlgebra C H) M]
    [CompactSpace M] [T2Space M] [TotallyDisconnectedSpace M]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (ψc : ContinuousMonoidHom G H)
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C G)
    (delta : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom) M)
    (hcont : Continuous delta) :
    @Continuous
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
      M
      (zcCompletedDifferentialPreModuleNaturalTopology C ψc.toMonoidHom)
      inferInstance
      (crossedDifferentialModuleLiftLinear
        (R := ZCCompletedGroupAlgebra C H) delta) := by
  classical
  let : ContinuousAdd M := inferInstance
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψc.toMonoidHom
  apply _root_.CompletedGroupAlgebra.continuous_of_forall_openSubmodule_quotient_continuous
    (R := ZCCompletedGroupAlgebra C H) M
  intro W hWopen
  let hdisc : _root_.CompletedGroupAlgebra.IsDiscreteModule
      (ZCCompletedGroupAlgebra C H) (M ⧸ W) :=
    _root_.CompletedGroupAlgebra.quotient_openSubmodule_isDiscreteModule
      (ZCCompletedGroupAlgebra C H) M W hWopen
  let : DiscreteTopology (M ⧸ W) := hdisc.2
  let : ContinuousSMul (ZCCompletedGroupAlgebra C H) (M ⧸ W) := hdisc.1.2.2
  let : Fintype (M ⧸ W) :=
    Classical.choice
      (_root_.CompletedGroupAlgebra.finite_quotient_of_openSubmodule
        (ZCCompletedGroupAlgebra C H) M W hWopen)
  let deltaQ : ScalarCrossedHom
      (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom) (M ⧸ W) :=
    delta.mapLinear (Submodule.mkQ W)
  have hqcont : Continuous (Submodule.mkQ W : M → M ⧸ W) := by
    change Continuous (Submodule.Quotient.mk (p := W))
    exact continuous_quotient_mk'
  have hcontQ : Continuous deltaQ := hqcont.comp hcont
  rcases crossedDifferentialModuleLiftLinear_factors_finite_discrete
      (C := C) (H := H) (A := M ⧸ W) hC hForm ψc hG deltaQ hcontQ with
    ⟨i, L, hL⟩
  have hEq :
      (fun x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
          Submodule.mkQ W
            (crossedDifferentialModuleLiftLinear
              (R := ZCCompletedGroupAlgebra C H) delta x)) =
        crossedDifferentialModuleLiftLinear
          (R := ZCCompletedGroupAlgebra C H) deltaQ := by
    funext x
    refine Finsupp.induction_linear x ?zero ?add ?single
    · simp only [crossedDifferentialModuleLiftLinear, map_zero, deltaQ]
    · intro x y hx hy
      simp only [map_add, hx, hy]
    · intro g a
      simp only [crossedDifferentialModuleLiftLinear_single, map_smul]
      change a • Submodule.mkQ W (delta g) =
        a • Submodule.mkQ W (delta g)
      rfl
  rw [hEq]
  exact
    continuous_crossedDifferentialModuleLiftLinear_of_preStageMap_factor
      C ψc.toMonoidHom deltaQ i L hL

/--
Mathematical profinite-target universal property for \(A_{\psi}(C)\): continuous crossed
differentials into a profinite \(\mathbb{Z}_C\llbracket H\rrbracket\)-module are represented by
continuous linear maps out of the separated completed Fox module.
-/
def zcApsiContinuousCrossedDifferentialEquivContinuousLinearMapOfProfiniteTarget
    {M : Type u} [AddCommGroup M] [Module (ZCCompletedGroupAlgebra C H) M]
    [TopologicalSpace M]
    [IsTopologicalRing (ZCCompletedGroupAlgebra C H)]
    [CompactSpace (ZCCompletedGroupAlgebra C H)]
    [IsTopologicalAddGroup M] [ContinuousSMul (ZCCompletedGroupAlgebra C H) M]
    [CompactSpace M] [T2Space M] [TotallyDisconnectedSpace M]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (ψc : ContinuousMonoidHom G H)
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C G) :
    {delta : ScalarCrossedHom
        (zcCompletedGroupAlgebraScalar C ψc.toMonoidHom) M //
        Continuous delta} ≃
      (letI : TopologicalSpace (ZCApsi C ψc.toMonoidHom) :=
        zcSeparatedCompletedDifferentialModuleNaturalTopology C ψc.toMonoidHom
      ZCApsi C ψc.toMonoidHom →L[ZCCompletedGroupAlgebra C H] M) := by
  letI : T1Space M := inferInstance
  letI : ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C :=
    hForm.containsTrivialQuotients
  letI : Nonempty (ZCCompletedDifferentialModuleIndex C ψc.toMonoidHom) :=
    nonempty_zcCompletedDifferentialModuleIndex C hC ψc
  exact
    zcSeparatedCompletedContinuousCrossedDifferentialEquivContinuousLinearMap
      C ψc.toMonoidHom
      (directed_zcCompletedDifferentialModuleIndex C hForm hC ψc)
      (fun delta hcont =>
        continuous_crossedDifferentialModuleLiftLinear_of_profiniteTarget
          C hC hForm ψc hG delta hcont)

omit [IsTopologicalGroup G] in
/--
If the completed crossed-differential relation submodule is closed for the finite-stage
pre-module topology, then finite relation reductions reflect actual completed relations.
-/
theorem zcDiffModuleFiniteRelationReductionsReflectRelations_of_isClosed_relSubmodule
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ))
    (hclosed :
      @IsClosed
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
        (zcCompletedDifferentialPreModuleNaturalTopology C ψ)
        ((crossedDifferentialRelationSubmodule
          (zcCompletedGroupAlgebraScalar C ψ) :
            Submodule (ZCCompletedGroupAlgebra C H)
              (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) : Set
                (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G))) :
    zcCompletedDifferentialModuleFiniteRelationReductionsReflectRelations C ψ := by
  intro x hx
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  have hxcl :
      x ∈ closure
        ((crossedDifferentialRelationSubmodule
          (zcCompletedGroupAlgebraScalar C ψ) :
            Submodule (ZCCompletedGroupAlgebra C H)
              (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) : Set
                (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :=
    zcDiffModuleFiniteRelationReductions_mem_closure_relSubmodule
      C ψ hdir x hx
  simpa [hclosed.closure_eq] using hxcl

omit [IsTopologicalGroup G] in
/-- A named version of relation-reflection from closedness of the completed relation submodule. -/
theorem zcDiffModuleFiniteRelationReductionsReflectRelations_of_relSubmoduleClosed
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ))
    (hclosed : zcCompletedDifferentialModuleRelationSubmoduleClosed C ψ) :
    zcCompletedDifferentialModuleFiniteRelationReductionsReflectRelations C ψ :=
  zcDiffModuleFiniteRelationReductionsReflectRelations_of_isClosed_relSubmodule
    C ψ hdir hclosed

omit [IsTopologicalGroup G] in
/-- The pre-quotient separation statement is exactly finite relation-reflection. -/
theorem zcDiffModulePreStageProjsSeparate_iff_finiteRelationReductionsReflectRelations
    (C : ProCGroups.FiniteGroupClass.{u}) (ψ : G →* H) :
    zcCompletedDifferentialModulePreStageProjectionsSeparate C ψ ↔
      zcCompletedDifferentialModuleFiniteRelationReductionsReflectRelations C ψ := by
  constructor
  · intro hpre x hx
    apply hpre
    intro i
    exact
      (mem_zcDiffModulePreStageKernel_iff_preStageMap_mem_relSubmodule (C := C) (ψ := ψ) (i :=
          i) (x := x)).2 (hx i)
  · intro hreflect x hx
    apply hreflect
    intro i
    exact
      (mem_zcDiffModulePreStageKernel_iff_preStageMap_mem_relSubmodule (C := C) (ψ := ψ) (i :=
          i) (x := x)).1 (hx i)

omit [IsTopologicalGroup G] in
/--
Pre-stage separation is equivalently the claim that the crossed-differential relation submodule
is exactly the intersection of all finite-stage pre-kernels.
-/
theorem zcDiffModulePreStageProjsSeparate_iff_relSubmodule_eq_iInf_kernel
    (C : ProCGroups.FiniteGroupClass.{u}) (ψ : G →* H) :
    zcCompletedDifferentialModulePreStageProjectionsSeparate C ψ ↔
      crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) =
        zcCompletedDifferentialModulePreStageKernelIntersection C ψ := by
  constructor
  · intro hpre
    apply le_antisymm
    · intro x hx
      rw [zcCompletedDifferentialModulePreStageKernelIntersection, Submodule.mem_iInf]
      intro i
      exact
        crossedDiffRelSubmodule_le_zcDiffModulePreStageKernel
          (C := C) (ψ := ψ) i hx
    · intro x hx
      apply hpre
      intro i
      have hxi : x ∈ zcCompletedDifferentialModulePreStageKernel C ψ i := by
        exact
          (Submodule.mem_iInf
            (p := fun i : ZCCompletedDifferentialModuleIndex C ψ =>
              zcCompletedDifferentialModulePreStageKernel C ψ i)).1
            (by
              simpa [zcCompletedDifferentialModulePreStageKernelIntersection] using hx) i
      simpa using hxi
  · intro hEq x hx
    have hxint : x ∈ zcCompletedDifferentialModulePreStageKernelIntersection C ψ := by
      rw [zcCompletedDifferentialModulePreStageKernelIntersection, Submodule.mem_iInf]
      intro i
      simpa using hx i
    simpa [hEq] using hxint

omit [IsTopologicalGroup G] in
/-- Pre-quotient finite-stage separation implies separation on the algebraic quotient. -/
theorem zcDiffModuleStageProjsSeparate_of_preStageProjsSeparate
    (hpre : zcCompletedDifferentialModulePreStageProjectionsSeparate C ψ) :
    zcCompletedDifferentialModuleStageProjectionsSeparate C ψ := by
  intro a b hab
  have hcoord : ∀ i : ZCCompletedDifferentialModuleIndex C ψ,
      zcCompletedDifferentialModuleStageProjection C ψ i a =
        zcCompletedDifferentialModuleStageProjection C ψ i b := by
    intro i
    simpa [zcCompletedDifferentialModuleStageProjectionProduct,
      zcCompletedDifferentialModuleStageProjectionAdd] using congrFun hab i
  have hzero :
      ∀ z : ZCCompletedDifferentialModule C ψ,
        (∀ i : ZCCompletedDifferentialModuleIndex C ψ,
          zcCompletedDifferentialModuleStageProjection C ψ i z = 0) → z = 0 := by
    intro z
    refine Submodule.Quotient.induction_on
      (p := crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ))
      (C := fun z =>
        (∀ i : ZCCompletedDifferentialModuleIndex C ψ,
          zcCompletedDifferentialModuleStageProjection C ψ i z = 0) → z = 0)
      z ?_
    intro x hz
    apply (Submodule.Quotient.mk_eq_zero
      (p := crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ))
      (x := x)).2
    apply hpre
    intro i
    have hi := hz i
    change
      zcCompletedDifferentialModuleStageProjection C ψ i
          ((crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C ψ)).mkQ x) = 0 at hi
    rw [zcCompletedDifferentialModuleStageProjection_mkQ] at hi
    exact hi
  apply sub_eq_zero.mp
  apply hzero
  intro i
  rw [map_sub, hcoord i, sub_self]

omit [IsTopologicalGroup G] in
/-- Kernel-intersection form of finite-stage separation on the algebraic quotient. -/
theorem zcDiffModuleStageProjsSeparate_of_relSubmodule_eq_iInf_kernel
    (hker :
      crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) =
        zcCompletedDifferentialModulePreStageKernelIntersection C ψ) :
    zcCompletedDifferentialModuleStageProjectionsSeparate C ψ :=
  zcDiffModuleStageProjsSeparate_of_preStageProjsSeparate C ψ
    ((zcDiffModulePreStageProjsSeparate_iff_relSubmodule_eq_iInf_kernel (C := C) (ψ := ψ)).2 hker)

omit [IsTopologicalGroup G] in
/--
If the finite-stage projection product is injective, then equality of every finite coordinate
implies equality in the genuine universal module.
-/
theorem zcCompletedDifferentialModuleStageProjection_ext_of_separating
    (hsep : zcCompletedDifferentialModuleStageProjectionsSeparate C ψ)
    {a b : ZCCompletedDifferentialModule C ψ}
    (h : ∀ i : ZCCompletedDifferentialModuleIndex C ψ,
      zcCompletedDifferentialModuleStageProjectionAdd C ψ i a =
        zcCompletedDifferentialModuleStageProjectionAdd C ψ i b) :
    a = b := by
  apply hsep
  funext i
  exact h i

omit [IsTopologicalGroup G] in
/--
The finite-stage completed topology is Hausdorff once the finite-stage projections separate
points.
-/
theorem t2Space_zcCompletedDifferentialModuleNaturalTopology_of_separating
    (hsep : zcCompletedDifferentialModuleStageProjectionsSeparate C ψ) :
    @T2Space (ZCCompletedDifferentialModule C ψ)
      (zcCompletedDifferentialModuleNaturalTopology C ψ) := by
  let : TopologicalSpace (ZCCompletedDifferentialModule C ψ) :=
    zcCompletedDifferentialModuleNaturalTopology C ψ
  exact T2Space.of_injective_continuous hsep
    (continuous_zcCompletedDifferentialModuleStageProjectionProduct_naturalTopology C ψ)

omit [IsTopologicalGroup G] in
/-- Kernel-intersection form of the Hausdorff property for the finite-stage completed topology. -/
theorem t2Space_zcDiffModuleNaturalTopology_of_relSubmodule_eq_iInf_kernel
    (hker :
      crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) =
        zcCompletedDifferentialModulePreStageKernelIntersection C ψ) :
    @T2Space (ZCCompletedDifferentialModule C ψ)
      (zcCompletedDifferentialModuleNaturalTopology C ψ) :=
  t2Space_zcCompletedDifferentialModuleNaturalTopology_of_separating C ψ
    (zcDiffModuleStageProjsSeparate_of_relSubmodule_eq_iInf_kernel
      C ψ hker)

omit [IsTopologicalGroup G] in
/--
If finite-stage projections separate the algebraic quotient, then the defining relation
submodule is closed for the finite-stage topology on the completed pre-module.
-/
theorem zcCompletedDifferentialModuleRelationSubmoduleClosed_of_stageProjsSeparate
    (hsep : zcCompletedDifferentialModuleStageProjectionsSeparate C ψ) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed C ψ := by
  let : TopologicalSpace
      (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :=
    zcCompletedDifferentialPreModuleNaturalTopology C ψ
  let : TopologicalSpace (ZCCompletedDifferentialModule C ψ) :=
    zcCompletedDifferentialModuleNaturalTopology C ψ
  let : T2Space (ZCCompletedDifferentialModule C ψ) :=
    t2Space_zcCompletedDifferentialModuleNaturalTopology_of_separating C ψ hsep
  change IsClosed
    ((crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) :
      Submodule (ZCCompletedGroupAlgebra C H)
        (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
      Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G))
  have hpreimage :
      (((crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) :
        Submodule (ZCCompletedGroupAlgebra C H)
          (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)) :
        Set (CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G))) =
      (fun x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G =>
        (crossedDifferentialRelationSubmodule
          (zcCompletedGroupAlgebraScalar C ψ)).mkQ x) ⁻¹'
        ({0} : Set (ZCCompletedDifferentialModule C ψ)) := by
    ext x
    simp only [SetLike.mem_coe, Submodule.mkQ_apply, Set.mem_preimage, Set.mem_singleton_iff,
  Submodule.Quotient.mk_eq_zero]
  rw [hpreimage]
  exact isClosed_singleton.preimage
    (continuous_zcCompletedDifferentialModule_mkQ_naturalTopology C ψ)

omit [IsTopologicalGroup G] in
/--
Finite relation reflection implies closedness of the algebraic crossed-differential relation
submodule for the finite-stage pre-module topology.
-/
theorem zcDiffModuleRelSubmoduleClosed_of_finiteRelationReductionsReflectRelations
    (hreflect :
      zcCompletedDifferentialModuleFiniteRelationReductionsReflectRelations C ψ) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed C ψ :=
  zcCompletedDifferentialModuleRelationSubmoduleClosed_of_stageProjsSeparate C ψ
    (zcDiffModuleStageProjsSeparate_of_preStageProjsSeparate C ψ
      ((zcDiffModulePreStageProjsSeparate_iff_finiteRelationReductionsReflectRelations (C := C)
          (ψ := ψ)).2 hreflect))

omit [IsTopologicalGroup G] in
/-- Kernel-intersection formulation of finite relation reflection. -/
theorem zcDiffModuleFiniteRelationReductionsReflectRelations_iff_relSubmodule_eq_iInf_kernel
    (C : ProCGroups.FiniteGroupClass.{u}) (ψ : G →* H) :
    zcCompletedDifferentialModuleFiniteRelationReductionsReflectRelations C ψ ↔
      crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) =
        zcCompletedDifferentialModulePreStageKernelIntersection C ψ :=
  (zcDiffModulePreStageProjsSeparate_iff_finiteRelationReductionsReflectRelations (C := C) (ψ :=
      ψ)).symm.trans
    (zcDiffModulePreStageProjsSeparate_iff_relSubmodule_eq_iInf_kernel (C := C) (ψ := ψ))

omit [IsTopologicalGroup G] in
/--
In the directed finite-stage situation, closedness of the completed relation submodule is
equivalent to finite-stage separation of the algebraic quotient.
-/
theorem zcDiffModuleRelSubmoduleClosed_iff_stageProjsSeparate
    {C : ProCGroups.FiniteGroupClass.{u}} {ψ : G →* H}
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ)) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed C ψ ↔
      zcCompletedDifferentialModuleStageProjectionsSeparate C ψ := by
  constructor
  · intro hclosed
    exact
      zcDiffModuleStageProjsSeparate_of_preStageProjsSeparate C ψ
        ((zcDiffModulePreStageProjsSeparate_iff_finiteRelationReductionsReflectRelations (C :=
            C) (ψ := ψ)).2
          (zcDiffModuleFiniteRelationReductionsReflectRelations_of_relSubmoduleClosed
            C ψ hdir hclosed))
  · intro hsep
    exact zcCompletedDifferentialModuleRelationSubmoduleClosed_of_stageProjsSeparate C ψ hsep

omit [IsTopologicalGroup G] in
/--
In the directed finite-stage situation, closedness of the defining relation submodule is
equivalent to Hausdorffness of the finite-stage natural topology on the algebraic quotient. This
is the mathematical version of the paper-level principle that the source completion/closure has
been reflected correctly into the closed quotient exactly when the finite-stage topology on the
algebraic universal module is separated.
-/
theorem zcCompletedDifferentialModuleRelationSubmoduleClosed_iff_t2_naturalTopology
    {C : ProCGroups.FiniteGroupClass.{u}} {ψ : G →* H}
    [Nonempty (ZCCompletedDifferentialModuleIndex C ψ)]
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ)) :
    zcCompletedDifferentialModuleRelationSubmoduleClosed C ψ ↔
      @T2Space (ZCCompletedDifferentialModule C ψ)
        (zcCompletedDifferentialModuleNaturalTopology C ψ) := by
  constructor
  · intro hclosed
    exact
      t2Space_zcCompletedDifferentialModuleNaturalTopology_of_separating C ψ
        ((zcDiffModuleRelSubmoduleClosed_iff_stageProjsSeparate (C := C) (ψ := ψ) hdir).1 hclosed)
  · intro hT2
    let : TopologicalSpace (ZCCompletedDifferentialModule C ψ) :=
      zcCompletedDifferentialModuleNaturalTopology C ψ
    let : T2Space (ZCCompletedDifferentialModule C ψ) := hT2
    exact
      zcCompletedDifferentialModuleRelationSubmoduleClosed_of_t1_naturalTopology
        C ψ (by infer_instance)

omit [IsTopologicalGroup G] in
/-- Addition is continuous for the finite-stage completed topology. -/
theorem continuous_add_zcCompletedDifferentialModuleNaturalTopology :
    letI : TopologicalSpace (ZCCompletedDifferentialModule C ψ) :=
      zcCompletedDifferentialModuleNaturalTopology C ψ
    Continuous (fun p : ZCCompletedDifferentialModule C ψ ×
        ZCCompletedDifferentialModule C ψ => p.1 + p.2) := by
  let : TopologicalSpace (ZCCompletedDifferentialModule C ψ) :=
    zcCompletedDifferentialModuleNaturalTopology C ψ
  rw [continuous_induced_rng]
  change Continuous
    (fun p : ZCCompletedDifferentialModule C ψ ×
        ZCCompletedDifferentialModule C ψ =>
      fun i : ZCCompletedDifferentialModuleIndex C ψ =>
        zcCompletedDifferentialModuleStageProjectionAdd C ψ i (p.1 + p.2))
  simpa [map_add] using
    (continuous_pi fun i =>
      ((continuous_zcCompletedDifferentialModuleStageProjectionAdd_naturalTopology C ψ i).comp
          continuous_fst).add
        ((continuous_zcCompletedDifferentialModuleStageProjectionAdd_naturalTopology C ψ i).comp
          continuous_snd))

omit [IsTopologicalGroup G] in
/-- Negation is continuous for the finite-stage completed topology. -/
theorem continuous_neg_zcCompletedDifferentialModuleNaturalTopology :
    letI : TopologicalSpace (ZCCompletedDifferentialModule C ψ) :=
      zcCompletedDifferentialModuleNaturalTopology C ψ
    Continuous (fun a : ZCCompletedDifferentialModule C ψ => -a) := by
  let : TopologicalSpace (ZCCompletedDifferentialModule C ψ) :=
    zcCompletedDifferentialModuleNaturalTopology C ψ
  rw [continuous_induced_rng]
  change Continuous
    (fun a : ZCCompletedDifferentialModule C ψ =>
      fun i : ZCCompletedDifferentialModuleIndex C ψ =>
        zcCompletedDifferentialModuleStageProjectionAdd C ψ i (-a))
  simpa [map_neg] using
    (continuous_pi fun i =>
      (continuous_zcCompletedDifferentialModuleStageProjectionAdd_naturalTopology C ψ i).neg)

omit [IsTopologicalGroup G] in
/-- The finite-stage completed topology is an additive group topology. -/
theorem isTopologicalAddGroup_zcCompletedDifferentialModuleNaturalTopology :
    @IsTopologicalAddGroup (ZCCompletedDifferentialModule C ψ)
      (zcCompletedDifferentialModuleNaturalTopology C ψ) _ := by
  let : TopologicalSpace (ZCCompletedDifferentialModule C ψ) :=
    zcCompletedDifferentialModuleNaturalTopology C ψ
  exact
    { continuous_add := by
        simpa using continuous_add_zcCompletedDifferentialModuleNaturalTopology C ψ
      continuous_neg := by
        simpa using continuous_neg_zcCompletedDifferentialModuleNaturalTopology C ψ }

/-- The finite-stage differential is continuous as a map out of the source group. -/
theorem continuous_zcCompletedDifferentialModuleStageDifferential
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    Continuous (zcCompletedDifferentialModuleStageDifferential C ψ i) := by
  let : DiscreteTopology (zcCompletedDifferentialModuleStageSource C ψ i) :=
    ProCGroups.ProC.OpenNormalSubgroup.quotientDiscrete (G := G) i.source.1
  have hdiff :
      Continuous (fun q : zcCompletedDifferentialModuleStageSource C ψ i =>
        universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ i) q) :=
    continuous_of_discreteTopology
  have hsource :
      Continuous (zcCompletedDifferentialModuleStageSourceProj C ψ i) :=
    QuotientGroup.continuous_mk
  have hcomp := hdiff.comp hsource
  change Continuous (zcCompletedDifferentialModuleStageDifferential C ψ i) at hcomp
  exact hcomp

/--
The universal differential is continuous for the finite-stage completed topology on the
algebraic quotient.
-/
theorem continuous_zcUniversalDifferential_naturalTopology :
    @Continuous G (ZCCompletedDifferentialModule C ψ) inferInstance
      (zcCompletedDifferentialModuleNaturalTopology C ψ)
      (zcUniversalDifferential C ψ) := by
  rw [continuous_induced_rng]
  change Continuous
    (fun g : G =>
      fun i : ZCCompletedDifferentialModuleIndex C ψ =>
        zcCompletedDifferentialModuleStageProjectionAdd C ψ i
          (zcUniversalDifferential C ψ g))
  refine continuous_pi fun i => ?_
  simpa using continuous_zcCompletedDifferentialModuleStageDifferential C ψ i

/--
The universal final topology on the algebraic quotient is below the finite-stage completed
topology.
-/
theorem zcUniversalDifferentialFinalTopology_le_naturalTopology :
    zcUniversalDifferentialFinalTopology C ψ ≤
      zcCompletedDifferentialModuleNaturalTopology C ψ :=
  (continuous_zcUniversalDifferential_naturalTopology C ψ).coinduced_le

omit [IsTopologicalGroup G] in
/--
The finite-stage boundary map is continuous for the completed differential-module topology
defined by the finite-stage projections.
-/
theorem continuous_zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    Continuous (zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap C ψ i) :=
  continuous_of_discreteTopology

omit [IsTopologicalGroup G] in
/-- The algebraic completed boundary is continuous for the finite-stage completed topology. -/
theorem continuous_zcToCompletedGroupAlgebra_naturalTopology
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψc : ContinuousMonoidHom G H) :
    @Continuous (ZCCompletedDifferentialModule C ψc.toMonoidHom)
      (ZCCompletedGroupAlgebra C H)
      (zcCompletedDifferentialModuleNaturalTopology C ψc.toMonoidHom) inferInstance
      (zcToCompletedGroupAlgebra C ψc.toMonoidHom) := by
  let : TopologicalSpace (ZCCompletedDifferentialModule C ψc.toMonoidHom) :=
    zcCompletedDifferentialModuleNaturalTopology C ψc.toMonoidHom
  have hval : Continuous (fun a : ZCCompletedDifferentialModule C ψc.toMonoidHom =>
      ((zcToCompletedGroupAlgebra C ψc.toMonoidHom a : ZCCompletedGroupAlgebra C H) :
        (j : ZCCompletedGroupAlgebraIndex C H) → ZCCompletedGroupAlgebraStage C H j)) := by
    refine continuous_pi fun j => ?_
    let i := zcCompletedDifferentialModuleComapIndex C hC ψc j
    have hstage : Continuous (fun a : ZCCompletedDifferentialModule C ψc.toMonoidHom =>
        zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap C ψc.toMonoidHom i
          (zcCompletedDifferentialModuleStageProjection C ψc.toMonoidHom i a)) :=
      (continuous_zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap
          C ψc.toMonoidHom i).comp
        (continuous_zcCompletedDifferentialModuleStageProjection_naturalTopology
          C ψc.toMonoidHom i)
    have hcoord :
        (fun a : ZCCompletedDifferentialModule C ψc.toMonoidHom =>
          zcCompletedGroupAlgebraProjection C H j
            (zcToCompletedGroupAlgebra C ψc.toMonoidHom a)) =
        (fun a : ZCCompletedDifferentialModule C ψc.toMonoidHom =>
          zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap C ψc.toMonoidHom i
            (zcCompletedDifferentialModuleStageProjection C ψc.toMonoidHom i a)) := by
      funext a
      have h :=
        congrArg (fun f =>
          f a)
          (zcDiffModuleStageBoundaryCompletedLinearMap_comp_stageProj
            C ψc.toMonoidHom i)
      change
        zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap C ψc.toMonoidHom i
              (zcCompletedDifferentialModuleStageProjection C ψc.toMonoidHom i a) =
          zcCompletedGroupAlgebraProjectionLinearMap C H i.target
            (zcToCompletedGroupAlgebra C ψc.toMonoidHom a) at h
      change
        zcCompletedGroupAlgebraProjectionLinearMap C H i.target
              (zcToCompletedGroupAlgebra C ψc.toMonoidHom a) =
          zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap C ψc.toMonoidHom i
            (zcCompletedDifferentialModuleStageProjection C ψc.toMonoidHom i a)
      exact h.symm
    rw [hcoord]
    exact hstage
  simpa only [Subtype.eta] using
    (Continuous.subtype_mk (p := ZCCompletedGroupAlgebraCompatible C H) hval
      (fun a => (zcToCompletedGroupAlgebra C ψc.toMonoidHom a).property))

omit [IsTopologicalGroup G] in
/--
Scalar multiplication by \(\mathbb{Z}_C\llbracket H\rrbracket\) is continuous for the
finite-stage completed topology.
-/
theorem continuousSMul_zcCompletedDifferentialModuleNaturalTopology :
    @ContinuousSMul (ZCCompletedGroupAlgebra C H)
      (ZCCompletedDifferentialModule C ψ)
      inferInstance inferInstance (zcCompletedDifferentialModuleNaturalTopology C ψ) := by
  let : TopologicalSpace (ZCCompletedDifferentialModule C ψ) :=
    zcCompletedDifferentialModuleNaturalTopology C ψ
  refine ⟨?_⟩
  rw [continuous_induced_rng]
  change Continuous
    (fun p : ZCCompletedGroupAlgebra C H × ZCCompletedDifferentialModule C ψ =>
      fun i : ZCCompletedDifferentialModuleIndex C ψ =>
        zcCompletedDifferentialModuleStageProjectionAdd C ψ i (p.1 • p.2))
  refine continuous_pi fun i => ?_
  let : TopologicalSpace (zcCompletedDifferentialModuleStageRing C ψ i) := inferInstance
  let : DiscreteTopology (zcCompletedDifferentialModuleStageRing C ψ i) := inferInstance
  have hstageAction :
      Continuous (fun p : zcCompletedDifferentialModuleStageRing C ψ i ×
          ZCCompletedDifferentialModuleStage C ψ i => p.1 • p.2) :=
    continuous_of_discreteTopology
  have hcoeff :
      Continuous (fun a : ZCCompletedGroupAlgebra C H =>
        zcCompletedGroupAlgebraProjectionRingHom C H i.target a) :=
    continuous_zcCompletedGroupAlgebraProjectionRingHom (C := C) (G := H) i.target
  have hmodule :
      Continuous (fun a : ZCCompletedDifferentialModule C ψ =>
        zcCompletedDifferentialModuleStageProjectionAdd C ψ i a) :=
    continuous_zcCompletedDifferentialModuleStageProjectionAdd_naturalTopology C ψ i
  have hpair :
      Continuous (fun p : ZCCompletedGroupAlgebra C H ×
          ZCCompletedDifferentialModule C ψ =>
        (zcCompletedGroupAlgebraProjectionRingHom C H i.target p.1,
          zcCompletedDifferentialModuleStageProjectionAdd C ψ i p.2)) :=
    (hcoeff.comp continuous_fst).prodMk (hmodule.comp continuous_snd)
  have hcomp :
      Continuous
        ((fun p : zcCompletedDifferentialModuleStageRing C ψ i ×
            ZCCompletedDifferentialModuleStage C ψ i => p.1 • p.2) ∘
          fun p : ZCCompletedGroupAlgebra C H ×
              ZCCompletedDifferentialModule C ψ =>
            (zcCompletedGroupAlgebraProjectionRingHom C H i.target p.1,
              zcCompletedDifferentialModuleStageProjectionAdd C ψ i p.2)) :=
    hstageAction.comp hpair
  have hfun :
      (fun p : ZCCompletedGroupAlgebra C H × ZCCompletedDifferentialModule C ψ =>
        zcCompletedDifferentialModuleStageProjectionAdd C ψ i (p.1 • p.2)) =
        ((fun p : zcCompletedDifferentialModuleStageRing C ψ i ×
            ZCCompletedDifferentialModuleStage C ψ i => p.1 • p.2) ∘
          fun p : ZCCompletedGroupAlgebra C H ×
              ZCCompletedDifferentialModule C ψ =>
            (zcCompletedGroupAlgebraProjectionRingHom C H i.target p.1,
              zcCompletedDifferentialModuleStageProjectionAdd C ψ i p.2)) := by
    funext p
    change
      zcCompletedDifferentialModuleStageProjection C ψ i (p.1 • p.2) =
        zcCompletedGroupAlgebraProjectionRingHom C H i.target p.1 •
          zcCompletedDifferentialModuleStageProjection C ψ i p.2
    rw [map_smul, zcCompletedDifferentialModuleStage_completed_smul]
  rw [hfun]
  exact hcomp

end

end FoxDifferential
