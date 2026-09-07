import ProCGroups.FoxDifferential.Completed.FiniteStage.RelationReflection
import ProCGroups.FoxDifferential.Completed.FreeProC.FiniteQuotientStages
import ProCGroups.FoxDifferential.Completed.Continuous.Universal.NaturalTopology
import ProCGroups.FreeProC.FiniteBasis

set_option autoImplicit false

/-!
# Relation reflection for free pro-\(C\) presentations

This module supplies the finite free-basis family used to reflect completed
Fox relations through finite quotient stages, and relates stagewise
vanishing to equality in the completed differential module.
-/

namespace CrowellExactSequence

noncomputable section

open scoped Topology
open ProCGroups.InverseSystems
open ProCGroups.ProC
open FoxDifferential

universe u v

section FreeRelationReflection

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable {H : Type u}
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
variable [T2Space H]

/-- The universe-lifted finite free basis supplies the relation-reflection family. -/
abbrev freeProCReflectionFamily
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r) : ULift.{u} (Fin r) → sourceData.carrier :=
  freeProCChosenULiftFamilyOfBasisCard (C := C) sourceData hbasis

omit [T2Space H] in
/-- The target images of the chosen basis topologically generate a surjective target. -/
theorem freeProCReflectionFamily_target_generates
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi) :
    ProCGroups.Generation.TopologicallyGenerates
      (G := H)
      (Set.range (fun i : ULift.{u} (Fin r) =>
        psi (freeProCReflectionFamily (C := C) sourceData hbasis i))) := by
  simpa [freeProCReflectionFamily] using
    freeProCChosenULiftFamilyOfBasisCard_image_generates_of_surjective
      (C := C) sourceData hbasis psi hpsi

/-- The free-group map onto the source quotient used by a differential-module finite stage. -/
def freeProCRelationReflectionStageSourceHom
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom) :
    FreeGroup (ULift.{u} (Fin r)) →*
      zcCompletedDifferentialModuleStageSource
        C psi.toMonoidHom i :=
  (zcCompletedDifferentialModuleStageSourceProj
      C psi.toMonoidHom i).comp
    (FreeGroup.lift (freeProCReflectionFamily (C := C) sourceData hbasis))

/--
The source kernel used by a differential-module stage, pulled back to the abstract free group
on the chosen basis.
-/
def freeProCRelationReflectionStageKernel
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom) :
    Subgroup (FreeGroup (ULift.{u} (Fin r))) :=
  MonoidHom.ker
    (freeProCRelationReflectionStageSourceHom (C := C) sourceData hbasis psi i)

/--
The relation-reflection stage kernel is a normal subgroup of the free group on the lifted
finite basis.
-/
instance freeProCRelationReflectionStageKernel_normal
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom) :
    (freeProCRelationReflectionStageKernel (C := C) sourceData hbasis psi i).Normal := by
  dsimp [freeProCRelationReflectionStageKernel]
  infer_instance

omit [IsTopologicalGroup H] [T2Space H] in
/-- The chosen free basis surjects onto every finite source quotient stage. -/
theorem freeProCRelationReflectionStageSourceHom_surjective
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom) :
    Function.Surjective
      (freeProCRelationReflectionStageSourceHom (C := C) sourceData hbasis psi i) := by
  classical
  let X : Type u := ULift.{u} (Fin r)
  let ι : X → sourceData.carrier := freeProCReflectionFamily (C := C) sourceData hbasis
  let Q : Type u :=
    zcCompletedDifferentialModuleStageSource
      C psi.toMonoidHom i
  let : DiscreteTopology Q :=
    QuotientGroup.discreteTopology i.source.1.toOpenSubgroup.isOpen'
  let g : X → Q := fun x =>
    zcCompletedDifferentialModuleStageSourceProj
      C psi.toMonoidHom i (ι x)
  have hsource :
      ProCGroups.Generation.TopologicallyGenerates
        (G := sourceData.carrier) (Set.range ι) := by
    simpa [ι, freeProCReflectionFamily] using
      freeProCChosenULiftFamilyOfBasisCard_generates (C := C) sourceData hbasis
  have hquot_image :
      ProCGroups.Generation.TopologicallyGenerates
        (G := Q)
        ((QuotientGroup.mk' (i.source.1 : Subgroup sourceData.carrier)) '' Set.range ι) := by
    simpa [Q] using
      ProCGroups.Generation.topologicallyGenerates_quotient_image
        (G := sourceData.carrier) (N := (i.source.1 : Subgroup sourceData.carrier)) hsource
  have hrange :
      ((QuotientGroup.mk' (i.source.1 : Subgroup sourceData.carrier)) '' Set.range ι) =
        Set.range g := by
    ext y
    constructor
    · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨ι a, ⟨a, rfl⟩, rfl⟩
  have hg :
      ProCGroups.Generation.TopologicallyGenerates (G := Q) (Set.range g) := by
    rw [← hrange]
    exact hquot_image
  have hsurj : Function.Surjective (FreeGroup.lift g) :=
    ProCGroups.FiniteGeneration.freeGroup_lift_surjective_of_topologicallyGenerates_discrete
      (G := Q) g hg
  have hlift :
      FreeGroup.lift g =
        freeProCRelationReflectionStageSourceHom (C := C) sourceData hbasis psi i := by
    apply FreeGroup.ext_hom
    intro x
    rw [FreeGroup.lift_apply_of]
    change
      zcCompletedDifferentialModuleStageSourceProj
        C psi.toMonoidHom i (ι x) =
      zcCompletedDifferentialModuleStageSourceProj
        C psi.toMonoidHom i
        ((FreeGroup.lift (freeProCReflectionFamily (C := C) sourceData hbasis))
          (FreeGroup.of x))
    rw [FreeGroup.lift_apply_of]
  simpa [hlift] using hsurj

/-- Identification of the source quotient stage with the corresponding free-group quotient. -/
def freeProCRelationReflectionStageSourceEquiv
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom) :
    foxAlgebraicStageTargetQuotient
        (X := ULift.{u} (Fin r))
        (freeProCRelationReflectionStageKernel (C := C) sourceData hbasis psi i) ≃*
      zcCompletedDifferentialModuleStageSource
        C psi.toMonoidHom i :=
  QuotientGroup.quotientKerEquivOfSurjective
    (freeProCRelationReflectionStageSourceHom (C := C) sourceData hbasis psi i)
    (freeProCRelationReflectionStageSourceHom_surjective
      (C := C) sourceData hbasis psi i)

omit [IsTopologicalGroup H] [T2Space H] in
/--
The relation-reflection source-stage equivalence sends the quotient class of a free word to its
image under the corresponding source-stage homomorphism.
-/
@[simp]
theorem freeProCRelationReflectionStageSourceEquiv_mk
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom)
    (w : FreeGroup (ULift.{u} (Fin r))) :
    freeProCRelationReflectionStageSourceEquiv (C := C) sourceData hbasis psi i
        (QuotientGroup.mk'
          (freeProCRelationReflectionStageKernel (C := C) sourceData hbasis psi i) w) =
      freeProCRelationReflectionStageSourceHom (C := C) sourceData hbasis psi i w :=
  rfl

/--
The target finite Fox relation kernel attached to the target quotient of a
\(\mathbb{Z}_C\)-completed differential-module index.
-/
abbrev freeProCRelationReflectionTargetStageKernel
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom) :
    Subgroup (FreeGroup (ULift.{u} (Fin r))) :=
  freeProCFiniteQuotientStageKernel
    (C := C)
    (fun x : ULift.{u} (Fin r) =>
      psi (freeProCReflectionFamily (C := C) sourceData hbasis x))
    i.target.2

/-- The target finite Fox relation kernel is normal. -/
instance freeProCRelationReflectionTargetStageKernel_normal
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom) :
    (freeProCRelationReflectionTargetStageKernel (C := C) sourceData hbasis psi i).Normal :=
  inferInstance

omit [T2Space H] in
/-- Target finite Fox kernels are antitone along differential-module stage refinement. -/
theorem freeProCRelationReflectionTargetStageKernel_antitone
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    {i j : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom} (hij : i ≤ j) :
    freeProCRelationReflectionTargetStageKernel (C := C) sourceData hbasis psi j ≤
      freeProCRelationReflectionTargetStageKernel (C := C) sourceData hbasis psi i := by
  exact freeProCFiniteQuotientStageKernel_antitone
    (C := C)
    (fun x : ULift.{u} (Fin r) =>
      psi (freeProCReflectionFamily (C := C) sourceData hbasis x))
    hij.2.2

/-- The canonical target quotient comparison map \(H/U_i \to F_X/N_i\). -/
def freeProCRelationReflectionTargetStageQMap
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (i : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom) :
    CompletedGroupAlgebraQuotientInClass H C i.target.2 →*
      foxAlgebraicStageTargetQuotient
        (X := ULift.{u} (Fin r))
        (freeProCRelationReflectionTargetStageKernel (C := C) sourceData hbasis psi i) := by
  let φ : ULift.{u} (Fin r) → H := fun x =>
    psi (freeProCReflectionFamily (C := C) sourceData hbasis x)
  have hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ) := by
    simpa [φ] using
      freeProCReflectionFamily_target_generates (C := C) sourceData hbasis psi hpsi
  letI : DiscreteTopology
      (CompletedGroupAlgebraQuotientInClass H C i.target.2) :=
    QuotientGroup.discreteTopology
      (ProCGroups.openNormalSubgroup_isOpen (G := H)
        ((OrderDual.ofDual i.target.2).1 : OpenNormalSubgroup H))
  exact freeProCFiniteQuotientStageQMap
    (C := C) φ i.target.2
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := C) φ i.target.2 hφgen)

omit [T2Space H] in
/--
The generator formula for the free pro-\(C\) relation-reflection target finite-stage quotient
map identifies the specified Crowell boundary or coordinate map.
-/
@[simp 900]
theorem freeProCRelationReflectionTargetStageQMap_generator
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (i : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom)
    (x : ULift.{u} (Fin r)) :
    freeProCRelationReflectionTargetStageQMap (C := C) sourceData hbasis psi hpsi i
        (QuotientGroup.mk
          (psi (freeProCReflectionFamily (C := C) sourceData hbasis x))) =
      QuotientGroup.mk'
        (freeProCRelationReflectionTargetStageKernel (C := C) sourceData hbasis psi i)
        (FreeGroup.of x) := by
  let φ : ULift.{u} (Fin r) → H := fun x =>
    psi (freeProCReflectionFamily (C := C) sourceData hbasis x)
  change
    freeProCRelationReflectionTargetStageQMap
        (C := C) sourceData hbasis psi hpsi i (QuotientGroup.mk (φ x)) =
      QuotientGroup.mk'
        (freeProCRelationReflectionTargetStageKernel (C := C) sourceData hbasis psi i)
        (FreeGroup.of x)
  unfold freeProCRelationReflectionTargetStageQMap
  simp only [freeProCFiniteQuotientStageQMap_generator,
    freeProCRelationReflectionTargetStageKernel, ContinuousMonoidHom.coe_toMonoidHom,
    QuotientGroup.mk'_apply, φ]

omit [T2Space H] in
/-- Target quotient comparison maps commute with differential-module stage refinement. -/
theorem freeProCRelationReflectionTargetStageQMap_transition
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    {i j : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom} (hij : i ≤ j)
    (q : CompletedGroupAlgebraQuotientInClass H C j.target.2) :
    freeProCRelationReflectionTargetStageQMap (C := C) sourceData hbasis psi hpsi i
        ((OpenNormalSubgroupInClass.map
          (C := C) (G := H)
          (U := OrderDual.ofDual i.target.2)
          (V := OrderDual.ofDual j.target.2) hij.2.2) q) =
      foxAlgebraicStageTargetQuotientMap
        (X := ULift.{u} (Fin r))
        (freeProCRelationReflectionTargetStageKernel_antitone
          (C := C) sourceData hbasis psi hij)
        (freeProCRelationReflectionTargetStageQMap
          (C := C) sourceData hbasis psi hpsi j q) := by
  let φ : ULift.{u} (Fin r) → H := fun x =>
    psi (freeProCReflectionFamily (C := C) sourceData hbasis x)
  have hφgen :
      ProCGroups.Generation.TopologicallyGenerates (G := H) (Set.range φ) := by
    simpa [φ] using
      freeProCReflectionFamily_target_generates (C := C) sourceData hbasis psi hpsi
  let : DiscreteTopology
      (CompletedGroupAlgebraQuotientInClass H C i.target.2) :=
    QuotientGroup.discreteTopology
      (ProCGroups.openNormalSubgroup_isOpen (G := H)
        ((OrderDual.ofDual i.target.2).1 : OpenNormalSubgroup H))
  let : DiscreteTopology
      (CompletedGroupAlgebraQuotientInClass H C j.target.2) :=
    QuotientGroup.discreteTopology
      (ProCGroups.openNormalSubgroup_isOpen (G := H)
        ((OrderDual.ofDual j.target.2).1 : OpenNormalSubgroup H))
  unfold freeProCRelationReflectionTargetStageQMap
  exact freeProCFiniteQuotientStageQMap_transition
    (C := C) φ hij.2.2
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := C) φ i.target.2 hφgen)
    (freeProCFiniteQuotientStageHom_surjective_of_topologicallyGenerates
      (C := C) φ j.target.2 hφgen)
    q

/-- The target component map used by finite Fox semidirect stages. -/
def freeProCRelationReflectionTargetStageRight
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (i : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom) :
    H →* foxAlgebraicStageTargetQuotient
        (X := ULift.{u} (Fin r))
        (freeProCRelationReflectionTargetStageKernel (C := C) sourceData hbasis psi i) :=
  (freeProCRelationReflectionTargetStageQMap
    (C := C) sourceData hbasis psi hpsi i).comp
    (openNormalSubgroupInClassProj
      (C := C) (G := H) i.target.2)

omit [T2Space H] in
/--
The target-stage right map sends the chosen generator to its quotient class in the
relation-reflection target stage.
-/
@[simp 900]
theorem freeProCRelationReflectionTargetStageRight_generator
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (i : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom)
    (x : ULift.{u} (Fin r)) :
    freeProCRelationReflectionTargetStageRight (C := C) sourceData hbasis psi hpsi i
        (psi (freeProCReflectionFamily (C := C) sourceData hbasis x)) =
      QuotientGroup.mk'
        (freeProCRelationReflectionTargetStageKernel (C := C) sourceData hbasis psi i)
        (FreeGroup.of x) := by
  change
    freeProCRelationReflectionTargetStageQMap
        (C := C) sourceData hbasis psi hpsi i
        (QuotientGroup.mk
          (psi (freeProCReflectionFamily (C := C) sourceData hbasis x))) =
      QuotientGroup.mk'
        (freeProCRelationReflectionTargetStageKernel (C := C) sourceData hbasis psi i)
        (FreeGroup.of x)
  exact freeProCRelationReflectionTargetStageQMap_generator
    (C := C) sourceData hbasis psi hpsi i x

/-- The finite Fox semidirect projection attached to one target quotient stage. -/
def freeProCRelationReflectionTargetStageMap
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (hpsi : Function.Surjective psi)
    (i : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom) :
    ZCCompletedFoxSemidirect C (ULift.{u} (Fin r)) H →*
      FoxAlgebraicStageSemidirect
        (X := ULift.{u} (Fin r))
        (freeProCRelationReflectionTargetStageKernel (C := C) sourceData hbasis psi i)
        i.target.1.modulus := by
  letI : ∀ j : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom,
      Fact (0 < j.target.1.modulus) :=
    fun j => ProCGroups.Completion.ProCIntegerIndex.positiveFact j.target.1
  exact
    freeProCZCCompletedFoxSemidirectZCBifilteredStageMap
      (C := C) (X := ULift.{u} (Fin r)) (H := H)
      (Nstage := fun j =>
        freeProCRelationReflectionTargetStageKernel (C := C) sourceData hbasis psi j)
      (nstage := fun j => j.target.1.modulus)
      (zcIndex := fun j => j.target)
      (hmod := fun _ => dvd_rfl)
      (qmap := fun j =>
        freeProCRelationReflectionTargetStageQMap
          (C := C) sourceData hbasis psi hpsi j)
      i

omit [T2Space H] in
/--
Each target finite stage attached to the chosen free pro-\(C\) basis satisfies the finite Fox
relation-boundary module exactness needed by the approximation theorem.
-/
theorem freeProCRelationReflection_finiteStage_relationBoundaryModuleExact
    (sourceData :
      ProCGroups.FreeProC.EpimorphicallyFreeProCGroupOnConvergingSetData.{u, u} C)
    {r : Nat}
    (hbasis : Cardinal.mk sourceData.basis = r)
    (psi : ContinuousMonoidHom sourceData.carrier H)
    (i : ZCCompletedDifferentialModuleIndex
      C psi.toMonoidHom) :
    foxAlgebraicStageRelationBoundaryModuleExact
      (X := ULift.{u} (Fin r))
      (freeProCRelationReflectionTargetStageKernel (C := C) sourceData hbasis psi i)
      i.target.1.modulus := by
  exact
    foxAlgebraicStageRelationBoundaryModuleExact_of_sourceBoundaryRelReduction
      (X := ULift.{u} (Fin r))
      (freeProCRelationReflectionTargetStageKernel (C := C) sourceData hbasis psi i)
      i.target.1.modulus
      (foxAlgebraicStageSourceBoundaryRelationIdealReduction_of_relationIdeal_derivatives
        (X := ULift.{u} (Fin r))
        (freeProCRelationReflectionTargetStageKernel (C := C) sourceData hbasis psi i)
        i.target.1.modulus)

end FreeRelationReflection

end

end CrowellExactSequence
