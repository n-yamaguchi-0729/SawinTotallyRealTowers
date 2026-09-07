import ProCGroups.FoxDifferential.Completed.Continuous.Universal.Basic
import ProCGroups.InverseSystems.Utilities

set_option autoImplicit false

/-!
# Fox differential: completed — continuous — universal — finite stage

The principal declarations in this module are:

- `ZCCompletedDifferentialModuleIndex`
  A finite stage for the completed universal differential module. It consists of a finite source
  quotient \(G/V\), a coefficient-and-target stage \((\mathbb{Z}/n\mathbb{Z})[H/U]\) of
  \(\mathbb{Z}_C\llbracket H\rrbracket\), and the compatibility \(\psi(V)\leq U\) needed to descend
  \(\psi\) to \(G/V\to H/U\).
- `zcCompletedDifferentialModuleComapIndex`
  The finite stage whose source quotient is the pullback of a target finite quotient along a
  continuous homomorphism.
- `le_def`
  The order on completed differential-module indices is the simultaneous refinement order on source,
  target, and coefficient stages.
- `nonempty_zcCompletedDifferentialModuleIndex`
  The finite-stage index type is nonempty for a continuous homomorphism: take the pullback of the
  terminal completed group-algebra target stage.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.Completion
open ProCGroups.ProC

universe u

variable (C : ProCGroups.FiniteGroupClass.{u})
variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
A finite stage for the completed universal differential module. It consists of a finite source
quotient \(G/V\), a coefficient-and-target stage \((\mathbb{Z}/n\mathbb{Z})[H/U]\) of
\(\mathbb{Z}_C\llbracket H\rrbracket\), and the compatibility \(\psi(V)\leq U\) needed to
descend \(\psi\) to \(G/V\to H/U\).
-/
structure ZCCompletedDifferentialModuleIndex (ψ : G →* H) where
  /-- The open-normal source subgroup defining the finite quotient of \(G\). -/
  source : OpenNormalSubgroupInClass C G
  /-- The coefficient-and-target stage of the completed group algebra of \(H\). -/
  target : ZCCompletedGroupAlgebraIndex C H
  /-- The source subgroup maps into the target subgroup, so \(\psi\) descends to the quotients. -/
  compatible :
    (source.1 : Subgroup G) ≤
      ((OrderDual.ofDual target.2).1 : Subgroup H).comap ψ

namespace ZCCompletedDifferentialModuleIndex

variable {C}
variable {ψ : G →* H}

/--
Completed differential-module indices order source subgroups contravariantly and target stages
covariantly.
-/
instance instLE : LE (ZCCompletedDifferentialModuleIndex C ψ) where
  le i j :=
    (j.source.1 : Subgroup G) ≤ (i.source.1 : Subgroup G) ∧ i.target ≤ j.target

/-- The simultaneous source-and-target refinement relation defines a preorder on stage indices. -/
instance instPreorder : Preorder (ZCCompletedDifferentialModuleIndex C ψ) where
  le := (· ≤ ·)
  le_refl i := ⟨le_rfl, le_rfl⟩
  le_trans i j k hij hjk :=
    ⟨hjk.1.trans hij.1, hij.2.trans hjk.2⟩

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/--
The order on completed differential-module indices is the simultaneous refinement order on
source, target, and coefficient stages.
-/
@[simp]
theorem le_def {i j : ZCCompletedDifferentialModuleIndex C ψ} :
    i ≤ j ↔
      (j.source.1 : Subgroup G) ≤ (i.source.1 : Subgroup G) ∧ i.target ≤ j.target :=
  Iff.rfl

end ZCCompletedDifferentialModuleIndex

variable (ψ : G →* H)

/--
The finite stage whose source quotient is the pullback of a target finite quotient along a
continuous homomorphism.
-/
def zcCompletedDifferentialModuleComapIndex
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψc : ContinuousMonoidHom G H)
    (i : ZCCompletedGroupAlgebraIndex C H) :
    ZCCompletedDifferentialModuleIndex C ψc.toMonoidHom where
  source := OrderDual.ofDual
    (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hC ψc i.2)
  target := i
  compatible := by
    intro g hg
    change ψc.toMonoidHom g ∈
      ((((OrderDual.ofDual i.2).1 : OpenNormalSubgroup H) : Subgroup H))
    simpa [completedGroupAlgebraComapIndexInClass] using hg

omit [IsTopologicalGroup G] in
/--
The finite-stage index type is nonempty for a continuous homomorphism: take the pullback of the
terminal completed group-algebra target stage.
-/
theorem nonempty_zcCompletedDifferentialModuleIndex
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψc : ContinuousMonoidHom G H) :
    Nonempty (ZCCompletedDifferentialModuleIndex C ψc.toMonoidHom) :=
  ⟨zcCompletedDifferentialModuleComapIndex C hC ψc
    (ProCIntegerIndex.terminal (C := C) inferInstance,
      zcCompletedGroupAlgebraTopIndex C H)⟩

omit [IsTopologicalGroup G] in
/--
The compatible finite source/target/coefficient stages are directed for a continuous
homomorphism, provided the finite quotient class is closed under the usual formation and
hereditary operations.
-/
theorem directed_zcCompletedDifferentialModuleIndex
    (hForm : ProCGroups.FiniteGroupClass.Formation C)
    (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψc : ContinuousMonoidHom G H) :
    Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψc.toMonoidHom →
        ZCCompletedDifferentialModuleIndex C ψc.toMonoidHom) := by
  intro i j
  rcases ProCIntegerIndex.directed_of_formation hForm i.target.1 j.target.1 with
    ⟨n, hin, hjn⟩
  rcases directed_openNormalSubgroupInClass
      (C := C) (G := H) hForm i.target.2 j.target.2 with
    ⟨U, hiU, hjU⟩
  let target : ZCCompletedGroupAlgebraIndex C H := (n, U)
  let comapSource : OpenNormalSubgroupInClass C G :=
    OrderDual.ofDual
      (completedGroupAlgebraComapIndexInClass
        (G := G) (H := H) C hHer ψc U)
  let sourceIJ : OpenNormalSubgroupInClass C G :=
    ⟨i.source.1 ⊓ j.source.1,
      ProCGroups.FiniteGroupClass.Formation.quotient_inf_mem
        (C := C) (G := G) hForm i.source.1 j.source.1 i.source.2 j.source.2⟩
  let source : OpenNormalSubgroupInClass C G :=
    ⟨sourceIJ.1 ⊓ comapSource.1,
      ProCGroups.FiniteGroupClass.Formation.quotient_inf_mem
        (C := C) (G := G) hForm sourceIJ.1 comapSource.1 sourceIJ.2 comapSource.2⟩
  let k : ZCCompletedDifferentialModuleIndex C ψc.toMonoidHom :=
    { source := source
      target := target
      compatible := by
        intro g hg
        have hgcomap : g ∈ (comapSource.1 : Subgroup G) := hg.2
        change ψc.toMonoidHom g ∈
          ((((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H))
        simpa [comapSource, completedGroupAlgebraComapIndexInClass] using hgcomap }
  refine ⟨k, ?_, ?_⟩
  · constructor
    · intro g hg
      exact hg.1.1
    · exact ⟨hin, hiU⟩
  · constructor
    · intro g hg
      exact hg.1.2
    · exact ⟨hjn, hjU⟩

/-- The source quotient \(G/V\) at one finite differential-module stage. -/
abbrev zcCompletedDifferentialModuleStageSource
    (i : ZCCompletedDifferentialModuleIndex C ψ) : Type u :=
  G ⧸ (i.source.1 : Subgroup G)

/-- The target finite quotient \(H/U\) underlying the group-algebra stage. -/
abbrev zcCompletedDifferentialModuleStageTarget
    (i : ZCCompletedDifferentialModuleIndex C ψ) : Type u :=
  CompletedGroupAlgebraQuotientInClass H C i.target.2

/--
The finite coefficient ring \((\mathbb{Z}/n\mathbb{Z})[H/U]\) acting on one finite
differential-module stage.
-/
abbrev zcCompletedDifferentialModuleStageRing
    (i : ZCCompletedDifferentialModuleIndex C ψ) : Type u :=
  ZCCompletedGroupAlgebraStage C H i.target

/-- The target map \(G/V \to H/U\) induced by \(\psi\) at a compatible finite stage. -/
def zcCompletedDifferentialModuleStagePsi
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    zcCompletedDifferentialModuleStageSource C ψ i →*
      zcCompletedDifferentialModuleStageTarget C ψ i :=
  QuotientGroup.map
    (N := (i.source.1 : Subgroup G))
    (M := ((OrderDual.ofDual i.target.2).1 : Subgroup H))
    ψ i.compatible

/-- The stage coefficient homomorphism \(G/V \to (\mathbb{Z}/n\mathbb{Z})[H/U]\). -/
def zcCompletedDifferentialModuleStageScalar
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    zcCompletedDifferentialModuleStageSource C ψ i →*
      zcCompletedDifferentialModuleStageRing C ψ i :=
  (MonoidAlgebra.of (ModNCompletedCoeff i.target.1.modulus)
    (zcCompletedDifferentialModuleStageTarget C ψ i)).comp
      (zcCompletedDifferentialModuleStagePsi C ψ i)

/-- The finite crossed-differential module at one source/target/coefficient stage. -/
abbrev ZCCompletedDifferentialModuleStage
    (i : ZCCompletedDifferentialModuleIndex C ψ) : Type u :=
  CrossedDifferentialModule (zcCompletedDifferentialModuleStageScalar C ψ i)

/-- Finite completed differential-module stages carry the discrete topology. -/
instance instTopologicalSpaceZCCompletedDifferentialModuleStage
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    TopologicalSpace (ZCCompletedDifferentialModuleStage C ψ i) :=
  ⊥

/-- Finite completed differential-module stages carry the discrete topology. -/
instance instDiscreteTopologyZCCompletedDifferentialModuleStage
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    DiscreteTopology (ZCCompletedDifferentialModuleStage C ψ i) :=
  ⟨rfl⟩

/-- Finite completed differential-module stages are Hausdorff. -/
instance instT2SpaceZCCompletedDifferentialModuleStage
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    T2Space (ZCCompletedDifferentialModuleStage C ψ i) :=
  inferInstance

/-- Finite completed differential-module stages are topological additive groups. -/
instance instIsTopologicalAddGroupZCCompletedDifferentialModuleStage
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    IsTopologicalAddGroup (ZCCompletedDifferentialModuleStage C ψ i) :=
  inferInstance

/--
The completed differential-module stage is a module over the corresponding
\(\mathbb{Z}_C\)-completed group-algebra stage.
-/
instance instModuleZCCompletedGroupAlgebraZCCompletedDifferentialModuleStage
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    Module (ZCCompletedGroupAlgebra C H) (ZCCompletedDifferentialModuleStage C ψ i) :=
  Module.compHom _ (zcCompletedGroupAlgebraProjectionRingHom C H i.target)

/-- The quotient map from the source group into a finite differential-module stage source. -/
def zcCompletedDifferentialModuleStageSourceProj
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    G →* zcCompletedDifferentialModuleStageSource C ψ i :=
  QuotientGroup.mk' (i.source.1 : Subgroup G)

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/--
The finite-stage source projection is the quotient map by the source subgroup of the
differential-module stage.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageSourceProj_apply
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcCompletedDifferentialModuleStageSourceProj C ψ i g =
      QuotientGroup.mk' (i.source.1 : Subgroup G) g :=
  rfl

omit [IsTopologicalGroup G] in
/--
The finite-stage \(\psi\)-map for the \(\mathbb{Z}_C\)-completed differential module is the
coordinate map determined by the source projection.
-/
@[simp]
theorem zcCompletedDifferentialModuleStagePsi_mk
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcCompletedDifferentialModuleStagePsi C ψ i
        (QuotientGroup.mk' (i.source.1 : Subgroup G) g) =
      QuotientGroup.mk' ((OrderDual.ofDual i.target.2).1 : Subgroup H) (ψ g) :=
  rfl

omit [IsTopologicalGroup G] in
/--
The scalar structure on the \(\mathbb{Z}_C\)-completed differential-module stage is computed by
the finite-stage scalar action.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageScalar_mk
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcCompletedDifferentialModuleStageScalar C ψ i
        (QuotientGroup.mk' (i.source.1 : Subgroup G) g) =
      MonoidAlgebra.of (ModNCompletedCoeff i.target.1.modulus)
        (zcCompletedDifferentialModuleStageTarget C ψ i)
        (QuotientGroup.mk' ((OrderDual.ofDual i.target.2).1 : Subgroup H) (ψ g)) :=
  rfl

omit [IsTopologicalGroup G] in
/--
The finite-stage \(\psi\)-map for the \(\mathbb{Z}_C\)-completed differential module is the
coordinate map determined by the source projection.
-/
@[simp]
theorem zcCompletedDifferentialModuleStagePsi_coe
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcCompletedDifferentialModuleStagePsi C ψ i
        (QuotientGroup.mk g : zcCompletedDifferentialModuleStageSource C ψ i) =
      (QuotientGroup.mk (ψ g) : zcCompletedDifferentialModuleStageTarget C ψ i) :=
  rfl

omit [IsTopologicalGroup G] in
/--
The scalar structure on the \(\mathbb{Z}_C\)-completed differential-module stage is computed by
the finite-stage scalar action.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageScalar_coe
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcCompletedDifferentialModuleStageScalar C ψ i
        (QuotientGroup.mk g : zcCompletedDifferentialModuleStageSource C ψ i) =
      MonoidAlgebra.of (ModNCompletedCoeff i.target.1.modulus)
        (zcCompletedDifferentialModuleStageTarget C ψ i)
        (QuotientGroup.mk (ψ g) : zcCompletedDifferentialModuleStageTarget C ψ i) :=
  rfl

omit [IsTopologicalGroup G] in
/--
The finite-stage \(\psi\)-map for the \(\mathbb{Z}_C\)-completed differential module is the
coordinate map determined by the source projection.
-/
@[simp]
theorem zcCompletedDifferentialModuleStagePsi_sourceProj
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcCompletedDifferentialModuleStagePsi C ψ i
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g) =
      QuotientGroup.mk' ((OrderDual.ofDual i.target.2).1 : Subgroup H) (ψ g) := by
  simp only [zcCompletedDifferentialModuleStageSourceProj, QuotientGroup.mk'_apply,
  zcCompletedDifferentialModuleStagePsi_coe]
  rfl

omit [IsTopologicalGroup G] in
/--
The scalar structure on the \(\mathbb{Z}_C\)-completed differential-module stage is computed by
the finite-stage scalar action.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageScalar_sourceProj
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcCompletedDifferentialModuleStageScalar C ψ i
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g) =
      MonoidAlgebra.of (ModNCompletedCoeff i.target.1.modulus)
        (zcCompletedDifferentialModuleStageTarget C ψ i)
        (QuotientGroup.mk' ((OrderDual.ofDual i.target.2).1 : Subgroup H) (ψ g)) := by
  simp only [zcCompletedDifferentialModuleStageSourceProj, QuotientGroup.mk'_apply,
  zcCompletedDifferentialModuleStageScalar_coe]

/--
The source-identity finite stage attached to a \(\psi\)-stage. It has the same source quotient
and coefficient modulus, and its target quotient is the same source quotient.
-/
def zcCompletedDifferentialModuleIdentitySourceIndex
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    ZCCompletedDifferentialModuleIndex C (MonoidHom.id G) where
  source := i.source
  target := (i.target.1, OrderDual.toDual i.source)
  compatible := by
    intro g hg
    simpa using hg

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The identity-source index associated to `i` has the same source quotient as `i`. -/
@[simp]
theorem zcCompletedDifferentialModuleIdentitySourceIndex_source
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i).source = i.source :=
  rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The identity-source index associated to `i` retains the coefficient component of `i.target`. -/
@[simp]
theorem zcCompletedDifferentialModuleIdentitySourceIndex_target_fst
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i).target.1 = i.target.1 :=
  rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/--
At an identity-source index, the source projection for `MonoidHom.id G` agrees with the source
projection for `ψ`.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageSourceProj_identitySourceIndex
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcCompletedDifferentialModuleStageSourceProj C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i) g =
      zcCompletedDifferentialModuleStageSourceProj C ψ i g :=
  rfl

omit [IsTopologicalGroup H] in
/-- The identity-stage map fixes every element obtained from the original source projection. -/
@[simp]
theorem zcCompletedDifferentialModuleStagePsi_identitySourceIndex_sourceProj
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcCompletedDifferentialModuleStagePsi C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i)
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g) =
      zcCompletedDifferentialModuleStageSourceProj C ψ i g :=
  rfl

omit [IsTopologicalGroup H] in
/--
At the identity-source index, the scalar attached to a projected source element is the corresponding
group-like basis element.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageScalar_identitySourceIndex_sourceProj
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i)
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g) =
      MonoidAlgebra.of (ModNCompletedCoeff i.target.1.modulus)
        (zcCompletedDifferentialModuleStageSource C ψ i)
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g) :=
  rfl

/--
The finite group-algebra map from the source-identity stage attached to \(i\) to the
\(\psi\)-stage \(i\), induced by the finite target map \(G/V \to H/U\).
-/
def zcCompletedDifferentialModuleIdentitySourceStageRingHom
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    RingHom
      (zcCompletedDifferentialModuleStageRing C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i))
      (zcCompletedDifferentialModuleStageRing C ψ i) :=
  MonoidAlgebra.mapDomainRingHom (ModNCompletedCoeff i.target.1.modulus)
    (zcCompletedDifferentialModuleStagePsi C ψ i)

/--
The identity-source stage ring homomorphism sends the identity-stage scalar of `q` to the scalar of
`q` at the original stage.
-/
@[simp]
theorem zcCompletedDifferentialModuleIdentitySourceStageRingHom_stageScalar
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (q : zcCompletedDifferentialModuleStageSource C ψ i) :
    zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i
        (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G)
          (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i) q) =
      zcCompletedDifferentialModuleStageScalar C ψ i q := by
  refine QuotientGroup.induction_on q ?_
  intro g
  simp only [zcCompletedDifferentialModuleIdentitySourceStageRingHom,
    zcCompletedDifferentialModuleStageScalar, MonoidHom.coe_comp, Function.comp_apply,
    MonoidAlgebra.of_apply]
  change MonoidAlgebra.mapDomain (zcCompletedDifferentialModuleStagePsi C ψ i)
      (MonoidAlgebra.of (ModNCompletedCoeff i.target.1.modulus)
        (zcCompletedDifferentialModuleStageSource C ψ i)
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g)) =
    MonoidAlgebra.of (ModNCompletedCoeff i.target.1.modulus)
      (zcCompletedDifferentialModuleStageTarget C ψ i)
      (zcCompletedDifferentialModuleStagePsi C ψ i
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g))
  exact MonoidAlgebra.mapDomain_single

/-- The universal differential on a \(\psi\)-stage, bundled for the
source-identity stage scalars after restriction along the finite-stage ring
map. -/
def zcCompletedDifferentialModuleIdentitySourceStageToStageCrossedHom
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    letI : Module
        (zcCompletedDifferentialModuleStageRing C (MonoidHom.id G)
          (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i))
        (ZCCompletedDifferentialModuleStage C ψ i) :=
      Module.compHom _ (zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i)
    ScalarCrossedHom
      (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i))
      (ZCCompletedDifferentialModuleStage C ψ i) := by
  letI : Module
      (zcCompletedDifferentialModuleStageRing C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i))
      (ZCCompletedDifferentialModuleStage C ψ i) :=
    Module.compHom _ (zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i)
  exact
    { toFun := fun q =>
        universalCrossedDifferential
          (zcCompletedDifferentialModuleStageScalar C ψ i) q
      map_mul' := by
        intro q r
        dsimp only [zcCompletedDifferentialModuleIdentitySourceIndex] at q r ⊢
        change
          universalCrossedDifferential
                (zcCompletedDifferentialModuleStageScalar C ψ i) (q * r) =
            universalCrossedDifferential
                (zcCompletedDifferentialModuleStageScalar C ψ i) q +
              zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G)
                (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i) q •
                universalCrossedDifferential
                  (zcCompletedDifferentialModuleStageScalar C ψ i) r
        rw [universalCrossedDifferential_mul]
        congr 1
        symm
        change
          zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i
              (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G)
                (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i) q) •
              universalCrossedDifferential
                (zcCompletedDifferentialModuleStageScalar C ψ i) r =
            zcCompletedDifferentialModuleStageScalar C ψ i q •
              universalCrossedDifferential
                (zcCompletedDifferentialModuleStageScalar C ψ i) r
        rw [zcCompletedDifferentialModuleIdentitySourceStageRingHom_stageScalar] }

/--
The finite-stage comparison from the source-identity stage attached to i to the \(\psi\)-stage
i, sending d q to d q.
-/
def zcCompletedDifferentialModuleIdentitySourceStageToStage
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    letI : Module
        (zcCompletedDifferentialModuleStageRing C (MonoidHom.id G)
          (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i))
        (ZCCompletedDifferentialModuleStage C ψ i) :=
      Module.compHom _ (zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i)
    ZCCompletedDifferentialModuleStage C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i) →ₗ[
      zcCompletedDifferentialModuleStageRing C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i)]
      ZCCompletedDifferentialModuleStage C ψ i := by
  letI : Module
      (zcCompletedDifferentialModuleStageRing C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i))
      (ZCCompletedDifferentialModuleStage C ψ i) :=
    Module.compHom _ (zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i)
  exact crossedHomModuleLift
    (A := ZCCompletedDifferentialModuleStage C ψ i)
    (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G)
      (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i))
    (zcCompletedDifferentialModuleIdentitySourceStageToStageCrossedHom C ψ i)

/--
The comparison from the identity-source stage carries the universal crossed differential of `q` to
the universal crossed differential at the original stage.
-/
@[simp]
theorem zcCompletedDifferentialModuleIdentitySourceStageToStage_universal
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (q : zcCompletedDifferentialModuleStageSource C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i)) :
    zcCompletedDifferentialModuleIdentitySourceStageToStage C ψ i
        (universalCrossedDifferential
          (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G)
            (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i)) q) =
      universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ i) q := by
  let : Module
      (zcCompletedDifferentialModuleStageRing C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i))
      (ZCCompletedDifferentialModuleStage C ψ i) :=
    Module.compHom _ (zcCompletedDifferentialModuleIdentitySourceStageRingHom C ψ i)
  exact
    crossedHomModuleLift_universal
      (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i))
      (zcCompletedDifferentialModuleIdentitySourceStageToStageCrossedHom C ψ i) q

omit [IsTopologicalGroup G] in
/--
Finite-stage scalar multiplication agrees with first projecting the completed group-algebra
scalar and the completed differential-module element.
-/
@[simp]
theorem zcCompletedDifferentialModuleStage_completed_smul
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (a : ZCCompletedGroupAlgebra C H)
    (m : ZCCompletedDifferentialModuleStage C ψ i) :
    a • m =
      zcCompletedGroupAlgebraProjectionRingHom C H i.target a • m :=
  rfl

omit [IsTopologicalGroup G] in
/--
Group-like completed scalars act at a finite stage through the corresponding projected
target-group basis element.
-/
@[simp]
theorem zcCompletedDifferentialModuleStage_completed_groupLike_smul
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G)
    (m : ZCCompletedDifferentialModuleStage C ψ i) :
    zcCompletedGroupAlgebraScalar C ψ g • m =
      zcCompletedDifferentialModuleStageScalar C ψ i
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g) • m := by
  rw [zcCompletedDifferentialModuleStage_completed_smul]
  simp only [zcCompletedGroupAlgebraScalar, MonoidHom.coe_comp, Function.comp_apply,
  zcCompletedGroupAlgebraProjectionRingHom_apply, zcCompletedGroupAlgebraProjection_groupLike,
  zcCompletedDifferentialModuleStageSourceProj_apply, QuotientGroup.mk'_apply,
  zcCompletedDifferentialModuleStageScalar_coe]

/-- The finite-stage universal differential, with scalars restricted from the
completed group algebra. -/
def zcCompletedDifferentialModuleStageDifferential
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    ScalarCrossedHom (zcCompletedGroupAlgebraScalar C ψ)
      (ZCCompletedDifferentialModuleStage C ψ i) where
  toFun g :=
    universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ i)
      (zcCompletedDifferentialModuleStageSourceProj C ψ i g)
  map_mul' := by
    intro g h
    change
      universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ i)
          (zcCompletedDifferentialModuleStageSourceProj C ψ i (g * h)) =
        universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ i)
            (zcCompletedDifferentialModuleStageSourceProj C ψ i g) +
          zcCompletedGroupAlgebraScalar C ψ g •
            universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ i)
              (zcCompletedDifferentialModuleStageSourceProj C ψ i h)
    rw [map_mul, universalCrossedDifferential_mul,
      zcCompletedDifferentialModuleStage_completed_groupLike_smul]

omit [IsTopologicalGroup G] in
/-- The finite-stage completed differential sends the identity element to zero. -/
@[simp]
theorem zcCompletedDifferentialModuleStageDifferential_one
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    zcCompletedDifferentialModuleStageDifferential C ψ i (1 : G) = 0 :=
  ScalarCrossedHom.map_one (zcCompletedDifferentialModuleStageDifferential C ψ i)

/-- Boundary map from a finite differential-module stage to its coefficient group algebra stage. -/
def zcCompletedDifferentialModuleStageBoundary
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    ZCCompletedDifferentialModuleStage C ψ i →ₗ[zcCompletedDifferentialModuleStageRing C ψ i]
      zcCompletedDifferentialModuleStageRing C ψ i :=
  crossedHomModuleLift
    (A := zcCompletedDifferentialModuleStageRing C ψ i)
    (zcCompletedDifferentialModuleStageScalar C ψ i)
    (coefficientFoxBoundaryCrossedHom
      (zcCompletedDifferentialModuleStageScalar C ψ i))

omit [IsTopologicalGroup G] in
/--
The \(\mathbb{Z}_C\)-completed differential-module boundary is the finite-stage boundary
obtained from the source and target coordinates.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageBoundary_differential
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcCompletedDifferentialModuleStageBoundary C ψ i
        (zcCompletedDifferentialModuleStageDifferential C ψ i g) =
      zcCompletedDifferentialModuleStageScalar C ψ i
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g) - 1 := by
  change
    crossedHomModuleLift
        (zcCompletedDifferentialModuleStageScalar C ψ i)
        (coefficientFoxBoundaryCrossedHom
          (zcCompletedDifferentialModuleStageScalar C ψ i))
        (universalCrossedDifferential
          (zcCompletedDifferentialModuleStageScalar C ψ i)
          (zcCompletedDifferentialModuleStageSourceProj C ψ i g)) =
      zcCompletedDifferentialModuleStageScalar C ψ i
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g) - 1
  rw [crossedHomModuleLift_universal, coefficientFoxBoundaryCrossedHom_apply]

/--
The finite-stage boundary as a completed-ring-linear map, using restriction of scalars through
the coefficient stage projection.
-/
def zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    ZCCompletedDifferentialModuleStage C ψ i →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedGroupAlgebraStage C H i.target where
  toFun := zcCompletedDifferentialModuleStageBoundary C ψ i
  map_add' x y := by
    exact map_add (zcCompletedDifferentialModuleStageBoundary C ψ i) x y
  map_smul' r x := by
    change zcCompletedDifferentialModuleStageBoundary C ψ i
        (zcCompletedGroupAlgebraProjectionRingHom C H i.target r • x) =
      zcCompletedGroupAlgebraProjectionRingHom C H i.target r •
        zcCompletedDifferentialModuleStageBoundary C ψ i x
    exact map_smul (zcCompletedDifferentialModuleStageBoundary C ψ i)
      (zcCompletedGroupAlgebraProjectionRingHom C H i.target r) x

omit [IsTopologicalGroup G] in
/--
The completed Fox boundary linear map is evaluated by applying the finite-stage boundary formula
to each coordinate.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap_apply
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (x : ZCCompletedDifferentialModuleStage C ψ i) :
    zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap C ψ i x =
      zcCompletedDifferentialModuleStageBoundary C ψ i x :=
  rfl

/--
The projection from the algebraic completed module to a finite source/target/coefficient stage.
-/
def zcCompletedDifferentialModuleStageProjection
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    ZCCompletedDifferentialModule C ψ →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedDifferentialModuleStage C ψ i :=
  crossedHomModuleLift
    (A := ZCCompletedDifferentialModuleStage C ψ i)
    (zcCompletedGroupAlgebraScalar C ψ)
    (zcCompletedDifferentialModuleStageDifferential C ψ i)

omit [IsTopologicalGroup G] in
/--
The finite-stage projection sends the universal differential to the corresponding finite-stage
differential.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageProjection_universal
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcCompletedDifferentialModuleStageProjection C ψ i
        (zcUniversalDifferential C ψ g) =
      zcCompletedDifferentialModuleStageDifferential C ψ i g :=
  crossedHomModuleLift_universal
    (A := ZCCompletedDifferentialModuleStage C ψ i)
    (zcCompletedGroupAlgebraScalar C ψ)
    (zcCompletedDifferentialModuleStageDifferential C ψ i) g

/--
The identity-source comparison carries the projected universal differential of `g` to its projection
at the original stage.
-/
@[simp]
theorem zcDiffModuleIdentitySourceStageToStage_stageProj_universal
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g : G) :
    zcCompletedDifferentialModuleIdentitySourceStageToStage C ψ i
        (zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G)
          (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i)
          (zcUniversalDifferential C (MonoidHom.id G) g)) =
      zcCompletedDifferentialModuleStageProjection C ψ i
        (zcUniversalDifferential C ψ g) := by
  rw [zcCompletedDifferentialModuleStageProjection_universal,
    zcCompletedDifferentialModuleStageProjection_universal]
  change
    zcCompletedDifferentialModuleIdentitySourceStageToStage C ψ i
        (universalCrossedDifferential
          (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G)
            (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i))
          (zcCompletedDifferentialModuleStageSourceProj C (MonoidHom.id G)
            (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i) g)) =
      universalCrossedDifferential
        (zcCompletedDifferentialModuleStageScalar C ψ i)
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g)
  rw [zcCompletedDifferentialModuleIdentitySourceStageToStage_universal,
    zcCompletedDifferentialModuleStageSourceProj_identitySourceIndex]

omit [IsTopologicalGroup G] in
/-- The finite-stage projection evaluated on a representative of the universal quotient module. -/
theorem zcCompletedDifferentialModuleStageProjection_mkQ
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :
    zcCompletedDifferentialModuleStageProjection C ψ i
        ((crossedDifferentialRelationSubmodule
          (zcCompletedGroupAlgebraScalar C ψ)).mkQ x) =
      crossedDifferentialModuleLiftLinear
        (R := ZCCompletedGroupAlgebra C H)
        (zcCompletedDifferentialModuleStageDifferential C ψ i) x := by
  exact crossedHomModuleLift_mkQ
    (A := ZCCompletedDifferentialModuleStage C ψ i)
    (zcCompletedGroupAlgebraScalar C ψ)
    (zcCompletedDifferentialModuleStageDifferential C ψ i) x

/--
The pre-module map obtained by reducing coefficients to a finite target stage and source
generators to the corresponding finite source quotient.
-/
def zcCompletedDifferentialModulePreStageMap
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G →ₗ[ZCCompletedGroupAlgebra C H]
      CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ i)
        (zcCompletedDifferentialModuleStageSource C ψ i) :=
  (Finsupp.lmapDomain
      (zcCompletedDifferentialModuleStageRing C ψ i)
      (ZCCompletedGroupAlgebra C H)
      (zcCompletedDifferentialModuleStageSourceProj C ψ i)).comp
    (Finsupp.mapRange.linearMap
      (α := G) (zcCompletedGroupAlgebraProjectionLinearMap C H i.target))

omit [IsTopologicalGroup G] in
/--
The finite pre-stage map evaluates a basis differential by the corresponding finite-stage source
and target coordinates.
-/
@[simp]
theorem zcCompletedDifferentialModulePreStageMap_single
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (g : G) (a : ZCCompletedGroupAlgebra C H) :
    zcCompletedDifferentialModulePreStageMap C ψ i (Finsupp.single g a) =
      Finsupp.single (zcCompletedDifferentialModuleStageSourceProj C ψ i g)
        (zcCompletedGroupAlgebraProjection C H i.target a) := by
  simp only [zcCompletedDifferentialModulePreStageMap, LinearMap.coe_comp, Function.comp_apply,
  Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
      zcCompletedGroupAlgebraProjectionLinearMap_apply,
  Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
      zcCompletedDifferentialModuleStageSourceProj_apply,
  QuotientGroup.mk'_apply]

omit [IsTopologicalGroup G] in
/--
The explicit finite pre-stage map carries completed crossed-differential relation generators to
the corresponding finite relation generators.
-/
theorem zcCompletedDifferentialModulePreStageMap_relationElement
    (i : ZCCompletedDifferentialModuleIndex C ψ) (g h : G) :
    zcCompletedDifferentialModulePreStageMap C ψ i
        (crossedDifferentialRelationElement (zcCompletedGroupAlgebraScalar C ψ) g h) =
      crossedDifferentialRelationElement
        (zcCompletedDifferentialModuleStageScalar C ψ i)
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g)
        (zcCompletedDifferentialModuleStageSourceProj C ψ i h) := by
  simp only [crossedDifferentialRelationElement, zcCompletedGroupAlgebraScalar, MonoidHom.coe_comp,
  Function.comp_apply, Finsupp.smul_single, smul_eq_mul, mul_one, map_sub,
  zcCompletedDifferentialModulePreStageMap_single,
      zcCompletedDifferentialModuleStageSourceProj_apply,
  QuotientGroup.mk'_apply, QuotientGroup.mk_mul, zcCompletedGroupAlgebraProjection_one, map_add,
  zcCompletedGroupAlgebraProjection_groupLike,
      zcCompletedDifferentialModuleStageScalar_coe]

omit [IsTopologicalGroup G] in
/--
Every finite crossed-differential relation is the reduction of a completed crossed-differential
relation.
-/
theorem zcCompletedDifferentialModulePreStageMap_relationSubmodule_surjective
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    {y : CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ i)
        (zcCompletedDifferentialModuleStageSource C ψ i)}
    (hy : y ∈ crossedDifferentialRelationSubmodule
        (zcCompletedDifferentialModuleStageScalar C ψ i)) :
    ∃ x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G,
      x ∈ crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) ∧
        zcCompletedDifferentialModulePreStageMap C ψ i x = y := by
  change y ∈ Submodule.span (zcCompletedDifferentialModuleStageRing C ψ i)
      (Set.range fun p :
        zcCompletedDifferentialModuleStageSource C ψ i ×
          zcCompletedDifferentialModuleStageSource C ψ i =>
        crossedDifferentialRelationElement
          (zcCompletedDifferentialModuleStageScalar C ψ i) p.1 p.2) at hy
  refine Submodule.span_induction (p := fun y _ =>
    ∃ x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G,
      x ∈ crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) ∧
        zcCompletedDifferentialModulePreStageMap C ψ i x = y) ?hgen ?hzero ?hadd ?hsmul hy
  · rintro y ⟨⟨q₁, q₂⟩, rfl⟩
    rcases QuotientGroup.mk'_surjective (i.source.1 : Subgroup G) q₁ with ⟨g₁, rfl⟩
    rcases QuotientGroup.mk'_surjective (i.source.1 : Subgroup G) q₂ with ⟨g₂, rfl⟩
    refine ⟨crossedDifferentialRelationElement
        (zcCompletedGroupAlgebraScalar C ψ) g₁ g₂,
      crossedDifferentialRelationElement_mem (zcCompletedGroupAlgebraScalar C ψ) g₁ g₂,
      ?_⟩
    simp only [zcCompletedDifferentialModulePreStageMap_relationElement,
  zcCompletedDifferentialModuleStageSourceProj, QuotientGroup.mk'_apply]
  · exact ⟨0, Submodule.zero_mem _, by simp only [zcCompletedDifferentialModulePreStageMap,
      LinearMap.coe_comp, Function.comp_apply,
  Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_zero, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_zero]⟩
  · intro y z hy hz hyLift hzLift
    rcases hyLift with ⟨x, hx, rfl⟩
    rcases hzLift with ⟨w, hw, rfl⟩
    exact ⟨x + w, Submodule.add_mem _ hx hw, by simp only [map_add]⟩
  · intro a y hy hyLift
    rcases hyLift with ⟨x, hx, rfl⟩
    rcases zcCompletedGroupAlgebraProjection_surjective C H i.target a with ⟨aLift, haLift⟩
    refine ⟨aLift • x, Submodule.smul_mem _ aLift hx, ?_⟩
    rw [map_smul]
    change
      zcCompletedGroupAlgebraProjection C H i.target aLift •
          zcCompletedDifferentialModulePreStageMap C ψ i x =
        a • zcCompletedDifferentialModulePreStageMap C ψ i x
    rw [haLift]

omit [IsTopologicalGroup G] in
/--
The finite-stage lift from the completed pre-module is obtained by applying the quotient map
after the explicit source-and-coefficient finite-stage pre-map.
-/
theorem zcCompletedDifferentialModulePreStageMap_mkQ
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :
    (crossedDifferentialRelationSubmodule
      (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
        (zcCompletedDifferentialModulePreStageMap C ψ i x) =
      crossedDifferentialModuleLiftLinear
        (R := ZCCompletedGroupAlgebra C H)
        (zcCompletedDifferentialModuleStageDifferential C ψ i) x := by
  refine Finsupp.induction_linear x ?zero ?add ?single
  · simp only [zcCompletedDifferentialModulePreStageMap, crossedDifferentialModuleLiftLinear,
      map_zero]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro g a
    rw [zcCompletedDifferentialModulePreStageMap_single]
    rw [crossedDifferentialModuleLiftLinear_single]
    change
      (crossedDifferentialRelationSubmodule
        (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
          (Finsupp.single (zcCompletedDifferentialModuleStageSourceProj C ψ i g)
            (zcCompletedGroupAlgebraProjection C H i.target a)) =
        a • universalCrossedDifferential
          (zcCompletedDifferentialModuleStageScalar C ψ i)
          (zcCompletedDifferentialModuleStageSourceProj C ψ i g)
    rw [← Finsupp.smul_single_one]
    change
      (crossedDifferentialRelationSubmodule
        (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
          (zcCompletedGroupAlgebraProjectionRingHom C H i.target a •
            Finsupp.single (zcCompletedDifferentialModuleStageSourceProj C ψ i g) 1) =
        zcCompletedGroupAlgebraProjectionRingHom C H i.target a •
          universalCrossedDifferential
            (zcCompletedDifferentialModuleStageScalar C ψ i)
            (zcCompletedDifferentialModuleStageSourceProj C ψ i g)
    change
      Submodule.Quotient.mk
          (zcCompletedGroupAlgebraProjectionRingHom C H i.target a •
            Finsupp.single (zcCompletedDifferentialModuleStageSourceProj C ψ i g) 1) =
        zcCompletedGroupAlgebraProjectionRingHom C H i.target a •
          Submodule.Quotient.mk
            (Finsupp.single (zcCompletedDifferentialModuleStageSourceProj C ψ i g) 1)
    exact
      Submodule.Quotient.mk_smul
        (p := crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i))
        (r := zcCompletedGroupAlgebraProjectionRingHom C H i.target a)
        (x := Finsupp.single (zcCompletedDifferentialModuleStageSourceProj C ψ i g) 1)

omit [IsTopologicalGroup G] in
/--
Applying the completed boundary and then projecting to a finite coefficient stage agrees with
first projecting \(A_{\psi}(C)\) to the corresponding finite crossed-differential stage and then
taking the finite-stage boundary.
-/
theorem zcDiffModuleStageBoundaryCompletedLinearMap_comp_stageProj
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    (zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap C ψ i).comp
        (zcCompletedDifferentialModuleStageProjection C ψ i) =
      (zcCompletedGroupAlgebraProjectionLinearMap C H i.target).comp
        (zcToCompletedGroupAlgebra C ψ) := by
  apply crossedDifferentialModuleHom_ext
    (zcCompletedGroupAlgebraScalar C ψ)
  intro g
  change
    zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap C ψ i
        (zcCompletedDifferentialModuleStageProjection C ψ i
          (zcUniversalDifferential C ψ g)) =
      zcCompletedGroupAlgebraProjectionLinearMap C H i.target
        (zcToCompletedGroupAlgebra C ψ (zcUniversalDifferential C ψ g))
  rw [zcCompletedDifferentialModuleStageProjection_universal,
    zcCompletedDifferentialModuleStageBoundaryCompletedLinearMap_apply,
    zcCompletedDifferentialModuleStageBoundary_differential,
    zcToCompletedGroupAlgebra_universal,
    zcCompletedGroupAlgebraProjectionLinearMap_apply]
  change
    zcCompletedDifferentialModuleStageScalar C ψ i
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g) - 1 =
      zcCompletedGroupAlgebraProjection C H i.target
        (zcGroupLike C H (ψ g) - 1)
  rw [
    zcCompletedGroupAlgebraProjection_sub,
    zcCompletedGroupAlgebraProjection_groupLike,
    zcCompletedGroupAlgebraProjection_one,
    zcCompletedDifferentialModuleStageScalar_sourceProj]
  simp only [QuotientGroup.mk'_apply]

omit [IsTopologicalGroup H] in
/--
At a source-identity finite stage, vanishing finite boundary forces vanishing in the finite
crossed-differential stage.
-/
theorem zcDiffModuleIdentitySourceStageProj_eq_zero_of_boundary_eq_zero
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (x : ZCCompletedDifferentialModule C (MonoidHom.id G))
    (hx :
      zcCompletedDifferentialModuleStageBoundary C (MonoidHom.id G)
          (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i)
          (zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G)
            (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i) x) = 0) :
    zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i) x = 0 := by
  let j := zcCompletedDifferentialModuleIdentitySourceIndex C ψ i
  have hscalar :
      zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G) j =
        MonoidAlgebra.of (ModNCompletedCoeff j.target.1.modulus)
          (zcCompletedDifferentialModuleStageSource C (MonoidHom.id G) j) := by
    apply MonoidHom.ext
    intro q
    refine QuotientGroup.induction_on q ?_
    intro g
    rfl
  refine Submodule.Quotient.induction_on
    (p := crossedDifferentialRelationSubmodule
      (zcCompletedGroupAlgebraScalar C (MonoidHom.id G)))
    (C := fun x =>
      zcCompletedDifferentialModuleStageBoundary C (MonoidHom.id G) j
        (zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G) j x) = 0 →
      zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G) j x = 0)
    x ?_ hx
  intro y hy
  have hproj :
      zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G) j
          ((crossedDifferentialRelationSubmodule
            (zcCompletedGroupAlgebraScalar C (MonoidHom.id G))).mkQ y) =
        (crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G) j)).mkQ
            (zcCompletedDifferentialModulePreStageMap C (MonoidHom.id G) j y) := by
    simpa [zcCompletedDifferentialModuleStageProjection, crossedHomModuleLift] using
      (zcCompletedDifferentialModulePreStageMap_mkQ C (MonoidHom.id G) j y).symm
  change zcCompletedDifferentialModuleStageBoundary C (MonoidHom.id G) j
      (zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G) j
        ((crossedDifferentialRelationSubmodule
          (zcCompletedGroupAlgebraScalar C (MonoidHom.id G))).mkQ y)) = 0 at hy
  have hb0 :
      crossedDifferentialModuleLiftLinear
        (R := zcCompletedDifferentialModuleStageRing C (MonoidHom.id G) j)
        (fun q : zcCompletedDifferentialModuleStageSource C (MonoidHom.id G) j =>
          zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G) j q - 1)
        (zcCompletedDifferentialModulePreStageMap C (MonoidHom.id G) j y) = 0 := by
    rw [hproj] at hy
    change crossedHomModuleLift
        (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G) j)
        (coefficientFoxBoundaryCrossedHom
          (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G) j))
        ((crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G) j)).mkQ
          (zcCompletedDifferentialModulePreStageMap C (MonoidHom.id G) j y)) = 0 at hy
    rw [crossedHomModuleLift_mkQ] at hy
    exact hy
  have hmk :
      (monoidAlgebraToIdentityCrossedDifferentialModule
          (S := ModNCompletedCoeff j.target.1.modulus)
          (G := zcCompletedDifferentialModuleStageSource C (MonoidHom.id G) j))
          (crossedDifferentialModuleLiftLinear
            (R := MonoidAlgebra (ModNCompletedCoeff j.target.1.modulus)
              (zcCompletedDifferentialModuleStageSource C (MonoidHom.id G) j))
            (fun q : zcCompletedDifferentialModuleStageSource C (MonoidHom.id G) j =>
              MonoidAlgebra.of (ModNCompletedCoeff j.target.1.modulus)
                (zcCompletedDifferentialModuleStageSource C (MonoidHom.id G) j) q - 1)
            (zcCompletedDifferentialModulePreStageMap C (MonoidHom.id G) j y)) =
        (crossedDifferentialRelationSubmodule
          (MonoidAlgebra.of (ModNCompletedCoeff j.target.1.modulus)
            (zcCompletedDifferentialModuleStageSource C (MonoidHom.id G) j))).mkQ
          (zcCompletedDifferentialModulePreStageMap C (MonoidHom.id G) j y) := by
    exact
      monoidAlgebraToIdentityCrossedDifferentialModule_comp_identityBoundary_mkQ
        (S := ModNCompletedCoeff j.target.1.modulus)
        (G := zcCompletedDifferentialModuleStageSource C (MonoidHom.id G) j)
        (zcCompletedDifferentialModulePreStageMap C (MonoidHom.id G) j y)
  have hmk0 :
      (crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C (MonoidHom.id G) j)).mkQ
        (zcCompletedDifferentialModulePreStageMap C (MonoidHom.id G) j y) = 0 := by
    rw [hscalar]
    exact hmk.symm.trans (by
      rw [hscalar] at hb0
      exact (congrArg
        (monoidAlgebraToIdentityCrossedDifferentialModule
          (S := ModNCompletedCoeff j.target.1.modulus)
          (G := zcCompletedDifferentialModuleStageSource C (MonoidHom.id G) j)) hb0).trans
        (map_zero (monoidAlgebraToIdentityCrossedDifferentialModule
          (S := ModNCompletedCoeff j.target.1.modulus)
          (G := zcCompletedDifferentialModuleStageSource C (MonoidHom.id G) j))))
  change zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G) j
      ((crossedDifferentialRelationSubmodule
        (zcCompletedGroupAlgebraScalar C (MonoidHom.id G))).mkQ y) = 0
  rw [hproj, hmk0]

omit [IsTopologicalGroup H] in
/--
A zero source-identity completed Fox tail has zero projection to every source-identity finite
stage attached to a \(\psi\)-stage.
-/
theorem zcDiffModuleIdentitySourceStageProj_eq_zero_of_zcTo_eq_zero
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (x : ZCCompletedDifferentialModule C (MonoidHom.id G))
    (hx : zcToCompletedGroupAlgebra C (MonoidHom.id G) x = 0) :
    zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G)
        (zcCompletedDifferentialModuleIdentitySourceIndex C ψ i) x = 0 := by
  let j := zcCompletedDifferentialModuleIdentitySourceIndex C ψ i
  have hcomp := congrArg (fun f => f x)
    (zcDiffModuleStageBoundaryCompletedLinearMap_comp_stageProj
      C (MonoidHom.id G) j)
  have hb :
      zcCompletedDifferentialModuleStageBoundary C (MonoidHom.id G) j
          (zcCompletedDifferentialModuleStageProjection C (MonoidHom.id G) j x) = 0 := by
    simpa [LinearMap.comp_apply, hx] using hcomp
  exact
    zcDiffModuleIdentitySourceStageProj_eq_zero_of_boundary_eq_zero
      C ψ i x hb

/-- The source transition \((G/V)_j\to (G/V)_i\) for \(i\leq j\). -/
def zcCompletedDifferentialModuleStageSourceTransition
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j) :
    zcCompletedDifferentialModuleStageSource C ψ j →*
      zcCompletedDifferentialModuleStageSource C ψ i :=
  OpenNormalSubgroupInClass.map (C := C) (G := G) hij.1

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/--
The source transition sends the quotient class of `g` at the finer stage to the quotient class of
`g` at the coarser stage.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageSourceTransition_coe
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j) (g : G) :
    zcCompletedDifferentialModuleStageSourceTransition C ψ hij
        (QuotientGroup.mk g : zcCompletedDifferentialModuleStageSource C ψ j) =
      (QuotientGroup.mk g : zcCompletedDifferentialModuleStageSource C ψ i) :=
  rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/--
The source transition carries `QuotientGroup.mk'` for the finer source subgroup to
`QuotientGroup.mk'` for the coarser source subgroup.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageSourceTransition_mk
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j) (g : G) :
    zcCompletedDifferentialModuleStageSourceTransition C ψ hij
        (QuotientGroup.mk' (j.source.1 : Subgroup G) g) =
      QuotientGroup.mk' (i.source.1 : Subgroup G) g :=
  rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Source projection commutes with the source transition between differential-module stages. -/
@[simp]
theorem zcCompletedDifferentialModuleStageSourceTransition_sourceProj
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j) (g : G) :
    zcCompletedDifferentialModuleStageSourceTransition C ψ hij
        (zcCompletedDifferentialModuleStageSourceProj C ψ j g) =
      zcCompletedDifferentialModuleStageSourceProj C ψ i g := by
  simp only [zcCompletedDifferentialModuleStageSourceProj, QuotientGroup.mk'_apply,
  zcCompletedDifferentialModuleStageSourceTransition_coe]

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The source transition attached to a reflexive refinement fixes every source-stage element. -/
@[simp]
theorem zcCompletedDifferentialModuleStageSourceTransition_id
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (x : zcCompletedDifferentialModuleStageSource C ψ i) :
    zcCompletedDifferentialModuleStageSourceTransition C ψ (le_rfl : i ≤ i) x = x := by
  rcases QuotientGroup.mk'_surjective (i.source.1 : Subgroup G) x with ⟨g, rfl⟩
  simp only [QuotientGroup.mk'_apply, zcCompletedDifferentialModuleStageSourceTransition_coe]

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Successive source transitions agree with the source transition for the composite refinement. -/
@[simp]
theorem zcCompletedDifferentialModuleStageSourceTransition_comp
    {i j k : ZCCompletedDifferentialModuleIndex C ψ}
    (hij : i ≤ j) (hjk : j ≤ k)
    (x : zcCompletedDifferentialModuleStageSource C ψ k) :
    zcCompletedDifferentialModuleStageSourceTransition C ψ hij
        (zcCompletedDifferentialModuleStageSourceTransition C ψ hjk x) =
      zcCompletedDifferentialModuleStageSourceTransition C ψ (hij.trans hjk) x := by
  rcases QuotientGroup.mk'_surjective (k.source.1 : Subgroup G) x with ⟨g, rfl⟩
  simp only [QuotientGroup.mk'_apply, zcCompletedDifferentialModuleStageSourceTransition_coe]

/-- The target transition \(H/U_j \to H/U_i\) underlying the coefficient transition. -/
def zcCompletedDifferentialModuleStageTargetTransition
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j) :
    zcCompletedDifferentialModuleStageTarget C ψ j →*
      zcCompletedDifferentialModuleStageTarget C ψ i :=
  OpenNormalSubgroupInClass.map (C := C) (G := H)
    (U := OrderDual.ofDual i.target.2) (V := OrderDual.ofDual j.target.2) hij.2.2

omit [IsTopologicalGroup G] in
/--
The target transition sends the quotient class of `h` at the finer stage to its class at the coarser
stage.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageTargetTransition_coe
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j) (h : H) :
    zcCompletedDifferentialModuleStageTargetTransition C ψ hij
        (QuotientGroup.mk h : zcCompletedDifferentialModuleStageTarget C ψ j) =
      (QuotientGroup.mk h : zcCompletedDifferentialModuleStageTarget C ψ i) :=
  rfl

omit [IsTopologicalGroup G] in
/--
The target transition carries `QuotientGroup.mk'` for the finer target subgroup to
`QuotientGroup.mk'` for the coarser target subgroup.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageTargetTransition_mk
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j) (h : H) :
    zcCompletedDifferentialModuleStageTargetTransition C ψ hij
        (QuotientGroup.mk' ((OrderDual.ofDual j.target.2).1 : Subgroup H) h) =
      QuotientGroup.mk' ((OrderDual.ofDual i.target.2).1 : Subgroup H) h :=
  rfl

omit [IsTopologicalGroup G] in
/-- The target transition attached to a reflexive refinement fixes every target-stage element. -/
@[simp]
theorem zcCompletedDifferentialModuleStageTargetTransition_id
    (i : ZCCompletedDifferentialModuleIndex C ψ)
    (x : zcCompletedDifferentialModuleStageTarget C ψ i) :
    zcCompletedDifferentialModuleStageTargetTransition C ψ (le_rfl : i ≤ i) x = x := by
  rcases QuotientGroup.mk'_surjective ((OrderDual.ofDual i.target.2).1 : Subgroup H) x
    with ⟨h, rfl⟩
  simp only [QuotientGroup.mk'_apply, zcCompletedDifferentialModuleStageTargetTransition_coe]
  rfl

omit [IsTopologicalGroup G] in
/-- Successive target transitions agree with the target transition for the composite refinement. -/
@[simp]
theorem zcCompletedDifferentialModuleStageTargetTransition_comp
    {i j k : ZCCompletedDifferentialModuleIndex C ψ}
    (hij : i ≤ j) (hjk : j ≤ k)
    (x : zcCompletedDifferentialModuleStageTarget C ψ k) :
    zcCompletedDifferentialModuleStageTargetTransition C ψ hij
        (zcCompletedDifferentialModuleStageTargetTransition C ψ hjk x) =
      zcCompletedDifferentialModuleStageTargetTransition C ψ (hij.trans hjk) x := by
  rcases QuotientGroup.mk'_surjective ((OrderDual.ofDual k.target.2).1 : Subgroup H) x
    with ⟨h, rfl⟩
  simp only [QuotientGroup.mk'_apply, zcCompletedDifferentialModuleStageTargetTransition_coe]
  rfl

omit [IsTopologicalGroup G] in
/-- The source-to-target stage map commutes with the source and target transition maps. -/
@[simp]
theorem zcCompletedDifferentialModuleStagePsi_transition
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j)
    (x : zcCompletedDifferentialModuleStageSource C ψ j) :
    zcCompletedDifferentialModuleStageTargetTransition C ψ hij
        (zcCompletedDifferentialModuleStagePsi C ψ j x) =
      zcCompletedDifferentialModuleStagePsi C ψ i
        (zcCompletedDifferentialModuleStageSourceTransition C ψ hij x) := by
  rcases QuotientGroup.mk'_surjective (j.source.1 : Subgroup G) x with ⟨g, rfl⟩
  simp only [QuotientGroup.mk'_apply, zcCompletedDifferentialModuleStagePsi_coe,
  zcCompletedDifferentialModuleStageTargetTransition_coe,
      zcCompletedDifferentialModuleStageSourceTransition_coe]
  rfl

omit [IsTopologicalGroup G] in
/--
The group-algebra transition of a stage scalar equals the scalar of the transitioned source element.
-/
@[simp 900]
theorem zcCompletedDifferentialModuleStageScalar_transition
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j)
    (x : zcCompletedDifferentialModuleStageSource C ψ j) :
    zcCompletedGroupAlgebraTransition C H hij.2
        (zcCompletedDifferentialModuleStageScalar C ψ j x) =
      zcCompletedDifferentialModuleStageScalar C ψ i
        (zcCompletedDifferentialModuleStageSourceTransition C ψ hij x) := by
  rcases QuotientGroup.mk'_surjective (j.source.1 : Subgroup G) x with ⟨g, rfl⟩
  rw [zcCompletedDifferentialModuleStageScalar_mk]
  erw [zcCompletedGroupAlgebraTransition_of]
  change
    MonoidAlgebra.of (ModNCompletedCoeff i.target.1.modulus)
        (zcCompletedDifferentialModuleStageTarget C ψ i)
        (zcCompletedDifferentialModuleStageTargetTransition C ψ hij
          (zcCompletedDifferentialModuleStagePsi C ψ j
            (QuotientGroup.mk' (j.source.1 : Subgroup G) g))) =
      MonoidAlgebra.of (ModNCompletedCoeff i.target.1.modulus)
        (zcCompletedDifferentialModuleStageTarget C ψ i)
        (zcCompletedDifferentialModuleStagePsi C ψ i
        (zcCompletedDifferentialModuleStageSourceTransition C ψ hij
            (QuotientGroup.mk' (j.source.1 : Subgroup G) g)))
  rw [zcCompletedDifferentialModuleStagePsi_transition]

/--
Additive transition between the finite pre-modules before quotienting by the
crossed-differential relations.
-/
def zcCompletedDifferentialModulePreStageTransition
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j) :
    CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ j)
        (zcCompletedDifferentialModuleStageSource C ψ j) →+
      CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ i)
        (zcCompletedDifferentialModuleStageSource C ψ i) :=
  (Finsupp.lmapDomain
      (zcCompletedDifferentialModuleStageRing C ψ i) ℤ
      (zcCompletedDifferentialModuleStageSourceTransition C ψ hij)).toAddMonoidHom.comp
    (Finsupp.mapRange.addMonoidHom
      (zcCompletedGroupAlgebraTransition C H hij.2).toAddMonoidHom)

omit [IsTopologicalGroup G] in
/--
The finite-stage transition sends a singleton basis function to the singleton supported at its
image in the coarser quotient.
-/
@[simp]
theorem zcCompletedDifferentialModulePreStageTransition_single
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j)
    (q : zcCompletedDifferentialModuleStageSource C ψ j)
    (a : zcCompletedDifferentialModuleStageRing C ψ j) :
    zcCompletedDifferentialModulePreStageTransition C ψ hij (Finsupp.single q a) =
      Finsupp.single (zcCompletedDifferentialModuleStageSourceTransition C ψ hij q)
        (zcCompletedGroupAlgebraTransition C H hij.2 a) := by
  simp only [zcCompletedDifferentialModulePreStageTransition, Finsupp.mapRange.addMonoidHom,
  RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, AddMonoidHom.coe_comp,
      LinearMap.toAddMonoidHom_coe,
  AddMonoidHom.coe_mk, ZeroHom.coe_mk, Function.comp_apply, Finsupp.mapRange_single,
      Finsupp.lmapDomain_apply,
  Finsupp.mapDomain_single]

omit [IsTopologicalGroup G] in
/-- Completed-to-pre-stage reduction is compatible with finite-stage transitions. -/
theorem zcCompletedDifferentialModulePreStageTransition_preStageMap
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j)
    (x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G) :
    zcCompletedDifferentialModulePreStageTransition C ψ hij
        (zcCompletedDifferentialModulePreStageMap C ψ j x) =
      zcCompletedDifferentialModulePreStageMap C ψ i x := by
  refine Finsupp.induction_linear x ?zero ?add ?single
  · simp only [zcCompletedDifferentialModulePreStageTransition, RingHom.toAddMonoidHom_eq_coe,
  zcCompletedDifferentialModulePreStageMap, LinearMap.coe_comp, Function.comp_apply,
      Finsupp.mapRange.linearMap_apply,
  Finsupp.mapRange_zero, Finsupp.lmapDomain_apply, Finsupp.mapDomain_zero, AddMonoidHom.coe_comp,
  LinearMap.toAddMonoidHom_coe, Finsupp.mapRange.addMonoidHom_apply, AddMonoidHom.coe_coe]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro g a
    simp only [zcCompletedDifferentialModulePreStageMap_single,
  zcCompletedDifferentialModuleStageSourceProj_apply, QuotientGroup.mk'_apply,
  zcCompletedDifferentialModulePreStageTransition_single,
      zcCompletedDifferentialModuleStageSourceTransition_coe,
  zcCompletedGroupAlgebraTransition_projection]

omit [IsTopologicalGroup G] in
/-- The universal differential transported along a finite-stage refinement. -/
def zcCompletedDifferentialModuleStageTransitionCrossedHom
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j) :
    letI : Module (zcCompletedDifferentialModuleStageRing C ψ j)
        (ZCCompletedDifferentialModuleStage C ψ i) :=
      Module.compHom _ (zcCompletedGroupAlgebraTransition C H hij.2)
    ScalarCrossedHom (zcCompletedDifferentialModuleStageScalar C ψ j)
      (ZCCompletedDifferentialModuleStage C ψ i) := by
  letI : Module (zcCompletedDifferentialModuleStageRing C ψ j)
      (ZCCompletedDifferentialModuleStage C ψ i) :=
    Module.compHom _ (zcCompletedGroupAlgebraTransition C H hij.2)
  exact
    { toFun := fun x =>
        universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ i)
          (zcCompletedDifferentialModuleStageSourceTransition C ψ hij x)
      map_mul' := by
        intro x y
        change
          universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ i)
              (zcCompletedDifferentialModuleStageSourceTransition C ψ hij (x * y)) =
            universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ i)
                (zcCompletedDifferentialModuleStageSourceTransition C ψ hij x) +
              zcCompletedDifferentialModuleStageScalar C ψ j x •
                universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ i)
                  (zcCompletedDifferentialModuleStageSourceTransition C ψ hij y)
        rw [map_mul, universalCrossedDifferential_mul]
        congr 1
        change
          zcCompletedDifferentialModuleStageScalar C ψ i
              (zcCompletedDifferentialModuleStageSourceTransition C ψ hij x) •
              universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ i)
                (zcCompletedDifferentialModuleStageSourceTransition C ψ hij y) =
            zcCompletedGroupAlgebraTransition C H hij.2
              (zcCompletedDifferentialModuleStageScalar C ψ j x) •
              universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ i)
                (zcCompletedDifferentialModuleStageSourceTransition C ψ hij y)
        rw [zcCompletedDifferentialModuleStageScalar_transition] }

/--
The additive transition map from a finer completed differential-module stage to a coarser stage.
-/
def zcCompletedDifferentialModuleStageTransition
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j) :
    ZCCompletedDifferentialModuleStage C ψ j →+
      ZCCompletedDifferentialModuleStage C ψ i := by
  letI : Module (zcCompletedDifferentialModuleStageRing C ψ j)
      (ZCCompletedDifferentialModuleStage C ψ i) :=
    Module.compHom _ (zcCompletedGroupAlgebraTransition C H hij.2)
  exact
    (crossedHomModuleLift
      (A := ZCCompletedDifferentialModuleStage C ψ i)
      (zcCompletedDifferentialModuleStageScalar C ψ j)
      (zcCompletedDifferentialModuleStageTransitionCrossedHom C ψ hij)).toAddMonoidHom

omit [IsTopologicalGroup G] in
/--
The differential-module stage transition preserves the universal stage differential of each group
element.
-/
@[simp]
theorem zcCompletedDifferentialModuleStageTransition_universal
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j) (g : G) :
    zcCompletedDifferentialModuleStageTransition C ψ hij
        (zcCompletedDifferentialModuleStageDifferential C ψ j g) =
      zcCompletedDifferentialModuleStageDifferential C ψ i g := by
  let : Module (zcCompletedDifferentialModuleStageRing C ψ j)
      (ZCCompletedDifferentialModuleStage C ψ i) :=
    Module.compHom _ (zcCompletedGroupAlgebraTransition C H hij.2)
  change
    crossedHomModuleLift
        (zcCompletedDifferentialModuleStageScalar C ψ j)
        (zcCompletedDifferentialModuleStageTransitionCrossedHom C ψ hij)
        (universalCrossedDifferential
          (zcCompletedDifferentialModuleStageScalar C ψ j)
          (zcCompletedDifferentialModuleStageSourceProj C ψ j g)) =
      universalCrossedDifferential
        (zcCompletedDifferentialModuleStageScalar C ψ i)
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g)
  rw [crossedHomModuleLift_universal]
  change
    universalCrossedDifferential
        (zcCompletedDifferentialModuleStageScalar C ψ i)
        (zcCompletedDifferentialModuleStageSourceTransition C ψ hij
          (zcCompletedDifferentialModuleStageSourceProj C ψ j g)) =
      universalCrossedDifferential
        (zcCompletedDifferentialModuleStageScalar C ψ i)
        (zcCompletedDifferentialModuleStageSourceProj C ψ i g)
  rw [zcCompletedDifferentialModuleStageSourceTransition_sourceProj]

omit [IsTopologicalGroup G] in
/--
The finite pre-module transition descends to the quotient transition between finite
differential-module stages.
-/
theorem zcCompletedDifferentialModulePreStageTransition_mkQ
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j)
    (x : CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ j)
        (zcCompletedDifferentialModuleStageSource C ψ j)) :
    (crossedDifferentialRelationSubmodule
        (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
        (zcCompletedDifferentialModulePreStageTransition C ψ hij x) =
      zcCompletedDifferentialModuleStageTransition C ψ hij
        ((crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ j)).mkQ x) := by
  refine Finsupp.induction_linear x ?zero ?add ?single
  · simp only [zcCompletedDifferentialModulePreStageTransition, RingHom.toAddMonoidHom_eq_coe,
      zcCompletedDifferentialModuleStageTransition, map_zero]
  · intro x y hx hy
    simp only [map_add, hx, Submodule.mkQ_apply, hy]
  · intro q a
    rw [zcCompletedDifferentialModulePreStageTransition_single]
    have hleft :
        (Submodule.Quotient.mk
            (p := crossedDifferentialRelationSubmodule
              (zcCompletedDifferentialModuleStageScalar C ψ i))
            (Finsupp.single (zcCompletedDifferentialModuleStageSourceTransition C ψ hij q)
              (zcCompletedGroupAlgebraTransition C H hij.2 a)) :
          ZCCompletedDifferentialModuleStage C ψ i) =
          zcCompletedGroupAlgebraTransition C H hij.2 a •
            universalCrossedDifferential
              (zcCompletedDifferentialModuleStageScalar C ψ i)
              (zcCompletedDifferentialModuleStageSourceTransition C ψ hij q) := by
      rw [← Finsupp.smul_single_one]
      rfl
    have hright :
        ((crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ j)).mkQ
            (Finsupp.single q a) :
          ZCCompletedDifferentialModuleStage C ψ j) =
          a • universalCrossedDifferential
            (zcCompletedDifferentialModuleStageScalar C ψ j) q := by
      rw [← Finsupp.smul_single_one]
      rfl
    change
      (Submodule.Quotient.mk
          (p := crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψ i))
          (Finsupp.single (zcCompletedDifferentialModuleStageSourceTransition C ψ hij q)
            (zcCompletedGroupAlgebraTransition C H hij.2 a)) :
        ZCCompletedDifferentialModuleStage C ψ i) =
        zcCompletedDifferentialModuleStageTransition C ψ hij
          ((crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψ j)).mkQ
              (Finsupp.single q a))
    rw [hleft, hright]
    simp only [zcCompletedDifferentialModuleStageTransition, LinearMap.toAddMonoidHom_coe, map_smul,
  crossedHomModuleLift_universal]
    change
      zcCompletedGroupAlgebraTransition C H hij.2 a •
          universalCrossedDifferential
            (zcCompletedDifferentialModuleStageScalar C ψ i)
            (zcCompletedDifferentialModuleStageSourceTransition C ψ hij q) =
        zcCompletedGroupAlgebraTransition C H hij.2 a •
          universalCrossedDifferential
            (zcCompletedDifferentialModuleStageScalar C ψ i)
            (zcCompletedDifferentialModuleStageSourceTransition C ψ hij q)
    rfl

omit [IsTopologicalGroup G] in
/-- Finite pre-stage transitions preserve the crossed-differential relation submodules. -/
theorem zcCompletedDifferentialModulePreStageTransition_mem_relationSubmodule
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j)
    {x : CrossedDifferentialPreModule
        (zcCompletedDifferentialModuleStageRing C ψ j)
        (zcCompletedDifferentialModuleStageSource C ψ j)}
    (hx : x ∈ crossedDifferentialRelationSubmodule
        (zcCompletedDifferentialModuleStageScalar C ψ j)) :
    zcCompletedDifferentialModulePreStageTransition C ψ hij x ∈
      crossedDifferentialRelationSubmodule
        (zcCompletedDifferentialModuleStageScalar C ψ i) := by
  have hq :
      (crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ
          (zcCompletedDifferentialModulePreStageTransition C ψ hij x) = 0 := by
    rw [zcCompletedDifferentialModulePreStageTransition_mkQ]
    have hxq :
        (crossedDifferentialRelationSubmodule
            (zcCompletedDifferentialModuleStageScalar C ψ j)).mkQ x = 0 :=
      (Submodule.Quotient.mk_eq_zero
        (p := crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ j))
        (x := x)).2 hx
    rw [hxq]
    exact map_zero (zcCompletedDifferentialModuleStageTransition C ψ hij)
  exact
    (Submodule.Quotient.mk_eq_zero
      (p := crossedDifferentialRelationSubmodule
        (zcCompletedDifferentialModuleStageScalar C ψ i))
      (x := zcCompletedDifferentialModulePreStageTransition C ψ hij x)).1 hq

omit [IsTopologicalGroup G] in
/-- The pre-stage transition for a reflexive refinement is the identity additive homomorphism. -/
@[simp]
theorem zcCompletedDifferentialModulePreStageTransition_id
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    zcCompletedDifferentialModulePreStageTransition C ψ (le_rfl : i ≤ i) =
      AddMonoidHom.id
        (CrossedDifferentialPreModule
          (zcCompletedDifferentialModuleStageRing C ψ i)
          (zcCompletedDifferentialModuleStageSource C ψ i)) := by
  apply AddMonoidHom.ext
  intro x
  refine Finsupp.induction_linear x ?zero ?add ?single
  · simp only [zcCompletedDifferentialModulePreStageTransition,
      zcCompletedGroupAlgebraTransition_id,
  RingHom.toAddMonoidHom_eq_coe, RingHom.coe_addMonoidHom_id, Finsupp.mapRange.addMonoidHom_id,
      AddMonoidHom.comp_id,
  LinearMap.toAddMonoidHom_coe, Finsupp.lmapDomain_apply, Finsupp.mapDomain_zero,
      AddMonoidHom.id_apply]
  · intro x y hx hy
    simp only [map_add, hx, AddMonoidHom.id_apply, hy]
  · intro q a
    rw [zcCompletedDifferentialModulePreStageTransition_single]
    have hcoeff :
        zcCompletedGroupAlgebraTransition C H (le_rfl : i.target ≤ i.target) a = a := by
      exact congrFun
        (congrArg DFunLike.coe
          (zcCompletedGroupAlgebraTransition_id C H i.target)) a
    simp only [zcCompletedDifferentialModuleStageSourceTransition_id,
        zcCompletedGroupAlgebraTransition_id,
  RingHom.id_apply, AddMonoidHom.id_apply]

omit [IsTopologicalGroup G] in
/-- Pre-stage transitions compose according to transitivity of index refinement. -/
@[simp 900]
theorem zcCompletedDifferentialModulePreStageTransition_comp
    {i j k : ZCCompletedDifferentialModuleIndex C ψ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    (zcCompletedDifferentialModulePreStageTransition C ψ hij).comp
        (zcCompletedDifferentialModulePreStageTransition C ψ hjk) =
      zcCompletedDifferentialModulePreStageTransition C ψ (hij.trans hjk) := by
  apply AddMonoidHom.ext
  intro x
  refine Finsupp.induction_linear x ?zero ?add ?single
  · simp only [zcCompletedDifferentialModulePreStageTransition, RingHom.toAddMonoidHom_eq_coe,
  AddMonoidHom.coe_comp, LinearMap.toAddMonoidHom_coe, Function.comp_apply,
      Finsupp.mapRange.addMonoidHom_apply,
  AddMonoidHom.coe_coe, Finsupp.mapRange_zero, Finsupp.lmapDomain_apply, Finsupp.mapDomain_zero]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro q a
    simp only [AddMonoidHom.comp_apply]
    rw [zcCompletedDifferentialModulePreStageTransition_single,
      zcCompletedDifferentialModulePreStageTransition_single,
      zcCompletedDifferentialModulePreStageTransition_single]
    have hcoeff :
        zcCompletedGroupAlgebraTransition C H hij.2
            (zcCompletedGroupAlgebraTransition C H hjk.2 a) =
          zcCompletedGroupAlgebraTransition C H (hij.trans hjk).2 a := by
      exact congrFun
        (congrArg DFunLike.coe
          (zcCompletedGroupAlgebraTransition_comp C H hij.2 hjk.2)) a
    rw [hcoeff]
    simp only [zcCompletedDifferentialModuleStageSourceTransition_comp]

omit [IsTopologicalGroup G] in
/--
If a completed pre-module element has relation-valued reductions at every finite stage, then any
finite list of finite stages is matched by a single completed relation.
-/
theorem zcCompletedDifferentialModuleFiniteRelationReductions_finiteStageApproximation
    (hdir : Directed (· ≤ ·)
      (id : ZCCompletedDifferentialModuleIndex C ψ →
        ZCCompletedDifferentialModuleIndex C ψ))
    (s : Finset (ZCCompletedDifferentialModuleIndex C ψ))
    (x : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G)
    (hx : ∀ i : ZCCompletedDifferentialModuleIndex C ψ,
      zcCompletedDifferentialModulePreStageMap C ψ i x ∈
        crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i)) :
    ∃ r : CrossedDifferentialPreModule (ZCCompletedGroupAlgebra C H) G,
      r ∈ crossedDifferentialRelationSubmodule (zcCompletedGroupAlgebraScalar C ψ) ∧
        ∀ i ∈ s,
          zcCompletedDifferentialModulePreStageMap C ψ i r =
            zcCompletedDifferentialModulePreStageMap C ψ i x := by
  classical
  by_cases hs : s.Nonempty
  · rcases ProCGroups.InverseSystems.exists_upperBound_finset
        (I := ZCCompletedDifferentialModuleIndex C ψ) hdir s hs with
      ⟨k, hk⟩
    rcases zcCompletedDifferentialModulePreStageMap_relationSubmodule_surjective
        C ψ k (hx k) with
      ⟨r, hr, hrk⟩
    refine ⟨r, hr, ?_⟩
    intro i hi
    have hik : i ≤ k := hk i hi
    have hcompat :=
      congrArg (zcCompletedDifferentialModulePreStageTransition C ψ hik) hrk
    simpa [zcCompletedDifferentialModulePreStageTransition_preStageMap] using hcompat
  · refine ⟨0, Submodule.zero_mem _, ?_⟩
    intro i hi
    exact False.elim (hs ⟨i, hi⟩)

omit [IsTopologicalGroup G] in
/-- Transitioning a projected universal differential gives its projection at the coarser stage. -/
@[simp]
theorem zcCompletedDifferentialModuleStageTransition_comp_projection
    {i j : ZCCompletedDifferentialModuleIndex C ψ} (hij : i ≤ j) (g : G) :
    zcCompletedDifferentialModuleStageTransition C ψ hij
        (zcCompletedDifferentialModuleStageProjection C ψ j
          (zcUniversalDifferential C ψ g)) =
      zcCompletedDifferentialModuleStageProjection C ψ i
        (zcUniversalDifferential C ψ g) := by
  simp only [zcCompletedDifferentialModuleStageProjection_universal,
  zcCompletedDifferentialModuleStageTransition_universal]

omit [IsTopologicalGroup G] in
/--
The differential-module stage transition for a reflexive refinement is the identity additive
homomorphism.
-/
@[simp 900]
theorem zcCompletedDifferentialModuleStageTransition_id
    (i : ZCCompletedDifferentialModuleIndex C ψ) :
    zcCompletedDifferentialModuleStageTransition C ψ (le_rfl : i ≤ i) =
      AddMonoidHom.id (ZCCompletedDifferentialModuleStage C ψ i) := by
  apply AddMonoidHom.ext
  intro x
  refine Submodule.Quotient.induction_on
    (p := crossedDifferentialRelationSubmodule
      (zcCompletedDifferentialModuleStageScalar C ψ i)) x ?_
  intro z
  refine Finsupp.induction_linear z ?zero ?add ?single
  · simp only [zcCompletedDifferentialModuleStageTransition,
      Submodule.Quotient.mk_zero, map_zero]
  · intro x y hx hy
    simp only [Submodule.Quotient.mk_add, map_add, hx, AddMonoidHom.id_apply, hy]
  · intro q a
    change zcCompletedDifferentialModuleStageTransition C ψ (le_rfl : i ≤ i)
        ((crossedDifferentialRelationSubmodule
          (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ (Finsupp.single q a)) =
      (crossedDifferentialRelationSubmodule
        (zcCompletedDifferentialModuleStageScalar C ψ i)).mkQ (Finsupp.single q a)
    rw [← zcCompletedDifferentialModulePreStageTransition_mkQ C ψ
      (le_rfl : i ≤ i) (Finsupp.single q a)]
    simp only [zcCompletedDifferentialModulePreStageTransition_single,
      zcCompletedDifferentialModuleStageSourceTransition_id,
      zcCompletedGroupAlgebraTransition_id, RingHom.id_apply]

omit [IsTopologicalGroup G] in
/-- Differential-module stage transitions compose according to transitivity of index refinement. -/
@[simp 900]
theorem zcCompletedDifferentialModuleStageTransition_comp
    {i j k : ZCCompletedDifferentialModuleIndex C ψ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    (zcCompletedDifferentialModuleStageTransition C ψ hij).comp
        (zcCompletedDifferentialModuleStageTransition C ψ hjk) =
      zcCompletedDifferentialModuleStageTransition C ψ (hij.trans hjk) := by
  apply AddMonoidHom.ext
  intro x
  refine Submodule.Quotient.induction_on
    (p := crossedDifferentialRelationSubmodule
      (zcCompletedDifferentialModuleStageScalar C ψ k)) x ?_
  intro z
  refine Finsupp.induction_linear z ?zero ?add ?single
  · simp only [zcCompletedDifferentialModuleStageTransition, Submodule.Quotient.mk_zero,
      map_zero]
  · intro x y hx hy
    simp only [Submodule.Quotient.mk_add, map_add, hx, hy]
  · intro q a
    have hsingle :
        (Submodule.Quotient.mk
            (p := crossedDifferentialRelationSubmodule
              (zcCompletedDifferentialModuleStageScalar C ψ k))
            (Finsupp.single q a) :
          ZCCompletedDifferentialModuleStage C ψ k) =
          a • universalCrossedDifferential
            (zcCompletedDifferentialModuleStageScalar C ψ k) q := by
      rw [← Finsupp.smul_single_one]
      rfl
    let : Module (zcCompletedDifferentialModuleStageRing C ψ k)
        (ZCCompletedDifferentialModuleStage C ψ j) :=
      Module.compHom _ (zcCompletedGroupAlgebraTransition C H hjk.2)
    let : Module (zcCompletedDifferentialModuleStageRing C ψ j)
        (ZCCompletedDifferentialModuleStage C ψ i) :=
      Module.compHom _ (zcCompletedGroupAlgebraTransition C H hij.2)
    let : Module (zcCompletedDifferentialModuleStageRing C ψ k)
        (ZCCompletedDifferentialModuleStage C ψ i) :=
      Module.compHom _ (zcCompletedGroupAlgebraTransition C H (hij.trans hjk).2)
    rw [hsingle]
    simp only [AddMonoidHom.comp_apply, zcCompletedDifferentialModuleStageTransition]
    change
      (crossedHomModuleLift
          (zcCompletedDifferentialModuleStageScalar C ψ j)
          (zcCompletedDifferentialModuleStageTransitionCrossedHom C ψ hij))
        ((crossedHomModuleLift
            (zcCompletedDifferentialModuleStageScalar C ψ k)
            (zcCompletedDifferentialModuleStageTransitionCrossedHom C ψ hjk))
          (a • universalCrossedDifferential
            (zcCompletedDifferentialModuleStageScalar C ψ k) q)) =
        (crossedHomModuleLift
            (zcCompletedDifferentialModuleStageScalar C ψ k)
            (zcCompletedDifferentialModuleStageTransitionCrossedHom C ψ (hij.trans hjk)))
          (a • universalCrossedDifferential
            (zcCompletedDifferentialModuleStageScalar C ψ k) q)
    have hinner :
        (crossedHomModuleLift
            (zcCompletedDifferentialModuleStageScalar C ψ k)
            (zcCompletedDifferentialModuleStageTransitionCrossedHom C ψ hjk))
          (a • universalCrossedDifferential
            (zcCompletedDifferentialModuleStageScalar C ψ k) q) =
          zcCompletedGroupAlgebraTransition C H hjk.2 a •
            universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ j)
              (zcCompletedDifferentialModuleStageSourceTransition C ψ hjk q) := by
      rw [map_smul, crossedHomModuleLift_universal]
      rfl
    have houter :
        (crossedHomModuleLift
            (zcCompletedDifferentialModuleStageScalar C ψ j)
            (zcCompletedDifferentialModuleStageTransitionCrossedHom C ψ hij))
          (zcCompletedGroupAlgebraTransition C H hjk.2 a •
            universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ j)
              (zcCompletedDifferentialModuleStageSourceTransition C ψ hjk q)) =
          zcCompletedGroupAlgebraTransition C H hij.2
              (zcCompletedGroupAlgebraTransition C H hjk.2 a) •
            universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ i)
              (zcCompletedDifferentialModuleStageSourceTransition C ψ hij
                (zcCompletedDifferentialModuleStageSourceTransition C ψ hjk q)) := by
      rw [map_smul, crossedHomModuleLift_universal]
      rfl
    have hrhs :
        (crossedHomModuleLift
            (zcCompletedDifferentialModuleStageScalar C ψ k)
            (zcCompletedDifferentialModuleStageTransitionCrossedHom C ψ (hij.trans hjk)))
          (a • universalCrossedDifferential
            (zcCompletedDifferentialModuleStageScalar C ψ k) q) =
          zcCompletedGroupAlgebraTransition C H (hij.trans hjk).2 a •
            universalCrossedDifferential (zcCompletedDifferentialModuleStageScalar C ψ i)
              (zcCompletedDifferentialModuleStageSourceTransition C ψ (hij.trans hjk) q) := by
      rw [map_smul, crossedHomModuleLift_universal]
      rfl
    have hcoeff :
        zcCompletedGroupAlgebraTransition C H hij.2
            (zcCompletedGroupAlgebraTransition C H hjk.2 a) =
          zcCompletedGroupAlgebraTransition C H (hij.trans hjk).2 a := by
      exact congrFun
        (congrArg DFunLike.coe
          (zcCompletedGroupAlgebraTransition_comp C H hij.2 hjk.2)) a
    rw [hinner, houter, hrhs, hcoeff]
    simp only [zcCompletedDifferentialModuleStageSourceTransition_comp]

end

end FoxDifferential
