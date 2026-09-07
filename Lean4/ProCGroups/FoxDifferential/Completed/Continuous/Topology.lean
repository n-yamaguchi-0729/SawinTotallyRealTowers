import ProCGroups.FoxDifferential.Completed.FreeProC.SemidirectKernelBasis
import ProCGroups.FoxDifferential.Completed.ProCIntegerCoefficients.Augmentation

set_option autoImplicit false

/-!
# Fox differential: completed — continuous — topology

The principal declarations in this module are:

- `freeProCZCCompletedFoxBoundary`
  Source-shaped completed Fox boundary map for a finite generating set. It evaluates a vector of
  completed Fox coefficients against the generator boundaries \([\varphi(x)]-1\).
- `zcCompletedFoxSemidirectHomeomorphProd`
  The completed Fox semidirect target is homeomorphic to its product of components.
- `continuous_foxBoundaryMap`
  A finite Fox boundary map is continuous over any topological ring.
- `continuous_zcCompletedGroupAlgebraProjection`
  A finite stage projection from \(\mathbb{Z}_C\llbracket G\rrbracket\) is continuous.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.Completion
open scoped BigOperators

universe u v

section BoundaryMapContinuity

variable {R : Type u} [Ring R] [TopologicalSpace R] [ContinuousAdd R] [ContinuousMul R]
variable {X : Type v} [Fintype X]

/-- A finite Fox boundary map is continuous over any topological ring. -/
theorem continuous_foxBoundaryMap (generatorBoundary : X → R) :
    Continuous (foxBoundaryMap generatorBoundary) := by
  change Continuous (fun v : X → R => ∑ x : X, v x * generatorBoundary x)
  exact continuous_finsetSum _ fun x _ => (continuous_apply x).mul continuous_const

end BoundaryMapContinuity

section CompletedGroupAlgebraTopology

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Each finite-stage \(\mathbb{Z}_C\)-completed group algebra carries its finite-stage topology. -/
instance instTopologicalSpaceZCCompletedGroupAlgebraStage
    (i : ZCCompletedGroupAlgebraIndex C G) :
    TopologicalSpace (ZCCompletedGroupAlgebraStage C G i) :=
  ⊥

/-- Each finite-stage \(\mathbb{Z}_C\)-completed group algebra carries the discrete topology. -/
instance instDiscreteTopologyZCCompletedGroupAlgebraStage
    (i : ZCCompletedGroupAlgebraIndex C G) :
    DiscreteTopology (ZCCompletedGroupAlgebraStage C G i) :=
  ⟨rfl⟩

/-- Each finite-stage \(\mathbb{Z}_C\)-completed group algebra is compact. -/
instance instCompactSpaceZCCompletedGroupAlgebraStage
    (i : ZCCompletedGroupAlgebraIndex C G) :
    CompactSpace (ZCCompletedGroupAlgebraStage C G i) := by
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  let : Finite (ZCCompletedGroupAlgebraStage C G i) :=
    finite_modNCompletedGroupAlgebraStageInClass
      (n := i.1.modulus) (G := G) C
      i.2
  let : Fintype (ZCCompletedGroupAlgebraStage C G i) := Fintype.ofFinite _
  infer_instance

/-- Each finite-stage \(\mathbb{Z}_C\)-completed group algebra is a \(T_2\) space. -/
instance instT2SpaceZCCompletedGroupAlgebraStage
    (i : ZCCompletedGroupAlgebraIndex C G) :
    T2Space (ZCCompletedGroupAlgebraStage C G i) :=
  inferInstance

/-- Each finite-stage \(\mathbb{Z}_C\)-completed group algebra is totally disconnected. -/
instance instTotallyDisconnectedSpaceZCCompletedGroupAlgebraStage
    (i : ZCCompletedGroupAlgebraIndex C G) :
    TotallyDisconnectedSpace (ZCCompletedGroupAlgebraStage C G i) :=
  inferInstance

/-- The completed \(\mathbb{Z}_C\)-group algebra is compact. -/
instance instCompactSpaceZCCompletedGroupAlgebra :
    CompactSpace (ZCCompletedGroupAlgebra C G) := by
  let S := zcCompletedGroupAlgebraSystem C G
  change CompactSpace S.inverseLimit
  let : ∀ i : ZCCompletedGroupAlgebraIndex C G, TopologicalSpace (S.X i) := fun _ =>
    inferInstance
  let : ∀ i : ZCCompletedGroupAlgebraIndex C G, CompactSpace (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    change @CompactSpace (ZCCompletedGroupAlgebraStage C G i) ⊥
    let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
    let : Finite (ZCCompletedGroupAlgebraStage C G i) :=
      finite_modNCompletedGroupAlgebraStageInClass
        (n := i.1.modulus) (G := G) C i.2
    exact Finite.compactSpace
  let : ∀ i : ZCCompletedGroupAlgebraIndex C G, T2Space (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    change @T2Space (ZCCompletedGroupAlgebraStage C G i) ⊥
    exact @DiscreteTopology.toT2Space _ ⊥ ⟨rfl⟩
  infer_instance

/-- The completed \(\mathbb{Z}_C\)-group algebra is a \(T_2\) space. -/
instance instT2SpaceZCCompletedGroupAlgebra :
    T2Space (ZCCompletedGroupAlgebra C G) := by
  let S := zcCompletedGroupAlgebraSystem C G
  change T2Space S.inverseLimit
  let : ∀ i : ZCCompletedGroupAlgebraIndex C G, TopologicalSpace (S.X i) := fun _ =>
    inferInstance
  let : ∀ i : ZCCompletedGroupAlgebraIndex C G, T2Space (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    change @T2Space (ZCCompletedGroupAlgebraStage C G i) ⊥
    exact @DiscreteTopology.toT2Space _ ⊥ ⟨rfl⟩
  exact S.t2Space_inverseLimit

/-- A finite stage projection from \(\mathbb{Z}_C\llbracket G\rrbracket\) is continuous. -/
theorem continuous_zcCompletedGroupAlgebraProjection
    (i : ZCCompletedGroupAlgebraIndex C G) :
    Continuous (zcCompletedGroupAlgebraProjection C G i) :=
  (continuous_apply i).comp continuous_subtype_val

/--
A finite stage projection from \(\mathbb{Z}_C\llbracket G\rrbracket\), regarded as a ring
homomorphism, is continuous.
-/
theorem continuous_zcCompletedGroupAlgebraProjectionRingHom
    (i : ZCCompletedGroupAlgebraIndex C G) :
    Continuous (zcCompletedGroupAlgebraProjectionRingHom C G i) :=
  continuous_zcCompletedGroupAlgebraProjection C G i

/-- The completed \(\mathbb{Z}_C\)-group algebra is totally disconnected. -/
instance instTotallyDisconnectedSpaceZCCompletedGroupAlgebra :
    TotallyDisconnectedSpace (ZCCompletedGroupAlgebra C G) := by
  let S := zcCompletedGroupAlgebraSystem C G
  change TotallyDisconnectedSpace S.inverseLimit
  let : ∀ i : ZCCompletedGroupAlgebraIndex C G, TopologicalSpace (S.X i) := fun _ =>
    inferInstance
  let : ∀ i : ZCCompletedGroupAlgebraIndex C G, TotallyDisconnectedSpace (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraSystem]
    change @TotallyDisconnectedSpace (ZCCompletedGroupAlgebraStage C G i) ⊥
    exact @TotallySeparatedSpace.totallyDisconnectedSpace _ ⊥
      (@TotallySeparatedSpace.of_discrete _ ⊥ ⟨rfl⟩)
  exact S.totallyDisconnectedSpace_inverseLimit

/--
Addition on \(\mathbb{Z}_C\llbracket H\rrbracket\) is continuous for the inverse-limit topology.
-/
instance instContinuousAddZCCompletedGroupAlgebra :
    ContinuousAdd (ZCCompletedGroupAlgebra C G) where
  continuous_add := by
    have hval : Continuous (fun p : ZCCompletedGroupAlgebra C G ×
        ZCCompletedGroupAlgebra C G =>
        ((p.1 + p.2 : ZCCompletedGroupAlgebra C G) :
          (i : ZCCompletedGroupAlgebraIndex C G) → ZCCompletedGroupAlgebraStage C G i)) := by
      exact continuous_pi fun i =>
        (continuous_of_discreteTopology :
          Continuous (fun q : ZCCompletedGroupAlgebraStage C G i ×
              ZCCompletedGroupAlgebraStage C G i => q.1 + q.2)).comp
            (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).prodMk
              ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))
    convert
      (Continuous.subtype_mk (p := ZCCompletedGroupAlgebraCompatible C G) hval
        (fun p => (p.1 + p.2 : ZCCompletedGroupAlgebra C G).property)) using 1

/-- Negation on the completed group algebra is continuous for the inverse-limit topology. -/
instance instContinuousNegZCCompletedGroupAlgebra :
    ContinuousNeg (ZCCompletedGroupAlgebra C G) where
  continuous_neg := by
    change Continuous (fun x : ZCCompletedGroupAlgebra C G => -x)
    have hval : Continuous (fun x : ZCCompletedGroupAlgebra C G =>
        ((-x : ZCCompletedGroupAlgebra C G) :
          (i : ZCCompletedGroupAlgebraIndex C G) → ZCCompletedGroupAlgebraStage C G i)) := by
      exact continuous_pi fun i =>
        (continuous_of_discreteTopology :
          Continuous (fun y : ZCCompletedGroupAlgebraStage C G i => -y)).comp
          ((continuous_apply i).comp continuous_subtype_val)
    convert
      (Continuous.subtype_mk (p := ZCCompletedGroupAlgebraCompatible C G) hval
        (fun x => (-x : ZCCompletedGroupAlgebra C G).property)) using 1

/-- The completed group algebra has addition defined coordinatewise on compatible families. -/
instance instIsTopologicalAddGroupZCCompletedGroupAlgebra :
    IsTopologicalAddGroup (ZCCompletedGroupAlgebra C G) where
  continuous_add := continuous_add
  continuous_neg := continuous_neg

/-- Multiplication on the completed group algebra is continuous for the inverse-limit topology. -/
instance instContinuousMulZCCompletedGroupAlgebra :
    ContinuousMul (ZCCompletedGroupAlgebra C G) where
  continuous_mul := by
    have hval : Continuous (fun p : ZCCompletedGroupAlgebra C G ×
        ZCCompletedGroupAlgebra C G =>
        ((p.1 * p.2 : ZCCompletedGroupAlgebra C G) :
          (i : ZCCompletedGroupAlgebraIndex C G) → ZCCompletedGroupAlgebraStage C G i)) := by
      exact continuous_pi fun i =>
        (continuous_of_discreteTopology :
          Continuous (fun q : ZCCompletedGroupAlgebraStage C G i ×
              ZCCompletedGroupAlgebraStage C G i => q.1 * q.2)).comp
            (((continuous_apply i).comp (continuous_subtype_val.comp continuous_fst)).prodMk
              ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))
    convert
      (Continuous.subtype_mk (p := ZCCompletedGroupAlgebraCompatible C G) hval
        (fun p => (p.1 * p.2 : ZCCompletedGroupAlgebra C G).property)) using 1

/-- The completed group algebra inherits a ring structure from the compatible finite-stage rings. -/
instance instIsTopologicalRingZCCompletedGroupAlgebra :
    IsTopologicalRing (ZCCompletedGroupAlgebra C G) where
  continuous_add := continuous_add
  continuous_mul := continuous_mul
  continuous_neg := continuous_neg

/-- Scalar multiplication is continuous for the relevant inverse-limit topology. -/
instance instContinuousSMulZCCompletedGroupAlgebraSelf :
    ContinuousSMul (ZCCompletedGroupAlgebra C G) (ZCCompletedGroupAlgebra C G) :=
  ContinuousMul.to_continuousSMul

/-- The scalar action map on the completed group algebra is continuous. -/
theorem continuous_zcCompletedGroupAlgebra_smul :
    Continuous (fun p : ZCCompletedGroupAlgebra C G × ZCCompletedGroupAlgebra C G =>
      p.1 • p.2) :=
  continuous_smul

/-- The completed group-like map \(G \to \mathbb{Z}_C\llbracket G\rrbracket\) is continuous. -/
theorem continuous_zcGroupLike : Continuous (zcGroupLike C G) := by
  have hval : Continuous (fun g : G =>
      ((zcGroupLike C G g : ZCCompletedGroupAlgebra C G) :
        (i : ZCCompletedGroupAlgebraIndex C G) → ZCCompletedGroupAlgebraStage C G i)) := by
    refine continuous_pi fun i => ?_
    let : DiscreteTopology (CompletedGroupAlgebraQuotientInClass G C i.2) :=
      QuotientGroup.discreteTopology
        (ProCGroups.openNormalSubgroup_isOpen (G := G)
          ((OrderDual.ofDual i.2).1 : OpenNormalSubgroup G))
    exact (continuous_of_discreteTopology :
        Continuous (fun q : CompletedGroupAlgebraQuotientInClass G C i.2 =>
          MonoidAlgebra.of (ModNCompletedCoeff i.1.modulus)
            (CompletedGroupAlgebraQuotientInClass G C i.2) q)).comp
      (continuous_quotient_mk' : Continuous (fun g : G =>
        QuotientGroup.mk' (((OrderDual.ofDual i.2).1 : OpenNormalSubgroup G) : Subgroup G) g))
  simpa [Subtype.eta] using
    (Continuous.subtype_mk (p := ZCCompletedGroupAlgebraCompatible C G) hval
      (fun g => (zcGroupLike C G g : ZCCompletedGroupAlgebra C G).property))

/--
The completed augmentation \(\mathbb{Z}_C\llbracket G\rrbracket \to \mathbb{Z}_C\) is continuous
in the inverse-limit topology.
-/
theorem continuous_zcCompletedGroupAlgebraAugmentation
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    Continuous (zcCompletedGroupAlgebraAugmentation C G) := by
  have hval : Continuous (fun x : ZCCompletedGroupAlgebra C G =>
      (zcCompletedGroupAlgebraAugmentation C G x :
        (i : ProCIntegerIndex C) → ProCIntegerStage C i)) := by
    refine continuous_pi fun i => ?_
    let : Fact (0 < i.modulus) := ⟨i.positive⟩
    let U := zcCompletedGroupAlgebraTopIndex C G
    let : TopologicalSpace (ModNCompletedGroupAlgebraStageInClass i.modulus G C U) := ⊥
    let : DiscreteTopology (ModNCompletedGroupAlgebraStageInClass i.modulus G C U) := ⟨rfl⟩
    exact
      (continuous_of_discreteTopology :
        Continuous (modNCompletedGroupAlgebraStageAugmentationInClass i.modulus G C U)).comp
        ((continuous_apply (i, U)).comp continuous_subtype_val)
  simpa [zcCompletedGroupAlgebraAugmentation, Subtype.eta] using
    (Continuous.subtype_mk (p := ProCIntegerCompatible C) hval
      (fun x => (zcCompletedGroupAlgebraAugmentation C G x).property))

/-- The completed augmentation ideal is closed in \(\mathbb{Z}_C\llbracket G\rrbracket\). -/
theorem isClosed_zcCompletedGroupAlgebraAugmentationIdeal
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    IsClosed
      ((zcCompletedGroupAlgebraAugmentationIdeal C G :
        Ideal (ZCCompletedGroupAlgebra C G)) : Set (ZCCompletedGroupAlgebra C G)) := by
  change IsClosed ((zcCompletedGroupAlgebraAugmentation C G) ⁻¹' ({0} : Set (ZCCoeff C)))
  exact isClosed_singleton.preimage
    (continuous_zcCompletedGroupAlgebraAugmentation (C := C) (G := G))

/-- The completed \(\mathbb{Z}_C\)-group algebra augmentation ideal is compact. -/
instance instCompactSpaceZCCompletedGroupAlgebraAugmentationIdeal
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    CompactSpace (ZCCompletedGroupAlgebraAugmentationIdeal C G) := by
  exact
    (isClosed_zcCompletedGroupAlgebraAugmentationIdeal
      (C := C) (G := G)).isClosedEmbedding_subtypeVal.compactSpace

/-- The completed \(\mathbb{Z}_C\)-group algebra augmentation ideal is a \(T_2\) space. -/
instance instT2SpaceZCCompletedGroupAlgebraAugmentationIdeal
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C] :
    T2Space (ZCCompletedGroupAlgebraAugmentationIdeal C G) :=
  inferInstance

variable {A : Type v} [Group A] [TopologicalSpace A]

/--
The completed group-algebra boundary \(a \mapsto [\psi(a)] - 1\) is continuous whenever \(\psi\)
is continuous.
-/
theorem continuous_zcCompletedGroupAlgebraBoundary
    (ψ : A →* G) (hψ : Continuous ψ) :
    Continuous (zcCompletedGroupAlgebraBoundary C ψ) := by
  convert
    ((continuous_zcGroupLike (C := C) (G := G)).comp hψ).sub continuous_const using 1 <;>
    rfl

variable {X : Type v} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- The completed \(\mathbb{Z}_C\llbracket G\rrbracket\) Fox boundary/Euler map is continuous. -/
theorem continuous_zcFreeGroupFoxBoundary (ψ : FreeGroup X →* G) :
    Continuous (zcFreeGroupFoxBoundary C ψ) := by
  classical
  rw [zcFreeGroupFoxBoundary_eq_foxBoundaryMap]
  exact continuous_foxBoundaryMap _

end CompletedGroupAlgebraTopology

section CompletedSourceBoundary

variable (C : ProCGroups.FiniteGroupClass.{u})
variable {X H : Type u} [Fintype X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
Source-shaped completed Fox boundary map for a finite generating set. It evaluates a vector of
completed Fox coefficients against the generator boundaries \([\varphi(x)]-1\).
-/
def freeProCZCCompletedFoxBoundary (φ : X → H) :
    ZCFreeFoxCoordinates C (X := X) (H := H) →ₗ[ZCCompletedGroupAlgebra C H]
      ZCCompletedGroupAlgebra C H :=
  foxBoundaryMap (fun x : X => zcGroupLike C H (φ x) - 1)


/--
The boundary map is evaluated on the canonical generators and then extended linearly to the
completed coordinate module.
-/
theorem freeProCZCCompletedFoxBoundary_apply
    (φ : X → H) (v : ZCFreeFoxCoordinates C (X := X) (H := H)) :
    freeProCZCCompletedFoxBoundary C φ v =
      ∑ x : X, v x * (zcGroupLike C H (φ x) - 1) :=
  rfl

variable [DecidableEq X]


/--
The source-shaped completed Fox boundary map sends the standard basis vector at \(x\) to
\([\varphi(x)]-1\).
-/
@[simp]
theorem freeProCZCCompletedFoxBoundary_single
    (φ : X → H) (x : X) :
    freeProCZCCompletedFoxBoundary C φ
        (Pi.single x (1 : ZCCompletedGroupAlgebra C H)) =
      zcGroupLike C H (φ x) - 1 := by
  simp only [freeProCZCCompletedFoxBoundary, foxBoundaryMap_single]

omit [DecidableEq X] in
/-- The source-shaped completed Fox boundary map is continuous for finite generating sets. -/
theorem continuous_freeProCZCCompletedFoxBoundary (φ : X → H) :
    Continuous (freeProCZCCompletedFoxBoundary C φ) :=
  continuous_foxBoundaryMap _

omit [DecidableEq X] in
/--
The source-shaped completed Fox boundary has image equal to the submodule generated by the
augmentation generators \([\varphi(x)]-1\).
-/
theorem freeProCZCCompletedFoxBoundary_range
    (φ : X → H) :
    (freeProCZCCompletedFoxBoundary C φ).range =
      Submodule.span (ZCCompletedGroupAlgebra C H)
        (Set.range fun x : X => zcGroupLike C H (φ x) - 1) := by
  classical
  apply le_antisymm
  · rintro y ⟨v, rfl⟩
    rw [freeProCZCCompletedFoxBoundary_apply]
    exact Submodule.sum_mem _ fun x _ =>
      Submodule.smul_mem _ (v x)
        (Submodule.subset_span (Set.mem_range_self x))
  · refine Submodule.span_le.2 ?_
    rintro y ⟨x, rfl⟩
    exact ⟨Pi.single x (1 : ZCCompletedGroupAlgebra C H), by simp only
        [freeProCZCCompletedFoxBoundary_single]⟩

omit [DecidableEq X] in
/--
If the chosen finite source hits every element of H, the source-shaped completed Fox boundary
has image equal to the algebraic standard-generator ideal.
-/
theorem freeProCZCCompletedFoxBoundary_range_eq_standardAugmentationIdeal_of_surjective
    (φ : X → H) (hφ : Function.Surjective φ) :
    (freeProCZCCompletedFoxBoundary C φ).range =
      (zcCompletedGroupAlgebraStandardAugmentationIdeal C H :
        Submodule (ZCCompletedGroupAlgebra C H) (ZCCompletedGroupAlgebra C H)) := by
  rw [freeProCZCCompletedFoxBoundary_range,
    zcCompletedGroupAlgebraStandardAugmentationIdeal_eq_span]
  congr 1
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨φ x, rfl⟩
  · rintro ⟨h, rfl⟩
    rcases hφ h with ⟨x, rfl⟩
    exact ⟨x, rfl⟩

end CompletedSourceBoundary

section SemidirectTopology

variable (C : ProCGroups.FiniteGroupClass.{v})
variable (X : Type u) [DecidableEq X]
variable (H : Type v) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The completed Fox semidirect product carries the inverse-limit topological space structure. -/
instance instTopologicalSpaceZCCompletedFoxSemidirect :
    TopologicalSpace (ZCCompletedFoxSemidirect C X H) :=
  TopologicalSpace.induced
    (fun a : ZCCompletedFoxSemidirect C X H => (a.left, a.right)) inferInstance

/-- The completed Fox semidirect target is homeomorphic to its product of components. -/
def zcCompletedFoxSemidirectHomeomorphProd :
    ZCCompletedFoxSemidirect C X H ≃ₜ (ZCFreeFoxCoordinates C (X := X) (H := H) × H) where
  toEquiv :=
    { toFun := fun a => (a.left, a.right)
      invFun := fun p => { left := p.1, right := p.2 }
      left_inv := by
        intro a
        cases a
        rfl
      right_inv := by
        intro p
        cases p
        rfl }
  continuous_toFun := continuous_induced_dom
  continuous_invFun := by
    rw [continuous_induced_rng]
    exact continuous_id

omit [DecidableEq X] in
/-- The component-pair map from the semidirect target is continuous. -/
theorem continuous_zcCompletedFoxSemidirect_toProd :
    Continuous (fun a : ZCCompletedFoxSemidirect C X H => (a.left, a.right)) :=
  continuous_induced_dom

omit [DecidableEq X] in
/-- The Fox-coordinate projection from the semidirect target is continuous. -/
theorem continuous_zcCompletedFoxSemidirect_left :
    Continuous (fun a : ZCCompletedFoxSemidirect C X H => a.left) :=
  continuous_fst.comp (continuous_zcCompletedFoxSemidirect_toProd C X H)

omit [DecidableEq X] in
/-- The group projection from the semidirect target is continuous. -/
theorem continuous_zcCompletedFoxSemidirect_right :
    Continuous (fun a : ZCCompletedFoxSemidirect C X H => a.right) :=
  continuous_snd.comp (continuous_zcCompletedFoxSemidirect_toProd C X H)

/-- The completed Fox semidirect product is compact as an inverse limit of finite stages. -/
instance instCompactSpaceZCCompletedFoxSemidirect [CompactSpace H] :
    CompactSpace (ZCCompletedFoxSemidirect C X H) := by
  exact (zcCompletedFoxSemidirectHomeomorphProd C X H).symm.compactSpace

/-- The completed Fox semidirect product is Hausdorff for the inverse-limit topology. -/
instance instT2SpaceZCCompletedFoxSemidirect [T2Space H] :
    T2Space (ZCCompletedFoxSemidirect C X H) := by
  exact (zcCompletedFoxSemidirectHomeomorphProd C X H).symm.t2Space

/--
The completed Fox semidirect product is totally disconnected as an inverse limit of finite
discrete stages.
-/
instance instTotallyDisconnectedSpaceZCCompletedFoxSemidirect [TotallyDisconnectedSpace H] :
    TotallyDisconnectedSpace (ZCCompletedFoxSemidirect C X H) := by
  exact (zcCompletedFoxSemidirectHomeomorphProd C X H).symm.totallyDisconnectedSpace

/-- The completed Fox semidirect product is a topological group for the inverse-limit topology. -/
instance instIsTopologicalGroupZCCompletedFoxSemidirect :
    IsTopologicalGroup (ZCCompletedFoxSemidirect C X H) where
  continuous_mul := by
    rw [continuous_induced_rng]
    have hleft : Continuous (fun p : ZCCompletedFoxSemidirect C X H ×
        ZCCompletedFoxSemidirect C X H => (p.1 * p.2).left) := by
      refine continuous_pi fun x => ?_
      have hleftA : Continuous (fun p : ZCCompletedFoxSemidirect C X H ×
          ZCCompletedFoxSemidirect C X H => p.1.left x) :=
        (continuous_apply x).comp
          ((continuous_zcCompletedFoxSemidirect_left C X H).comp continuous_fst)
      have hrightA : Continuous (fun p : ZCCompletedFoxSemidirect C X H ×
          ZCCompletedFoxSemidirect C X H => p.2.left x) :=
        (continuous_apply x).comp
          ((continuous_zcCompletedFoxSemidirect_left C X H).comp continuous_snd)
      have hgroup : Continuous (fun p : ZCCompletedFoxSemidirect C X H ×
          ZCCompletedFoxSemidirect C X H => zcGroupLike C H p.1.right) :=
        (continuous_zcGroupLike (C := C) (G := H)).comp
          ((continuous_zcCompletedFoxSemidirect_right C X H).comp continuous_fst)
      change Continuous (fun p : ZCCompletedFoxSemidirect C X H ×
          ZCCompletedFoxSemidirect C X H =>
        p.1.left x + zcGroupLike C H p.1.right * p.2.left x)
      exact hleftA.add (hgroup.mul hrightA)
    have hright : Continuous (fun p : ZCCompletedFoxSemidirect C X H ×
        ZCCompletedFoxSemidirect C X H => (p.1 * p.2).right) := by
      exact ((continuous_zcCompletedFoxSemidirect_right C X H).comp continuous_fst).mul
        ((continuous_zcCompletedFoxSemidirect_right C X H).comp continuous_snd)
    exact hleft.prodMk hright
  continuous_inv := by
    rw [continuous_induced_rng]
    have hleft : Continuous (fun a : ZCCompletedFoxSemidirect C X H => a⁻¹.left) := by
      refine continuous_pi fun x => ?_
      have hleftA : Continuous (fun a : ZCCompletedFoxSemidirect C X H => a.left x) :=
        (continuous_apply x).comp (continuous_zcCompletedFoxSemidirect_left C X H)
      have hgroup : Continuous (fun a : ZCCompletedFoxSemidirect C X H =>
          zcGroupLike C H a.right⁻¹) :=
        (continuous_zcGroupLike (C := C) (G := H)).comp
          ((continuous_zcCompletedFoxSemidirect_right C X H).inv)
      change Continuous (fun a : ZCCompletedFoxSemidirect C X H =>
        -(zcGroupLike C H a.right⁻¹ * a.left x))
      exact (hgroup.mul hleftA).neg
    have hright : Continuous (fun a : ZCCompletedFoxSemidirect C X H => a⁻¹.right) := by
      exact (continuous_zcCompletedFoxSemidirect_right C X H).inv
    exact hleft.prodMk hright

end SemidirectTopology

section CompletedGroupAlgebraProC

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (H : Type u) [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
One finite stage \((\mathbb{Z}/n\mathbb{Z})[H/U]\), viewed multiplicatively through its additive
group, belongs to \(C\).
-/
theorem finiteGroupClass_multiplicative_modNCompletedGroupAlgebraStageInClass_mem
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hProd : ProCGroups.FiniteGroupClass.FiniteProductClosed C)
    (i : ProCIntegerIndex C) (U : CompletedGroupAlgebraIndexInClass H C) :
    C (Multiplicative (ModNCompletedGroupAlgebraStageInClass i.modulus H C U)) := by
  classical
  let : Fact (0 < i.modulus) := ⟨i.positive⟩
  let Q := CompletedGroupAlgebraQuotientInClass H C U
  let : Finite Q := ProCGroups.FiniteGroupClass.finite (C := C) (OrderDual.ofDual U).2
  let : Fintype Q := Fintype.ofFinite Q
  let e :
      Multiplicative (ModNCompletedGroupAlgebraStageInClass i.modulus H C U) ≃*
        (Q → ULift.{u} (Multiplicative (ModNCompletedCoeff i.modulus))) :=
    { toFun := fun a q =>
        ULift.up (Multiplicative.ofAdd ((Finsupp.equivFunOnFinite a.toAdd.coeff) q))
      invFun := fun f =>
        Multiplicative.ofAdd
          (MonoidAlgebra.ofCoeff
            (Finsupp.equivFunOnFinite.symm fun q => (f q).down.toAdd))
      left_inv := by
        intro a
        apply Multiplicative.ext
        apply MonoidAlgebra.coeff_injective
        exact Finsupp.equivFunOnFinite.left_inv a.toAdd.coeff
      right_inv := by
        intro f
        funext q
        have hcoeff :
            (Finsupp.equivFunOnFinite
              (Finsupp.equivFunOnFinite.symm fun q => (f q).down.toAdd)) q =
              (f q).down.toAdd := by
          exact congrFun
            (Finsupp.equivFunOnFinite.right_inv
              (fun q => (f q).down.toAdd)) q
        apply ULift.ext
        apply Multiplicative.ext
        exact hcoeff
      map_mul' := by
        intro a b
        funext q
        apply ULift.ext
        apply Multiplicative.ext
        rfl }
  have hPi :
      C (Q → ULift.{u} (Multiplicative (ModNCompletedCoeff i.modulus))) := by
    exact hProd (ι := Q)
      (G := fun _ => ULift.{u} (Multiplicative (ModNCompletedCoeff i.modulus)))
      (fun _ => by
        apply C.mem_of_memAcrossUniverses
        apply (C.memAcrossUniverses_ulift_iff
          (Multiplicative (ModNCompletedCoeff i.modulus))).2
        simpa [ModNCompletedCoeff, ProCIntegerStage] using i.cyclic_mem)
  exact hIso ⟨e.symm⟩ hPi

/--
The group-valued inverse system underlying the additive group of \(\mathbb{Z}_C\llbracket
H\rrbracket\), written multiplicatively.
-/
def zcCompletedGroupAlgebraMultiplicativeSystem :
    ProCGroups.InverseSystems.InverseSystem (I := ZCCompletedGroupAlgebraIndex C H) where
  X := fun i => Multiplicative (ZCCompletedGroupAlgebraStage C H i)
  topologicalSpace := fun _ => ⊥
  map := fun {i j} hij =>
    (zcCompletedGroupAlgebraTransition C H hij).toAddMonoidHom.toMultiplicative
  continuous_map := by
    intro i j hij
    exact continuous_bot
  map_id := by
    intro i
    funext x
    apply Multiplicative.ext
    change zcCompletedGroupAlgebraTransition C H (le_rfl : i ≤ i) x.toAdd = x.toAdd
    simp only [zcCompletedGroupAlgebraTransition_id, RingHom.id_apply]
  map_comp := by
    intro i j k hij hjk
    funext x
    apply Multiplicative.ext
    change
      zcCompletedGroupAlgebraTransition C H hij
          (zcCompletedGroupAlgebraTransition C H hjk x.toAdd) =
        zcCompletedGroupAlgebraTransition C H (hij.trans hjk) x.toAdd
    exact congrArg (fun f : ZCCompletedGroupAlgebraStage C H k →+*
        ZCCompletedGroupAlgebraStage C H i => f x.toAdd)
      (zcCompletedGroupAlgebraTransition_comp C H hij hjk)

/-- Each stage of the multiplicative system carries the discrete topology selected by the system. -/
instance instDiscreteTopologyZCCompletedGroupAlgebraMultiplicativeSystemStage
    (i : ZCCompletedGroupAlgebraIndex C H) :
    DiscreteTopology ((zcCompletedGroupAlgebraMultiplicativeSystem C H).X i) :=
  ⟨rfl⟩

/-- Each stage of the multiplicative system is finite. -/
instance instFiniteZCCompletedGroupAlgebraMultiplicativeSystemStage
    (i : ZCCompletedGroupAlgebraIndex C H) :
    Finite ((zcCompletedGroupAlgebraMultiplicativeSystem C H).X i) := by
  dsimp [zcCompletedGroupAlgebraMultiplicativeSystem]
  let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
  let : Finite (ZCCompletedGroupAlgebraStage C H i) :=
    finite_modNCompletedGroupAlgebraStageInClass
      (n := i.1.modulus) (G := H) C i.2
  exact @Finite.of_equiv _ _ (inferInstance : Finite (ZCCompletedGroupAlgebraStage C H i))
    Multiplicative.toAdd

/-- Each finite-stage group algebra in the multiplicative system carries its group structure. -/
instance instGroupZCCompletedGroupAlgebraMultiplicativeSystemStage
    (i : ZCCompletedGroupAlgebraIndex C H) :
    Group ((zcCompletedGroupAlgebraMultiplicativeSystem C H).X i) := by
  dsimp [zcCompletedGroupAlgebraMultiplicativeSystem]
  infer_instance

/-- Each finite-stage group algebra in the multiplicative system is a topological group. -/
instance instIsTopologicalGroupZCCompletedGroupAlgebraMultiplicativeSystemStage
    (i : ZCCompletedGroupAlgebraIndex C H) :
    IsTopologicalGroup ((zcCompletedGroupAlgebraMultiplicativeSystem C H).X i) := by
  exact
    { continuous_mul := continuous_of_discreteTopology
      continuous_inv := continuous_of_discreteTopology }

/-- The multiplicative finite-stage group-algebra system is group-valued. -/
instance instIsGroupSystemZCCompletedGroupAlgebraMultiplicativeSystem :
    ProCGroups.InverseSystems.IsGroupSystem
      (zcCompletedGroupAlgebraMultiplicativeSystem C H) where
  map_one := by
    intro i j hij
    apply Multiplicative.ext
    change zcCompletedGroupAlgebraTransition C H hij 0 = 0
    exact map_zero _
  map_mul := by
    intro i j hij x y
    change Multiplicative (ZCCompletedGroupAlgebraStage C H j) at x y
    apply Multiplicative.ext
    change zcCompletedGroupAlgebraTransition C H hij (x.toAdd + y.toAdd) =
      zcCompletedGroupAlgebraTransition C H hij x.toAdd +
        zcCompletedGroupAlgebraTransition C H hij y.toAdd
    exact map_add _ _ _
  map_inv := by
    intro i j hij x
    change Multiplicative (ZCCompletedGroupAlgebraStage C H j) at x
    apply Multiplicative.ext
    change zcCompletedGroupAlgebraTransition C H hij (-x.toAdd) =
      -zcCompletedGroupAlgebraTransition C H hij x.toAdd
    exact (zcCompletedGroupAlgebraTransition C H hij).map_neg x.toAdd

/--
The multiplicative inverse limit of the finite completed group-algebra stages is the additive
group underlying \(\mathbb{Z}_C\llbracket H\rrbracket\), written multiplicatively.
-/
def zcCompletedGroupAlgebraMultiplicativeLimitEquiv :
    (zcCompletedGroupAlgebraMultiplicativeSystem C H).inverseLimit ≃ₜ*
      Multiplicative (ZCCompletedGroupAlgebra C H) := by
  let S := zcCompletedGroupAlgebraMultiplicativeSystem C H
  letI : ∀ i : ZCCompletedGroupAlgebraIndex C H, Group (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraMultiplicativeSystem]
    infer_instance
  letI : ProCGroups.InverseSystems.IsGroupSystem S := by
    dsimp [S]
    infer_instance
  refine
    { toMulEquiv := ?_
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · refine
      { toFun := fun x =>
          Multiplicative.ofAdd
            (⟨fun i => (S.projection i x).toAdd, by
              intro i j hij
              exact congrArg Multiplicative.toAdd (S.projection_compatible x i j hij)⟩ :
              ZCCompletedGroupAlgebra C H)
        invFun := fun x =>
          (⟨fun i =>
              Multiplicative.ofAdd
                (zcCompletedGroupAlgebraProjection C H i x.toAdd), by
            intro i j hij
            apply Multiplicative.ext
            exact x.toAdd.2 i j hij⟩ :
            S.inverseLimit)
        left_inv := by
          intro x
          apply S.ext
          intro i
          rfl
        right_inv := by
          intro x
          apply Multiplicative.ext
          ext i
          rfl
        map_mul' := by
          intro x y
          apply Multiplicative.ext
          ext i
          rfl }
  · refine continuous_ofAdd.comp ?_
    have hambient : Continuous fun x : S.inverseLimit =>
        (fun i : ZCCompletedGroupAlgebraIndex C H => (S.projection i x).toAdd :
          ∀ i : ZCCompletedGroupAlgebraIndex C H, ZCCompletedGroupAlgebraStage C H i) := by
      exact continuous_pi fun i => continuous_toAdd.comp (S.continuous_projection i)
    exact Continuous.subtype_mk hambient (fun x => by
      intro i j hij
      exact congrArg Multiplicative.toAdd (S.projection_compatible x i j hij))
  · have hambient : Continuous fun x : Multiplicative (ZCCompletedGroupAlgebra C H) =>
        (fun i : ZCCompletedGroupAlgebraIndex C H =>
          Multiplicative.ofAdd (zcCompletedGroupAlgebraProjection C H i x.toAdd) :
          ∀ i : ZCCompletedGroupAlgebraIndex C H, S.X i) := by
      exact continuous_pi fun i =>
        continuous_ofAdd.comp
          ((continuous_apply i).comp (continuous_subtype_val.comp continuous_toAdd))
    exact Continuous.subtype_mk hambient (fun x => by
      intro i j hij
      apply Multiplicative.ext
      exact x.toAdd.2 i j hij)

omit [IsTopologicalGroup H] in
/-- The two-parameter completed group-algebra index is directed when \(C\) is a formation. -/
theorem directed_zcCompletedGroupAlgebraIndex_of_formation
    (hForm : ProCGroups.FiniteGroupClass.Formation C) :
    Directed (· ≤ ·)
      (id : ZCCompletedGroupAlgebraIndex C H → ZCCompletedGroupAlgebraIndex C H) := by
  intro i j
  rcases ProCIntegerIndex.directed_of_formation (C := C) hForm i.1 j.1 with
    ⟨kcoeff, hki_coeff, hkj_coeff⟩
  rcases ProCGroups.ProC.directed_openNormalSubgroupInClass
      (C := C) (G := H) hForm i.2 j.2 with
    ⟨kquot, hki_quot, hkj_quot⟩
  exact ⟨(kcoeff, kquot), ⟨hki_coeff, hki_quot⟩, ⟨hkj_coeff, hkj_quot⟩⟩

/-- The additive group underlying \(\mathbb{Z}_C\llbracket H\rrbracket\), written multiplicatively,
has an open-normal \(C\)-basis. -/
theorem hasOpenNormalBasisInClass_multiplicative_zcCompletedGroupAlgebra
    (hForm : ProCGroups.FiniteGroupClass.Formation C) :
        ProCGroups.ProC.HasOpenNormalBasisInClass C (Multiplicative (ZCCompletedGroupAlgebra C
        H)) := by
  let : ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C :=
    hForm.containsTrivialQuotients
  let : Nonempty (ProCIntegerIndex C) :=
    ⟨ProCIntegerIndex.terminal hForm.containsTrivialQuotients⟩
  let : Nonempty (CompletedGroupAlgebraIndexInClass H C) :=
    ⟨_root_.CompletedGroupAlgebra.terminalCompletedGroupAlgebraIndexInClass (G := H) C⟩
  let : Nonempty (ZCCompletedGroupAlgebraIndex C H) := inferInstance
  let S := zcCompletedGroupAlgebraMultiplicativeSystem C H
  let : ∀ i : ZCCompletedGroupAlgebraIndex C H, Group (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraMultiplicativeSystem]
    infer_instance
  let : ∀ i : ZCCompletedGroupAlgebraIndex C H, IsTopologicalGroup (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraMultiplicativeSystem]
    exact instIsTopologicalGroupZCCompletedGroupAlgebraMultiplicativeSystemStage C H i
  let : ∀ i : ZCCompletedGroupAlgebraIndex C H, CompactSpace (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraMultiplicativeSystem]
    change @CompactSpace (Multiplicative (ZCCompletedGroupAlgebraStage C H i)) ⊥
    exact @Finite.compactSpace
      (Multiplicative (ZCCompletedGroupAlgebraStage C H i)) ⊥
      (instFiniteZCCompletedGroupAlgebraMultiplicativeSystemStage C H i)
  let : ∀ i : ZCCompletedGroupAlgebraIndex C H, T2Space (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraMultiplicativeSystem]
    change @T2Space (Multiplicative (ZCCompletedGroupAlgebraStage C H i)) ⊥
    exact @DiscreteTopology.toT2Space _ ⊥ ⟨rfl⟩
  let : ∀ i : ZCCompletedGroupAlgebraIndex C H, TotallyDisconnectedSpace (S.X i) := fun i => by
    dsimp [S, zcCompletedGroupAlgebraMultiplicativeSystem]
    change @TotallyDisconnectedSpace
      (Multiplicative (ZCCompletedGroupAlgebraStage C H i)) ⊥
    exact @TotallySeparatedSpace.totallyDisconnectedSpace _ ⊥
      (@TotallySeparatedSpace.of_discrete _ ⊥ ⟨rfl⟩)
  let : ProCGroups.InverseSystems.IsGroupSystem S := by
    dsimp [S]
    infer_instance
  have hS : ProCGroups.ProC.HasOpenNormalBasisInClass C (S.inverseLimit) := by
    exact ProCGroups.ProC.inverseLimit (S := S)
      hForm.isomClosed hForm.quotientClosed
      (directed_zcCompletedGroupAlgebraIndex_of_formation C H hForm)
      (fun i => by
        dsimp [S, zcCompletedGroupAlgebraMultiplicativeSystem]
        let : Fact (0 < i.1.modulus) := ⟨i.1.positive⟩
        let : Finite (ZCCompletedGroupAlgebraStage C H i) :=
          finite_modNCompletedGroupAlgebraStageInClass
            (n := i.1.modulus) (G := H) C
            i.2
        let : Finite (Multiplicative (ZCCompletedGroupAlgebraStage C H i)) :=
          @Finite.of_equiv _ _ (inferInstance : Finite (ZCCompletedGroupAlgebraStage C H i))
            Multiplicative.toAdd
        let : DiscreteTopology (Multiplicative (ZCCompletedGroupAlgebraStage C H i)) := ⟨rfl⟩
        exact ProCGroups.ProC.HasOpenNormalBasisInClass.of_finite_discrete (C := C)
          (G := Multiplicative (ZCCompletedGroupAlgebraStage C H i))
          hForm.quotientClosed
          (finiteGroupClass_multiplicative_modNCompletedGroupAlgebraStageInClass_mem
            C H hForm.isomClosed hForm.finiteProductClosed i.1 i.2))
  exact ProCGroups.ProC.HasOpenNormalBasisInClass.ofContinuousMulEquiv (C := C) hS
    (zcCompletedGroupAlgebraMultiplicativeLimitEquiv C H)

variable (X : Type u)

/--
Coordinatewise, the multiplicative version of an additive function group is the product of the
multiplicative coordinate groups.
-/
def multiplicativePiContinuousMulEquiv
    (A : Type u) [AddCommGroup A] [TopologicalSpace A] :
    Multiplicative (X → A) ≃ₜ* (X → Multiplicative A) where
  toMulEquiv :=
    { toFun := fun f x => Multiplicative.ofAdd (f.toAdd x)
      invFun := fun f => Multiplicative.ofAdd fun x => (f x).toAdd
      left_inv := by
        intro f
        rfl
      right_inv := by
        intro f
        rfl
      map_mul' := by
        intro f g
        rfl }
  continuous_toFun := by
    exact continuous_pi fun x =>
      continuous_ofAdd.comp ((continuous_apply x).comp continuous_toAdd)
  continuous_invFun := by
    exact continuous_ofAdd.comp
      (continuous_pi fun x => continuous_toAdd.comp (continuous_apply x))

/-- The additive Fox-coordinate group \(\mathbb{Z}_C\llbracket H\rrbracket^{X}\), written
multiplicatively, has an open-normal \(C\)-basis. -/
theorem hasOpenNormalBasisInClass_multiplicative_zcFreeFoxCoordinates
    (hForm : ProCGroups.FiniteGroupClass.Formation C) : ProCGroups.ProC.HasOpenNormalBasisInClass C
      (Multiplicative (ZCFreeFoxCoordinates C (X := X) (H := H))) := by
  let : T2Space (Multiplicative (ZCCompletedGroupAlgebra C H)) := by
    change T2Space (ZCCompletedGroupAlgebra C H)
    infer_instance
  let : TotallyDisconnectedSpace
      (Multiplicative (ZCCompletedGroupAlgebra C H)) := by
    change TotallyDisconnectedSpace (ZCCompletedGroupAlgebra C H)
    infer_instance
  have hPi : ProCGroups.ProC.HasOpenNormalBasisInClass C
        (X → Multiplicative (ZCCompletedGroupAlgebra C H)) :=
    ProCGroups.ProC.HasOpenNormalBasisInClass.pi
      (C := C) (α := X)
      (β := fun _ => Multiplicative (ZCCompletedGroupAlgebra C H))
      hForm
      (fun _ => hasOpenNormalBasisInClass_multiplicative_zcCompletedGroupAlgebra
        (C := C) (H := H) hForm)
  exact ProCGroups.ProC.HasOpenNormalBasisInClass.ofContinuousMulEquiv (C := C) hPi
    (multiplicativePiContinuousMulEquiv (X := X)
      (A := ZCCompletedGroupAlgebra C H)).symm

end CompletedGroupAlgebraProC

section SemidirectProC

variable (C : ProCGroups.FiniteGroupClass.{u})
variable (X H : Type u) [DecidableEq X]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The kernel of the right projection \(\mathbb{Z}_C\llbracket H\rrbracket^{X} \rtimes H \to H\) is
the additive coordinate group, written multiplicatively.
-/
def zcCompletedFoxSemidirectRightKernelEquivCoordinates :
    ((ZCCompletedFoxSemidirect.rightMonoidHom C X H).ker :
        Subgroup (ZCCompletedFoxSemidirect C X H)) ≃ₜ*
      Multiplicative (ZCFreeFoxCoordinates C (X := X) (H := H)) where
  toMulEquiv :=
    { toFun := fun a => Multiplicative.ofAdd a.1.left
      invFun := fun v =>
        ⟨{ left := v.toAdd, right := 1 }, by
          simp only [ZCCompletedFoxSemidirect.rightMonoidHom, MonoidHom.mem_ker,
              MonoidHom.coe_mk, OneHom.coe_mk]⟩
      left_inv := by
        intro a
        apply Subtype.ext
        apply ZCCompletedFoxSemidirect.ext
        · rfl
        · change (1 : H) = a.1.right
          exact a.2.symm
      right_inv := by
        intro v
        rfl
      map_mul' := by
        intro a b
        apply Multiplicative.ext
        have ha : a.1.right = 1 := by
          exact a.2
        simp only [Subgroup.coe_mul, ZCCompletedFoxSemidirect.mul_left, ha, map_one, one_smul,
            ofAdd_add, toAdd_mul,
  toAdd_ofAdd]}
  continuous_toFun := by
    exact continuous_ofAdd.comp
      ((continuous_zcCompletedFoxSemidirect_left C X H).comp continuous_subtype_val)
  continuous_invFun := by
    refine Continuous.subtype_mk ?_ (fun v => by
      simp only [ZCCompletedFoxSemidirect.rightMonoidHom, MonoidHom.mem_ker, MonoidHom.coe_mk,
          OneHom.coe_mk])
    rw [continuous_induced_rng]
    exact continuous_toAdd.prodMk continuous_const

omit [DecidableEq X] in
/-- The right-projection kernel in the completed Fox semidirect product has an open-normal
\(C\)-basis. -/
theorem hasOpenNormalBasisInClass_zcCompletedFoxSemidirect_rightKernel
    (hForm : ProCGroups.FiniteGroupClass.Formation C) : ProCGroups.ProC.HasOpenNormalBasisInClass C
      ((ZCCompletedFoxSemidirect.rightMonoidHom C X H).ker :
        Subgroup (ZCCompletedFoxSemidirect C X H)) := by
  have hcoords : ProCGroups.ProC.HasOpenNormalBasisInClass C
        (Multiplicative (ZCFreeFoxCoordinates C (X := X) (H := H))) :=
    hasOpenNormalBasisInClass_multiplicative_zcFreeFoxCoordinates (C := C) (X := X) (H := H) hForm
  exact ProCGroups.ProC.HasOpenNormalBasisInClass.ofContinuousMulEquiv (C := C) hcoords
    (zcCompletedFoxSemidirectRightKernelEquivCoordinates C X H).symm

omit [DecidableEq X] in
/-- The completed Fox semidirect target
\(\mathbb{Z}_C\llbracket H\rrbracket^{X} \rtimes H\) has an open-normal \(C\)-basis when \(H\)
does. -/
theorem hasOpenNormalBasisInClass_zcCompletedFoxSemidirect_of_hasOpenNormalBasisInClass
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hMel : ProCGroups.FiniteGroupClass.MelnikovFormation C)
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H)) :
        ProCGroups.ProC.HasOpenNormalBasisInClass C (ZCCompletedFoxSemidirect C X H) := by
  let E := ZCCompletedFoxSemidirect C X H
  let f : E →ₜ* H :=
    { toMonoidHom := ZCCompletedFoxSemidirect.rightMonoidHom C X H
      continuous_toFun := continuous_zcCompletedFoxSemidirect_right C X H }
  let K : Subgroup E := f.toMonoidHom.ker
  have hK : ProCGroups.ProC.HasOpenNormalBasisInClass C (K) := by
    dsimp [K, f, E]
    exact hasOpenNormalBasisInClass_zcCompletedFoxSemidirect_rightKernel
      (C := C) (X := X) (H := H) hMel.formation
  have hQ : ProCGroups.ProC.HasOpenNormalBasisInClass C (E ⧸ K) := by
    have hf_surj : Function.Surjective f := by
      intro h
      exact ⟨{ left := 0, right := h }, rfl⟩
    let eQuotRange : (E ⧸ K) ≃ₜ* f.toMonoidHom.range := by
      simpa [K] using ProCGroups.ContinuousMonoidHom.quotientKerContinuousMulEquivRange f
    let eRangeH : f.toMonoidHom.range ≃ₜ* H :=
      { toMulEquiv :=
          { toFun := fun x => x.1
            invFun := fun h => ⟨h, hf_surj h⟩
            left_inv := by
              intro x
              exact Subtype.ext rfl
            right_inv := by
              intro h
              rfl
            map_mul' := by
              intro x y
              rfl }
        continuous_toFun := continuous_subtype_val
        continuous_invFun := Continuous.subtype_mk continuous_id (fun h => hf_surj h) }
    exact ProCGroups.ProC.HasOpenNormalBasisInClass.ofContinuousMulEquiv (C := C) hH
      (eRangeH.symm.trans eQuotRange.symm)
  exact ProCGroups.ProC.HasOpenNormalBasisInClass.extension (C := C)
    hMel.formation.isomClosed hMel.formation.quotientClosed hMel.extensionClosed
    K (ProCGroups.ContinuousMonoidHom.isClosed_ker f) hK hQ

end SemidirectProC

end

end FoxDifferential
