import ProCGroups.CompletedGroupAlgebra.Basic.ClassComparison

set_option autoImplicit false

/-!
# Completed Group Algebra / Open Finite Quotient Topology / Canonical Maps

This module constructs the canonical dense maps from the abstract group algebra to the
\(C\)-indexed and all-finite named completions, together with their bundled ring, algebra, and
linear forms and finite-stage characterizations.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems
open ProCGroups.Completion

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The quotient map from the abstract group algebra \(R[G]\) to one \(C\)-indexed finite stage. -/
def completedGroupAlgebraStageMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (R : Type u) (G : Type v) [CommRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : CompletedGroupAlgebraIndexInClass G C) :
    MonoidAlgebra R G →+* CompletedGroupAlgebraStageInClass C R G U :=
  MonoidAlgebra.mapDomainRingHom R
    (openNormalSubgroupInClassProj (C := C) (G := G) U)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
At a \(C\)-indexed stage \(U\), the quotient map sends the group-like element of \(g\) to the
singleton at the image of \(g\) in \(G/U\), with coefficient \(1\).
-/
@[simp]
theorem completedGroupAlgebraStageMapInClass_of
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (g : G) :
    completedGroupAlgebraStageMapInClass C R G U (MonoidAlgebra.of R G g) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U g) 1 := by
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj (C := C) (G := G) U)
        (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single
        (openNormalSubgroupInClassProj (C := C) (G := G) U g) 1
  exact MonoidAlgebra.mapDomain_single

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
At a \(C\)-indexed stage \(U\), the quotient map sends the singleton at \(g\) with coefficient
\(r\) to the singleton at the image of \(g\) in \(G/U\), with coefficient \(r\).
-/
theorem completedGroupAlgebraStageMapInClass_single
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (g : G) (r : R) :
    completedGroupAlgebraStageMapInClass C R G U (MonoidAlgebra.single g r) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U g) r := by
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj (C := C) (G := G) U)
        (MonoidAlgebra.single g r) =
      MonoidAlgebra.single
        (openNormalSubgroupInClassProj (C := C) (G := G) U g) r
  exact MonoidAlgebra.mapDomain_single

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The \(C\)-indexed quotient-stage map preserves scalar multiplication by elements of \(R\). -/
theorem completedGroupAlgebraStageMapInClass_smul
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (r : R) (x : MonoidAlgebra R G) :
    completedGroupAlgebraStageMapInClass C R G U (r • x) =
      r • completedGroupAlgebraStageMapInClass C R G U x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj (C := C) (G := G) U)
        (MonoidAlgebra.single 1 r) =
      MonoidAlgebra.single 1 r
  rw [MonoidAlgebra.mapDomain_single,
    (openNormalSubgroupInClassProj (C := C) (G := G) U).map_one]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The \(C\)-indexed quotient-stage map commutes with the canonical embeddings of scalars from
\(R\).
-/
theorem completedGroupAlgebraStageMapInClass_algebraMap
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C)
    (r : R) :
    completedGroupAlgebraStageMapInClass C R G U (algebraMap R (MonoidAlgebra R G) r) =
      algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r := by
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj (C := C) (G := G) U)
        (MonoidAlgebra.single 1 r) =
      MonoidAlgebra.single 1 r
  rw [MonoidAlgebra.mapDomain_single,
    (openNormalSubgroupInClassProj (C := C) (G := G) U).map_one]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The quotient map \(R[G]\to R[G/U]\) is surjective for every \(C\)-indexed stage \(U\). -/
theorem completedGroupAlgebraStageMapInClass_surjective
    (C : ProCGroups.FiniteGroupClass.{v}) (U : CompletedGroupAlgebraIndexInClass G C) :
    Function.Surjective (completedGroupAlgebraStageMapInClass C R G U) := by
  classical
  intro x
  obtain ⟨y, hy⟩ :=
    Finsupp.mapDomain_surjective (M := R)
      (openNormalSubgroupInClassProj_surjective (C := C) (G := G) U) x.coeff
  refine ⟨MonoidAlgebra.ofCoeff y, ?_⟩
  apply MonoidAlgebra.coeff_injective
  exact hy

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The class-restricted completed group-algebra stage map is compatible with transition maps and
coordinate projections for the completed group algebra.
-/
@[simp]
theorem completedGroupAlgebraStageMapInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{v})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    (completedGroupAlgebraTransitionInClass C R G hUV).comp
        (completedGroupAlgebraStageMapInClass C R G V) =
      completedGroupAlgebraStageMapInClass C R G U := by
  unfold completedGroupAlgebraTransitionInClass completedGroupAlgebraStageMapInClass
  have hproj :
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV).comp
          (openNormalSubgroupInClassProj (C := C) (G := G) V) =
        openNormalSubgroupInClassProj (C := C) (G := G) U := by
    ext g
    exact congrFun
      (openNormalSubgroupInClassProj_compatible
        (C := C) (G := G) U V hUV) g
  exact
    (MonoidAlgebra.mapDomainRingHom_comp (R := R)
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
      (openNormalSubgroupInClassProj (C := C) (G := G) V)).symm.trans
      (congrArg (MonoidAlgebra.mapDomainRingHom R) hproj)

/-- The \(C\)-indexed finite-stage quotient maps form a compatible family. -/
theorem completedGroupAlgebraStageMapInClass_compatibleMaps
    (C : ProCGroups.FiniteGroupClass.{v}) :
    (completedGroupAlgebraSystemInClass C R G).CompatibleMaps
      (fun U => completedGroupAlgebraStageMapInClass C R G U) := by
  intro U V hUV
  funext x
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraStageMapInClass_compatible (R := R) (G := G) C hUV))
    x

/--
The canonical map \(R[G] \to \widehat{R[G]}_C\), obtained from all \(C\)-indexed quotient maps.
-/
def toCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (x : MonoidAlgebra R G) : CompletedGroupAlgebraInClass C R G :=
  (completedGroupAlgebraInClassCompatibleFamilyEquiv
    (R := R) (G := G) C).symm
    ((completedGroupAlgebraSystemInClass C R G).inverseLimitLift
      (fun U => completedGroupAlgebraStageMapInClass C R G U)
      (completedGroupAlgebraStageMapInClass_compatibleMaps
        (R := R) (G := G) C) x)

/--
The \(U\)-coordinate of the canonical dense element in the \(C\)-indexed completion is the
\(C\)-indexed stage map at \(U\).
-/
@[simp]
theorem completedGroupAlgebraProjectionInClass_toCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) (x : MonoidAlgebra R G) :
    completedGroupAlgebraProjectionInClass C R G U
        (toCompletedGroupAlgebraInClass C R G x) =
      completedGroupAlgebraStageMapInClass C R G U x :=
  rfl

/--
The canonical map from \(R[G]\) into the \(C\)-indexed completed group algebra preserves scalar
multiplication by \(R\).
-/
@[simp]
theorem toCompletedGroupAlgebraInClass_smul
    (C : ProCGroups.FiniteGroupClass.{v})
    (r : R) (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebraInClass C R G (r • x) =
      r • toCompletedGroupAlgebraInClass C R G x := by
  apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
  intro U
  change completedGroupAlgebraStageMapInClass C R G U (r • x) =
    r • completedGroupAlgebraStageMapInClass C R G U x
  exact completedGroupAlgebraStageMapInClass_smul (R := R) (G := G) C U r x

/-- The canonical map \(R[G] \to \widehat{R[G]}_C\) is bundled as a ring homomorphism. -/
def toCompletedGroupAlgebraInClassRingHom
    (C : ProCGroups.FiniteGroupClass.{v})
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    MonoidAlgebra R G →+* CompletedGroupAlgebraInClass C R G where
  toFun := toCompletedGroupAlgebraInClass C R G
  map_zero' := by
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    exact map_zero (completedGroupAlgebraStageMapInClass C R G U)
  map_one' := by
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    exact map_one (completedGroupAlgebraStageMapInClass C R G U)
  map_add' x y := by
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    exact map_add (completedGroupAlgebraStageMapInClass C R G U) x y
  map_mul' x y := by
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    exact map_mul (completedGroupAlgebraStageMapInClass C R G U) x y

/--
The bundled ring homomorphism has the same underlying function as the coordinatewise
construction.
-/
@[simp]
theorem toCompletedGroupAlgebraInClassRingHom_apply
    (C : ProCGroups.FiniteGroupClass.{v})
    (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebraInClassRingHom C R G x =
      toCompletedGroupAlgebraInClass C R G x :=
  rfl

/-- The canonical map \(R[G] \to \widehat{R[G]}_C\), as an algebra homomorphism. -/
def toCompletedGroupAlgebraInClassAlgHom
    (C : ProCGroups.FiniteGroupClass.{v})
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    MonoidAlgebra R G →ₐ[R] CompletedGroupAlgebraInClass C R G where
  toRingHom := toCompletedGroupAlgebraInClassRingHom C R G
  commutes' := by
    intro r
    apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
    intro U
    change completedGroupAlgebraStageMapInClass C R G U
        (algebraMap R (MonoidAlgebra R G) r) =
      algebraMap R (CompletedGroupAlgebraStageInClass C R G U) r
    exact completedGroupAlgebraStageMapInClass_algebraMap (R := R) (G := G) C U r

/--
Evaluating the canonical \(C\)-indexed algebra homomorphism gives the coordinatewise dense map
`toCompletedGroupAlgebraInClass`.
-/
@[simp]
theorem toCompletedGroupAlgebraInClassAlgHom_apply
    (C : ProCGroups.FiniteGroupClass.{v})
    (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebraInClassAlgHom C R G x =
      toCompletedGroupAlgebraInClass C R G x :=
  rfl

/-- The canonical map \(R[G] \to \widehat{R[G]}_C\), as a linear map. -/
def toCompletedGroupAlgebraInClassLinearMap
    (C : ProCGroups.FiniteGroupClass.{v})
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    MonoidAlgebra R G →ₗ[R] CompletedGroupAlgebraInClass C R G where
  toFun := toCompletedGroupAlgebraInClass C R G
  map_add' := by
    intro x y
    exact map_add (toCompletedGroupAlgebraInClassRingHom C R G) x y
  map_smul' := toCompletedGroupAlgebraInClass_smul (R := R) (G := G) C

/-- The bundled linear map has the same underlying function as the coordinatewise construction. -/
@[simp]
theorem toCompletedGroupAlgebraInClassLinearMap_apply
    (C : ProCGroups.FiniteGroupClass.{v})
    (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebraInClassLinearMap C R G x =
      toCompletedGroupAlgebraInClass C R G x :=
  rfl

/--
Composing the \(U\)-coordinate projection from the \(C\)-indexed completion with its canonical
dense ring homomorphism gives the \(C\)-indexed stage map at \(U\).
-/
@[simp]
theorem completedGAProjectionInClass_comp_toCompletedGAInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (U : CompletedGroupAlgebraIndexInClass G C) :
    (completedGroupAlgebraProjectionInClass C R G U).comp
        (toCompletedGroupAlgebraInClassRingHom C R G) =
      completedGroupAlgebraStageMapInClass C R G U := by
  apply RingHom.ext
  intro x
  rfl

/--
The abstract group algebra is dense in the \(C\)-indexed completed group algebra when \(G\) is
pro-\(C\) and \(C\) is a formation.
-/
theorem denseRange_toCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    DenseRange (toCompletedGroupAlgebraInClass C R G) := by
  let S := completedGroupAlgebraSystemInClass C R G
  let : Nonempty (OpenNormalSubgroupInClass C G) :=
    HasOpenNormalBasisInClass.openNormalSubgroupInClass_nonempty hG
  let : Nonempty (CompletedGroupAlgebraIndexInClass G C) := inferInstance
  have hdir :
      Directed (α := CompletedGroupAlgebraIndexInClass G C) (· ≤ ·) fun U => U :=
    directed_openNormalSubgroupInClass (C := C) (G := G) hForm
  have hdense :
      DenseRange
        (S.inverseLimitLift
          (fun U : CompletedGroupAlgebraIndexInClass G C =>
            completedGroupAlgebraStageMapInClass C R G U)
          (completedGroupAlgebraStageMapInClass_compatibleMaps (R := R) (G := G) C )) :=
    S.denseRange_lift
      (fun U : CompletedGroupAlgebraIndexInClass G C =>
        completedGroupAlgebraStageMapInClass C R G U)
      (completedGroupAlgebraStageMapInClass_compatibleMaps (R := R) (G := G) C )
      (fun U => completedGroupAlgebraStageMapInClass_surjective (R := R) (G := G) C U)
      hdir
  change DenseRange
    (S.inverseLimitLift
      (fun U : CompletedGroupAlgebraIndexInClass G C =>
        completedGroupAlgebraStageMapInClass C R G U)
      (completedGroupAlgebraStageMapInClass_compatibleMaps (R := R) (G := G) C))
  exact hdense

/--
Projecting to a finer stage \(V\) and then applying the transition to \(U\) agrees with projecting
directly to \(U\).
-/
@[simp]
theorem completedGroupAlgebraTransition_comp_projection
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (completedGroupAlgebraTransition R G hUV).comp
        (completedGroupAlgebraProjection R G V) =
      completedGroupAlgebraProjection R G U := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraProjection_compatible (R := R) (G := G) x hUV

/-- The quotient map from the abstract group algebra \(R[G]\) to one finite stage \(R[G/U]\). -/
def completedGroupAlgebraStageMap (R : Type u) (G : Type v) [CommRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] (U : CompletedGroupAlgebraIndex G) :
    MonoidAlgebra R G →+* CompletedGroupAlgebraStage R G U :=
  MonoidAlgebra.mapDomainRingHom R
    (openNormalSubgroupInClassProj
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
At an all-finite stage \(U\), the quotient map sends the group-like element of \(g\) to the
singleton at the image of \(g\) in \(G/U\), with coefficient \(1\).
-/
@[simp]
theorem completedGroupAlgebraStageMap_of
    (U : CompletedGroupAlgebraIndex G) (g : G) :
    completedGroupAlgebraStageMap R G U (MonoidAlgebra.of R G g) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) 1 := by
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)
        (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) 1
  exact MonoidAlgebra.mapDomain_single

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
At an all-finite stage \(U\), the quotient map sends the singleton at \(g\) with coefficient \(r\)
to the singleton at the image of \(g\) in \(G/U\), with coefficient \(r\).
-/
theorem completedGroupAlgebraStageMap_single
    (U : CompletedGroupAlgebraIndex G) (g : G) (r : R) :
    completedGroupAlgebraStageMap R G U (MonoidAlgebra.single g r) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) r := by
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)
        (MonoidAlgebra.single g r) =
      MonoidAlgebra.single
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) r
  exact MonoidAlgebra.mapDomain_single

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The all-finite quotient-stage map preserves scalar multiplication by elements of \(R\). -/
theorem completedGroupAlgebraStageMap_smul
    (U : CompletedGroupAlgebraIndex G) (r : R) (x : MonoidAlgebra R G) :
    completedGroupAlgebraStageMap R G U (r • x) =
      r • completedGroupAlgebraStageMap R G U x := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul]
  congr 1
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)
        (MonoidAlgebra.single 1 r) =
      MonoidAlgebra.single 1 r
  rw [MonoidAlgebra.mapDomain_single,
    (openNormalSubgroupInClassProj
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U).map_one]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The all-finite quotient-stage map commutes with the canonical embeddings of scalars from \(R\).
-/
theorem completedGroupAlgebraStageMap_algebraMap
    (U : CompletedGroupAlgebraIndex G) (r : R) :
    completedGroupAlgebraStageMap R G U (algebraMap R (MonoidAlgebra R G) r) =
      algebraMap R (CompletedGroupAlgebraStage R G U) r := by
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)
        (MonoidAlgebra.single 1 r) =
      MonoidAlgebra.single 1 r
  rw [MonoidAlgebra.mapDomain_single,
    (openNormalSubgroupInClassProj
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U).map_one]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The quotient map \(R[G]\to R[G/U]\) is surjective for every all-finite stage \(U\). -/
theorem completedGroupAlgebraStageMap_surjective (U : CompletedGroupAlgebraIndex G) :
    Function.Surjective (completedGroupAlgebraStageMap R G U) := by
  classical
  intro x
  obtain ⟨y, hy⟩ :=
    Finsupp.mapDomain_surjective (M := R)
      (openNormalSubgroupInClassProj_surjective
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U) x.coeff
  refine ⟨MonoidAlgebra.ofCoeff y, ?_⟩
  apply MonoidAlgebra.coeff_injective
  exact hy

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The completed group-algebra stage map is compatible with transition maps and coordinate
projections for the completed group algebra.
-/
@[simp]
theorem completedGroupAlgebraStageMap_compatible
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (completedGroupAlgebraTransition R G hUV).comp (completedGroupAlgebraStageMap R G V) =
      completedGroupAlgebraStageMap R G U := by
  unfold completedGroupAlgebraTransition completedGroupAlgebraStageMap
  have hproj :
      (OpenNormalSubgroupInClass.map
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV).comp
          (openNormalSubgroupInClassProj
            (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) V) =
        openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U := by
    ext g
    exact congrFun
      (openNormalSubgroupInClassProj_compatible
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U V hUV) g
  exact
    (MonoidAlgebra.mapDomainRingHom_comp (R := R)
      (OpenNormalSubgroupInClass.map
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
      (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) V)).symm.trans
      (congrArg (MonoidAlgebra.mapDomainRingHom R) hproj)

/--
The finite-stage quotient maps form a compatible family into the completed group algebra system.
-/
theorem completedGroupAlgebraStageMap_compatibleMaps :
    (completedGroupAlgebraSystem R G).CompatibleMaps
      (fun U => completedGroupAlgebraStageMap R G U) := by
  intro U V hUV
  funext x
  exact congrFun
    (congrArg DFunLike.coe
      (completedGroupAlgebraStageMap_compatible (R := R) (G := G) (U := U) (V := V) hUV))
    x

/--
The canonical map \(R[G] \to \widehat{R[G]}\), obtained from all quotient maps \(R[G]\to
R[G/U]\).
-/
def toCompletedGroupAlgebra (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (x : MonoidAlgebra R G) : CompletedGroupAlgebraCarrier R G :=
  (completedGroupAlgebraCompatibleFamilyEquiv (R := R) (G := G)).symm
    ((completedGroupAlgebraSystem R G).inverseLimitLift
      (fun U => completedGroupAlgebraStageMap R G U)
      (completedGroupAlgebraStageMap_compatibleMaps (R := R) (G := G)) x)

/--
The \(U\)-coordinate of the canonical dense element in the all-finite completion is the
all-finite stage map at \(U\).
-/
@[simp]
theorem completedGroupAlgebraProjection_toCompletedGroupAlgebra
    (U : CompletedGroupAlgebraIndex G) (x : MonoidAlgebra R G) :
    completedGroupAlgebraProjection R G U (toCompletedGroupAlgebra R G x) =
      completedGroupAlgebraStageMap R G U x := rfl

/--
The canonical map from \(R[G]\) into the all-finite completed group algebra preserves scalar
multiplication by \(R\).
-/
@[simp]
theorem toCompletedGroupAlgebra_smul (r : R) (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebra R G (r • x) =
      r • toCompletedGroupAlgebra R G x := by
  apply completedGroupAlgebra_ext (R := R) (G := G)
  intro U
  calc
    completedGroupAlgebraProjection R G U
        (toCompletedGroupAlgebra R G (r • x)) =
      completedGroupAlgebraStageMap R G U (r • x) :=
        completedGroupAlgebraProjection_toCompletedGroupAlgebra
          (R := R) (G := G) U (r • x)
    _ = r • completedGroupAlgebraStageMap R G U x :=
      completedGroupAlgebraStageMap_smul (R := R) (G := G) U r x
    _ = r • completedGroupAlgebraProjection R G U
        (toCompletedGroupAlgebra R G x) := by
      rw [completedGroupAlgebraProjection_toCompletedGroupAlgebra]
    _ = completedGroupAlgebraProjection R G U
        (r • toCompletedGroupAlgebra R G x) :=
      ((completedGroupAlgebraProjectionAlgHom R G U).toLinearMap.map_smul
        r (toCompletedGroupAlgebra R G x)).symm

/-- The canonical map \(R[G] \to \widehat{R[G]}\) is bundled as a ring homomorphism. -/
def toCompletedGroupAlgebraRingHom (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    MonoidAlgebra R G →+* CompletedGroupAlgebraCarrier R G where
  toFun := toCompletedGroupAlgebra R G
  map_zero' := by
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    exact map_zero (completedGroupAlgebraStageMap R G U)
  map_one' := by
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    exact map_one (completedGroupAlgebraStageMap R G U)
  map_add' x y := by
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    exact map_add (completedGroupAlgebraStageMap R G U) x y
  map_mul' x y := by
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    exact map_mul (completedGroupAlgebraStageMap R G U) x y

/--
Restricting the all-finite completion to its \(C\)-indexed coordinates after applying the
all-finite dense map agrees with the canonical \(C\)-indexed dense map.
-/
@[simp]
theorem completedGroupAlgebraToInClass_comp_toCompletedGroupAlgebra
    (C : ProCGroups.FiniteGroupClass.{v}) :
    (completedGroupAlgebraToInClassRingHom (R := R) (G := G) C ).comp
        (toCompletedGroupAlgebraRingHom R G) =
      toCompletedGroupAlgebraInClassRingHom C R G := by
  apply RingHom.ext
  intro x
  apply completedGroupAlgebraInClass_ext (R := R) (G := G) C
  intro U
  rfl

/--
Under the formation and pro-\(C\) hypotheses, transporting the \(C\)-indexed dense map back to the
all-finite completion recovers the all-finite dense map.
-/
@[simp]
theorem completedGroupAlgebraFromInClassRingHom_comp_toCompletedGroupAlgebraInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    (completedGroupAlgebraFromInClassRingHom (R := R) (G := G) C hForm hG).comp
        (toCompletedGroupAlgebraInClassRingHom C R G) =
      toCompletedGroupAlgebraRingHom R G := by
  rw [← completedGroupAlgebraToInClass_comp_toCompletedGroupAlgebra (R := R) (G := G) C ,
    ← RingHom.comp_assoc, completedGroupAlgebraFromInClassRingHom_comp_toInClassRingHom]
  rfl

/-- The canonical map \(R[G] \to \widehat{R[G]}\) as an \(R\)-algebra homomorphism. -/
def toCompletedGroupAlgebraAlgHom (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    MonoidAlgebra R G →ₐ[R] CompletedGroupAlgebraCarrier R G where
  toRingHom := toCompletedGroupAlgebraRingHom R G
  commutes' := by
    intro r
    apply completedGroupAlgebra_ext (R := R) (G := G)
    intro U
    change completedGroupAlgebraStageMap R G U (algebraMap R (MonoidAlgebra R G) r) =
      algebraMap R (CompletedGroupAlgebraStage R G U) r
    exact completedGroupAlgebraStageMap_algebraMap (R := R) (G := G) U r

/-- The canonical map \(R[G] \to \widehat{R[G]}\) as an \(R\)-linear map. -/
def toCompletedGroupAlgebraLinearMap (R : Type u) (G : Type v) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] :
    MonoidAlgebra R G →ₗ[R] CompletedGroupAlgebraCarrier R G where
  toFun := toCompletedGroupAlgebra R G
  map_add' := by
    intro x y
    exact map_add (toCompletedGroupAlgebraRingHom R G) x y
  map_smul' := toCompletedGroupAlgebra_smul (R := R) (G := G)

/--
Composing the \(U\)-coordinate projection from the all-finite completion with its canonical dense
ring homomorphism gives the all-finite stage map at \(U\).
-/
@[simp]
theorem completedGroupAlgebraProjection_comp_toCompletedGroupAlgebra
    (U : CompletedGroupAlgebraIndex G) :
    (completedGroupAlgebraProjection R G U).comp
        (toCompletedGroupAlgebraRingHom R G) =
      completedGroupAlgebraStageMap R G U := by
  apply RingHom.ext
  intro x
  exact completedGroupAlgebraProjection_toCompletedGroupAlgebra (R := R) (G := G) U x

omit G [Group G] [TopologicalSpace G] [IsTopologicalGroup G] in
end

end CompletedGroupAlgebra
