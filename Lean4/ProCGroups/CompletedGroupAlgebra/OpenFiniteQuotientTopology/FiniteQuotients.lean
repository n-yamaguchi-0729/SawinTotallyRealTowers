import ProCGroups.CompletedGroupAlgebra.OpenFiniteQuotientTopology.CanonicalMaps

set_option autoImplicit false

/-!
# Finite coefficient-and-group quotients

This file constructs the finite group-algebra stages obtained by quotienting both coefficients
and the group. It develops their quotient maps, kernels, transition maps, basis formulas,
continuity, and surjectivity.
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

/--
An open coefficient ideal gives a continuous quotient map when the quotient is equipped with the
discrete topology. This is the coefficient-side continuity used in Ribes--Zalesskii Section
\(5.3\).
-/
theorem continuous_idealQuotient_mk_openIdeal_discrete
    (I : Ideal R) (hI : IsOpen (I : Set R)) :
    letI : TopologicalSpace (R ⧸ I) := ⊥
    Continuous (Ideal.Quotient.mk I) := by
  let : TopologicalSpace (R ⧸ I) := ⊥
  have : DiscreteTopology (R ⧸ I) := ⟨rfl⟩
  rw [continuous_discrete_rng]
  intro b
  rcases Ideal.Quotient.mk_surjective (I := I) b with ⟨a, rfl⟩
  have hpre :
      (Ideal.Quotient.mk I) ⁻¹' ({Ideal.Quotient.mk I a} : Set (R ⧸ I)) =
        (fun x : R => x - a) ⁻¹' (I : Set R) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Ideal.Quotient.eq, SetLike.mem_coe]
  rw [hpre]
  exact hI.preimage (continuous_id.sub continuous_const)

omit G [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [IsTopologicalRing R] in
/-- Finite-stage group algebras are functorial in the coefficient ring by continuous maps. -/
theorem finiteGroupAlgebra_mapRangeRingHom_continuous
    (S : Type u) [CommRing S] [TopologicalSpace S]
    (Q : Type v) [Group Q] [Finite Q]
    (f : R →+* S) (hf : Continuous f) :
    letI : TopologicalSpace (MonoidAlgebra R Q) := finiteGroupAlgebraTopology R Q
    letI : TopologicalSpace (MonoidAlgebra S Q) := finiteGroupAlgebraTopology S Q
    Continuous (MonoidAlgebra.mapRingHom Q f :
      MonoidAlgebra R Q → MonoidAlgebra S Q) := by
  classical
  let : Fintype Q := Fintype.ofFinite Q
  let : TopologicalSpace (MonoidAlgebra R Q) := finiteGroupAlgebraTopology R Q
  let : TopologicalSpace (MonoidAlgebra S Q) := finiteGroupAlgebraTopology S Q
  let eS : MonoidAlgebra S Q ≃ (Q → S) :=
    MonoidAlgebra.coeffEquiv.trans Finsupp.equivFunOnFinite
  have heS : Topology.IsInducing (eS : MonoidAlgebra S Q → Q → S) :=
    Topology.IsInducing.induced eS
  have hcoordR : ∀ q : Q, Continuous fun x : MonoidAlgebra R Q => x.coeff q := by
    intro q
    exact finiteGroupAlgebra_coordinate_continuous R Q q
  rw [heS.continuous_iff]
  apply continuous_pi
  intro q
  change Continuous fun x : MonoidAlgebra R Q =>
    (MonoidAlgebra.mapRingHom Q f x : MonoidAlgebra S Q).coeff q
  change Continuous (f ∘ fun x : MonoidAlgebra R Q => x.coeff q)
  exact hf.comp (hcoordR q)

omit R G [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] in
/--
If the coefficient ring is discrete, then the finite-stage group algebra has the discrete
finite-product topology.
-/
theorem finiteGroupAlgebraTopology_discrete_of_discrete_coeff
    (S : Type u) [CommRing S] [TopologicalSpace S] [DiscreteTopology S]
    (Q : Type v) [Finite Q] :
    letI : TopologicalSpace (MonoidAlgebra S Q) := finiteGroupAlgebraTopology S Q
    DiscreteTopology (MonoidAlgebra S Q) := by
  classical
  let : Fintype Q := Fintype.ofFinite Q
  let : TopologicalSpace (MonoidAlgebra S Q) := finiteGroupAlgebraTopology S Q
  let e : MonoidAlgebra S Q ≃ (Q → S) :=
    MonoidAlgebra.coeffEquiv.trans Finsupp.equivFunOnFinite
  exact DiscreteTopology.of_continuous_injective
    (continuous_induced_dom : Continuous (e : MonoidAlgebra S Q → Q → S)) e.injective

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The Ribes--Zalesskii Section \(5.3\) finite quotient \((R/I)[G/U]\) applies both the coefficient
quotient and the group quotient and is used in the kernel-neighborhood topology.
-/
abbrev CompletedGroupAlgebraCoeffQuotientStage
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    Type (max u v) :=
  MonoidAlgebra (R ⧸ I) (CompletedGroupAlgebraQuotient G U)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The coefficient quotient map \(R[G/U]\) \(\to\) \((R/I)[G/U]\). -/
def completedGroupAlgebraStageCoeffQuotientMap
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    CompletedGroupAlgebraStage R G U →+*
      CompletedGroupAlgebraCoeffQuotientStage R G I U :=
  MonoidAlgebra.mapRingHom (CompletedGroupAlgebraQuotient G U)
    (Ideal.Quotient.mk I)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The coefficient-quotient map sends a singleton supported at a finite quotient class to the
corresponding singleton with transformed coefficient and unchanged quotient support.
-/
@[simp]
theorem completedGroupAlgebraStageCoeffQuotientMap_single
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G)
    (q : CompletedGroupAlgebraQuotient G U) (r : R) :
    completedGroupAlgebraStageCoeffQuotientMap R G I U (MonoidAlgebra.single q r) =
      MonoidAlgebra.single q (Ideal.Quotient.mk I r) := by
  exact MonoidAlgebra.mapRingHom_single (Ideal.Quotient.mk I) q r

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The finite-stage coefficient-quotient map is surjective; every target singleton is lifted by
keeping the quotient support and lifting the coefficient.
-/
theorem completedGroupAlgebraStageCoeffQuotientMap_surjective
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    Function.Surjective (completedGroupAlgebraStageCoeffQuotientMap R G I U) := by
  classical
  intro x
  obtain ⟨y, hy⟩ :=
    MonoidAlgebra.map_surjective (M := CompletedGroupAlgebraQuotient G U)
      (Ideal.Quotient.mk I).toAddMonoidHom Ideal.Quotient.mk_surjective x
  exact ⟨y, hy⟩

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The finite-quotient map \(R[G]\to (R/I)[G/U]\) used in Ribes--Zalesskii Section \(5.3\). -/
def groupAlgebraFiniteQuotientMap
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    MonoidAlgebra R G →+* CompletedGroupAlgebraCoeffQuotientStage R G I U :=
  (completedGroupAlgebraStageCoeffQuotientMap R G I U).comp
    (completedGroupAlgebraStageMap R G U)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The finite quotient map on a group algebra sends a singleton \(r[g]\) to the singleton \(\bar
r[\bar g]\) in \((R/I)[G/U]\).
-/
@[simp]
theorem groupAlgebraFiniteQuotientMap_single
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) (g : G) (r : R) :
    groupAlgebraFiniteQuotientMap R G I U (MonoidAlgebra.single g r) =
      MonoidAlgebra.single
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g)
        (Ideal.Quotient.mk I r) := by
  change
    MonoidAlgebra.map (Ideal.Quotient.mk I)
        (MonoidAlgebra.mapDomain
          (openNormalSubgroupInClassProj
            (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)
          (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g)
        (Ideal.Quotient.mk I r)
  rw [MonoidAlgebra.mapDomain_single, MonoidAlgebra.map_single]
  rfl

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The finite quotient group-algebra map is computed by choosing representatives and applying the
quotient map to supports.
-/
@[simp]
theorem groupAlgebraFiniteQuotientMap_of
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) (g : G) :
    groupAlgebraFiniteQuotientMap R G I U (MonoidAlgebra.of R G g) =
      MonoidAlgebra.of (R ⧸ I) (CompletedGroupAlgebraQuotient G U)
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) := by
  change
    groupAlgebraFiniteQuotientMap R G I U (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g) 1
  rw [groupAlgebraFiniteQuotientMap_single]
  exact congrArg
    (MonoidAlgebra.single
      (openNormalSubgroupInClassProj
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U g))
    (Ideal.Quotient.mk I).map_one

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The quotient map \(R[G] \to (R/I)[G/U]\) factors equally as coefficient quotient followed by
group quotient, or group quotient followed by coefficient quotient.
-/
theorem groupAlgebraFiniteQuotientMap_eq_mapDomain_comp_mapRange
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    groupAlgebraFiniteQuotientMap R G I U =
      (MonoidAlgebra.mapDomainRingHom (R ⧸ I)
          (openNormalSubgroupInClassProj
            (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)).comp
        (MonoidAlgebra.mapRingHom G (Ideal.Quotient.mk I)) := by
  change
    (MonoidAlgebra.mapRingHom (CompletedGroupAlgebraQuotient G U)
        (Ideal.Quotient.mk I)).comp
        (MonoidAlgebra.mapDomainRingHom R
          (openNormalSubgroupInClassProj
            (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)) =
      (MonoidAlgebra.mapDomainRingHom (R ⧸ I)
        (openNormalSubgroupInClassProj
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)).comp
        (MonoidAlgebra.mapRingHom G (Ideal.Quotient.mk I))
  exact MonoidAlgebra.mapRingHom_comp_mapDomainRingHom
    (f := Ideal.Quotient.mk I)
    (g := openNormalSubgroupInClassProj
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G) U)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The finite quotient map on group algebras is surjective, expressing functoriality after passage
to finite quotient stages.
-/
theorem groupAlgebraFiniteQuotientMap_surjective
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    Function.Surjective (groupAlgebraFiniteQuotientMap R G I U) := by
  classical
  exact
    (completedGroupAlgebraStageCoeffQuotientMap_surjective
      (R := R) (G := G) I U).comp
      (completedGroupAlgebraStageMap_surjective (R := R) (G := G) U)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The kernels used in Ribes--Zalesskii's natural topology on \(R[G]\); for the kernel-neighborhood
topology this family is restricted to open ideals \(I\) and open normal subgroups \(U\).
-/
def groupAlgebraFiniteQuotientKernel
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    Ideal (MonoidAlgebra R G) :=
  RingHom.ker (groupAlgebraFiniteQuotientMap R G I U)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
An element of \(R[G]\) lies in `groupAlgebraFiniteQuotientKernel` exactly when its image in
\((R/I)[G/U]\) is zero.
-/
@[simp]
theorem mem_groupAlgebraFiniteQuotientKernel_iff
    {R : Type u} {G : Type v} [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    {I : Ideal R} {U : CompletedGroupAlgebraIndex G} {x : MonoidAlgebra R G} :
    x ∈ groupAlgebraFiniteQuotientKernel R G I U ↔
      groupAlgebraFiniteQuotientMap R G I U x = 0 :=
  Iff.rfl

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The kernel of the finite quotient group-algebra map is the comap of the corresponding
quotient-kernel data.
-/
theorem groupAlgebraFiniteQuotientKernel_eq_comap
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    groupAlgebraFiniteQuotientKernel R G I U =
      Ideal.comap (completedGroupAlgebraStageMap R G U)
        (RingHom.ker (completedGroupAlgebraStageCoeffQuotientMap R G I U)) :=
  rfl

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
Coefficient transition \((R/I)[G/U]\) \(\to\) \((R/J)[G/U]\) induced by an inclusion \(I\le J\).
-/
def completedGroupAlgebraCoeffQuotientTransition
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {I J : Ideal R} (hIJ : I ≤ J)
    (U : CompletedGroupAlgebraIndex G) :
    CompletedGroupAlgebraCoeffQuotientStage R G I U →+*
      CompletedGroupAlgebraCoeffQuotientStage R G J U :=
  MonoidAlgebra.mapRingHom (CompletedGroupAlgebraQuotient G U)
    (Ideal.Quotient.factor hIJ)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The coefficient transition from \(R/I\) to \(R/J\) fixes the support \(q\) and applies
`Ideal.Quotient.factor` to the singleton coefficient.
-/
@[simp]
theorem completedGroupAlgebraCoeffQuotientTransition_single
    {I J : Ideal R} (hIJ : I ≤ J) (U : CompletedGroupAlgebraIndex G)
    (q : CompletedGroupAlgebraQuotient G U) (r : R ⧸ I) :
    completedGroupAlgebraCoeffQuotientTransition R G hIJ U (MonoidAlgebra.single q r) =
      MonoidAlgebra.single q (Ideal.Quotient.factor hIJ r) := by
  exact MonoidAlgebra.mapRingHom_single (Ideal.Quotient.factor hIJ) q r

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
Applying the coefficient transition after reduction modulo \(I\) agrees with reducing the stage
coefficients directly modulo \(J\).
-/
@[simp]
theorem completedGroupAlgebraCoeffQuotientTransition_comp_stageCoeffQuotientMap
    {I J : Ideal R} (hIJ : I ≤ J) (U : CompletedGroupAlgebraIndex G) :
    (completedGroupAlgebraCoeffQuotientTransition R G hIJ U).comp
        (completedGroupAlgebraStageCoeffQuotientMap R G I U) =
      completedGroupAlgebraStageCoeffQuotientMap R G J U := by
  rw [completedGroupAlgebraCoeffQuotientTransition,
    completedGroupAlgebraStageCoeffQuotientMap, completedGroupAlgebraStageCoeffQuotientMap,
    ← MonoidAlgebra.mapRingHom_comp]
  simp only [Ideal.Quotient.factor_comp_mk]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
At a fixed quotient stage \(U\), the coefficient transition induced by \(I\leq J\) is
surjective.
-/
theorem completedGroupAlgebraCoeffQuotientTransition_surjective
    {I J : Ideal R} (hIJ : I ≤ J) (U : CompletedGroupAlgebraIndex G) :
    Function.Surjective (completedGroupAlgebraCoeffQuotientTransition R G hIJ U) := by
  classical
  intro x
  obtain ⟨y, hy⟩ :=
    MonoidAlgebra.map_surjective (M := CompletedGroupAlgebraQuotient G U)
      (Ideal.Quotient.factor hIJ).toAddMonoidHom
      (Ideal.Quotient.factor_surjective hIJ) x
  exact ⟨y, hy⟩

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- Group-quotient transition \((R/I)[G/V]\) \(\to\) \((R/I)[G/U]\) induced by \(U\le V\). -/
def completedGroupAlgebraCoeffQuotientGroupTransition
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (I : Ideal R) {U V : CompletedGroupAlgebraIndex G}
    (hUV : U ≤ V) :
    CompletedGroupAlgebraCoeffQuotientStage R G I V →+*
      CompletedGroupAlgebraCoeffQuotientStage R G I U :=
  MonoidAlgebra.mapDomainRingHom (R ⧸ I)
    (OpenNormalSubgroupInClass.map
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The group-quotient transition from \(G/V\) to \(G/U\) sends a singleton to the singleton at the
induced quotient image and leaves its \(R/I\)-coefficient unchanged.
-/
@[simp]
theorem completedGroupAlgebraCoeffQuotientGroupTransition_single
    (I : Ideal R) {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V)
    (q : CompletedGroupAlgebraQuotient G V) (r : R ⧸ I) :
    completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) r := by
  change
    MonoidAlgebra.mapDomain
        (OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q) r
  exact MonoidAlgebra.mapDomain_single

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
Changing the group quotient after reducing coefficients modulo \(I\) agrees with first applying
the group-stage transition and then reducing coefficients.
-/
@[simp]
theorem completedGroupAlgebraCoeffQuotientGroupTransition_comp_stageCoeffQuotientMap
    (I : Ideal R) {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV).comp
        (completedGroupAlgebraStageCoeffQuotientMap R G I V) =
      (completedGroupAlgebraStageCoeffQuotientMap R G I U).comp
        (completedGroupAlgebraTransition R G hUV) := by
  rw [completedGroupAlgebraCoeffQuotientGroupTransition,
    completedGroupAlgebraStageCoeffQuotientMap, completedGroupAlgebraStageCoeffQuotientMap,
    completedGroupAlgebraTransition]
  exact (MonoidAlgebra.mapRingHom_comp_mapDomainRingHom
    (f := Ideal.Quotient.mk I)
    (g := OpenNormalSubgroupInClass.map
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)).symm

omit [TopologicalSpace R] [IsTopologicalRing R] [IsTopologicalGroup G] in
/-- The canonical quotient homomorphism \(G/V\to G/U\) induced by \(U\leq V\) is surjective. -/
theorem completedGroupAlgebraQuotientTransition_surjective
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    Function.Surjective
      (OpenNormalSubgroupInClass.map
        (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) := by
  intro q
  rcases QuotientGroup.mk'_surjective
      ((((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G)) q with
    ⟨g, rfl⟩
  refine ⟨QuotientGroup.mk'
    ((((OrderDual.ofDual V).1 : OpenNormalSubgroup G) : Subgroup G)) g, rfl⟩

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The group-quotient transition \((R/I)[G/V]\to(R/I)[G/U]\) is surjective.
-/
theorem completedGroupAlgebraCoeffQuotientGroupTransition_surjective
    (I : Ideal R) {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    Function.Surjective (completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV) := by
  classical
  intro x
  obtain ⟨y, hy⟩ :=
    Finsupp.mapDomain_surjective (M := R ⧸ I)
      (completedGroupAlgebraQuotientTransition_surjective
        (G := G) hUV) x.coeff
  refine ⟨MonoidAlgebra.ofCoeff y, ?_⟩
  apply MonoidAlgebra.coeff_injective
  exact hy

omit [TopologicalSpace R] [IsTopologicalRing R] in
/-- The combined transition (R/I)[G/V] -> (R/J)[G/U]. -/
def completedGroupAlgebraFiniteQuotientTransition
    (R : Type u) (G : Type v) [CommRing R] [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {I J : Ideal R} (hIJ : I ≤ J)
    {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    CompletedGroupAlgebraCoeffQuotientStage R G I V →+*
      CompletedGroupAlgebraCoeffQuotientStage R G J U :=
  (completedGroupAlgebraCoeffQuotientTransition R G hIJ U).comp
    (completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV)

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The combined finite-quotient transition sends a singleton by transporting its support from
\(G/V\) to \(G/U\) and its coefficient from \(R/I\) to \(R/J\).
-/
@[simp]
theorem completedGroupAlgebraFiniteQuotientTransition_single
    {I J : Ideal R} (hIJ : I ≤ J) {U V : CompletedGroupAlgebraIndex G}
    (hUV : U ≤ V) (q : CompletedGroupAlgebraQuotient G V) (r : R ⧸ I) :
    completedGroupAlgebraFiniteQuotientTransition R G hIJ hUV
        (MonoidAlgebra.single q r) =
      MonoidAlgebra.single
        ((OpenNormalSubgroupInClass.map
          (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV) q)
        (Ideal.Quotient.factor hIJ r) := by
  let f : CompletedGroupAlgebraQuotient G V →*
      CompletedGroupAlgebraQuotient G U :=
    OpenNormalSubgroupInClass.map
      (C := ProCGroups.FiniteGroupClass.allFinite) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV
  change
    MonoidAlgebra.map (Ideal.Quotient.factor hIJ)
        (MonoidAlgebra.mapDomain f (MonoidAlgebra.single q r)) =
      MonoidAlgebra.single (f q) (Ideal.Quotient.factor hIJ r)
  rw [MonoidAlgebra.mapDomain_single, MonoidAlgebra.map_single]
  rfl

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
At fixed coefficient quotient \(R/I\), applying the group-quotient transition after the abstract
finite-quotient map at \(V\) gives the finite-quotient map at \(U\).
-/
@[simp]
theorem completedGroupAlgebraCoeffQuotientGroupTransition_comp_finiteQuotientMap
    (I : Ideal R) {U V : CompletedGroupAlgebraIndex G} (hUV : U ≤ V) :
    (completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV).comp
        (groupAlgebraFiniteQuotientMap R G I V) =
      groupAlgebraFiniteQuotientMap R G I U := by
  apply RingHom.ext
  intro x
  calc
    completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV
        (groupAlgebraFiniteQuotientMap R G I V x) =
      completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV
        (completedGroupAlgebraStageCoeffQuotientMap R G I V
          (completedGroupAlgebraStageMap R G V x)) := rfl
    _ =
      completedGroupAlgebraStageCoeffQuotientMap R G I U
        (completedGroupAlgebraTransition R G hUV
          (completedGroupAlgebraStageMap R G V x)) := by
      exact congrFun
        (congrArg DFunLike.coe
          (completedGroupAlgebraCoeffQuotientGroupTransition_comp_stageCoeffQuotientMap
            (R := R) (G := G) I (U := U) (V := V) hUV))
        (completedGroupAlgebraStageMap R G V x)
    _ =
      completedGroupAlgebraStageCoeffQuotientMap R G I U
        (completedGroupAlgebraStageMap R G U x) := by
      congr 1
      exact congrFun
        (congrArg DFunLike.coe
          (completedGroupAlgebraStageMap_compatible
            (R := R) (G := G) (U := U) (V := V) hUV))
        x
    _ = groupAlgebraFiniteQuotientMap R G I U x := rfl

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The combined transition from \((R/I)[G/V]\) to \((R/J)[G/U]\), composed with the source
finite-quotient map, is the target finite-quotient map.
-/
@[simp]
theorem completedGroupAlgebraFiniteQuotientTransition_comp_finiteQuotientMap
    {I J : Ideal R} (hIJ : I ≤ J) {U V : CompletedGroupAlgebraIndex G}
    (hUV : U ≤ V) :
    (completedGroupAlgebraFiniteQuotientTransition R G hIJ hUV).comp
        (groupAlgebraFiniteQuotientMap R G I V) =
      groupAlgebraFiniteQuotientMap R G J U := by
  rw [completedGroupAlgebraFiniteQuotientTransition, RingHom.comp_assoc,
    completedGroupAlgebraCoeffQuotientGroupTransition_comp_finiteQuotientMap]
  rw [groupAlgebraFiniteQuotientMap, groupAlgebraFiniteQuotientMap]
  rw [← RingHom.comp_assoc,
    completedGroupAlgebraCoeffQuotientTransition_comp_stageCoeffQuotientMap]

omit [TopologicalSpace R] [IsTopologicalRing R] in
/--
The combined coefficient-and-group transition
\((R/I)[G/V]\to(R/J)[G/U]\) is surjective.
-/
theorem completedGroupAlgebraFiniteQuotientTransition_surjective
    {I J : Ideal R} (hIJ : I ≤ J) {U V : CompletedGroupAlgebraIndex G}
    (hUV : U ≤ V) :
    Function.Surjective (completedGroupAlgebraFiniteQuotientTransition R G hIJ hUV) := by
  intro x
  rcases completedGroupAlgebraCoeffQuotientTransition_surjective
      (R := R) (G := G) hIJ U x with
    ⟨y, hy⟩
  rcases completedGroupAlgebraCoeffQuotientGroupTransition_surjective
      (R := R) (G := G) I hUV y with
    ⟨z, hz⟩
  exact ⟨z, by rw [completedGroupAlgebraFiniteQuotientTransition, RingHom.comp_apply, hz, hy]⟩

/-- The corresponding projection from the completed group algebra to \((R/I)[G/U]\). -/
def completedGroupAlgebraFiniteQuotientProjection
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    CompletedGroupAlgebraCarrier R G →+*
      CompletedGroupAlgebraCoeffQuotientStage R G I U :=
  (completedGroupAlgebraStageCoeffQuotientMap R G I U).comp
    (completedGroupAlgebraProjection R G U)

/--
Composing the finite-quotient projection from the completed group algebra with its canonical dense
ring homomorphism gives `groupAlgebraFiniteQuotientMap`.
-/
@[simp]
theorem completedGroupAlgebraFiniteQuotientProjection_toCompletedGroupAlgebra
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) :
    (completedGroupAlgebraFiniteQuotientProjection R G I U).comp
        (toCompletedGroupAlgebraRingHom R G) =
      groupAlgebraFiniteQuotientMap R G I U := by
  apply RingHom.ext
  intro x
  rfl

/--
The finite-quotient projection of the canonical dense element is computed by the associated
quotient-stage map.
-/
@[simp]
theorem completedGroupAlgebraFiniteQuotientProjection_apply_toCompletedGroupAlgebra
    (I : Ideal R) (U : CompletedGroupAlgebraIndex G) (x : MonoidAlgebra R G) :
    completedGroupAlgebraFiniteQuotientProjection R G I U
        (toCompletedGroupAlgebra R G x) =
      groupAlgebraFiniteQuotientMap R G I U x :=
  rfl

/--
Projecting to \((R/I)[G/V]\) and then applying the combined transition agrees with projecting
directly to \((R/J)[G/U]\).
-/
@[simp 900]
theorem completedGroupAlgebraFiniteQuotientTransition_comp_projection
    {I J : Ideal R} (hIJ : I ≤ J) {U V : CompletedGroupAlgebraIndex G}
    (hUV : U ≤ V) :
    (completedGroupAlgebraFiniteQuotientTransition R G hIJ hUV).comp
        (completedGroupAlgebraFiniteQuotientProjection R G I V) =
      completedGroupAlgebraFiniteQuotientProjection R G J U := by
  apply RingHom.ext
  intro x
  calc
    completedGroupAlgebraFiniteQuotientTransition R G hIJ hUV
        (completedGroupAlgebraFiniteQuotientProjection R G I V x)
        =
      completedGroupAlgebraCoeffQuotientTransition R G hIJ U
        (completedGroupAlgebraCoeffQuotientGroupTransition R G I hUV
          (completedGroupAlgebraStageCoeffQuotientMap R G I V
            (completedGroupAlgebraProjection R G V x))) := rfl
    _ =
      completedGroupAlgebraCoeffQuotientTransition R G hIJ U
        (completedGroupAlgebraStageCoeffQuotientMap R G I U
          (completedGroupAlgebraTransition R G hUV
            (completedGroupAlgebraProjection R G V x))) := by
        have hstage := congrFun
          (congrArg DFunLike.coe
            (completedGroupAlgebraCoeffQuotientGroupTransition_comp_stageCoeffQuotientMap
              (R := R) (G := G) I (U := U) (V := V) hUV))
          (completedGroupAlgebraProjection R G V x)
        exact congrArg (completedGroupAlgebraCoeffQuotientTransition R G hIJ U) hstage
    _ =
      completedGroupAlgebraCoeffQuotientTransition R G hIJ U
        (completedGroupAlgebraStageCoeffQuotientMap R G I U
          (completedGroupAlgebraProjection R G U x)) := by
        rw [completedGroupAlgebraProjection_compatible (R := R) (G := G) x hUV]
    _ =
      completedGroupAlgebraStageCoeffQuotientMap R G J U
        (completedGroupAlgebraProjection R G U x) := by
        exact congrFun
          (congrArg DFunLike.coe
            (completedGroupAlgebraCoeffQuotientTransition_comp_stageCoeffQuotientMap
              (R := R) (G := G) (I := I) (J := J) hIJ U))
          (completedGroupAlgebraProjection R G U x)
    _ = completedGroupAlgebraFiniteQuotientProjection R G J U x := rfl
end

end CompletedGroupAlgebra
