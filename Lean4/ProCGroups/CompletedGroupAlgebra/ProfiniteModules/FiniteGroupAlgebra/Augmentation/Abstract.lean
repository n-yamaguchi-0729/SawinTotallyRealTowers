import ProCGroups.CompletedGroupAlgebra.ProfiniteModules.FiniteGroupAlgebra.Functoriality

set_option autoImplicit false

/-!
# Algebraic group-algebra augmentation

This file defines augmentation of an abstract group algebra, its linear form and kernel ideal,
and the resulting short exact sequences. It also proves that the differences \(g-1\) generate the
augmentation ideal.
-/

open scoped Topology
open ProCGroups

namespace CompletedGroupAlgebra

universe u v w z

/-- The augmentation map \(R[G] \to R\), sending every group-like basis element to \(1\). -/
noncomputable def groupAlgebraAugmentation
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    MonoidAlgebra R G →+* R :=
  (MonoidAlgebra.lift R R G (1 : MonoidHom G R)).toRingHom

/-- On a group-like basis element, the abstract augmentation is 1. -/
@[simp]
theorem groupAlgebraAugmentation_of
    (R : Type u) (G : Type v) [CommRing R] [Group G] (g : G) :
    groupAlgebraAugmentation R G (MonoidAlgebra.of R G g) = 1 := by
  simp only [groupAlgebraAugmentation, AlgHom.toRingHom_eq_coe, MonoidAlgebra.of_apply,
      RingHom.coe_coe,
  MonoidAlgebra.lift_single, MonoidHom.one_apply, smul_eq_mul, mul_one]

/-- On a finitely supported singleton, the abstract augmentation returns its coefficient. -/
@[simp]
theorem groupAlgebraAugmentation_single
    (R : Type u) (G : Type v) [CommRing R] [Group G] (g : G) (r : R) :
    groupAlgebraAugmentation R G (MonoidAlgebra.single g r) = r := by
  simp only [groupAlgebraAugmentation, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MonoidAlgebra.lift_single,
  MonoidHom.one_apply, smul_eq_mul, mul_one]

/-- The abstract augmentation restricts to the identity on coefficient scalars. -/
@[simp]
theorem groupAlgebraAugmentation_algebraMap
    (R : Type u) (G : Type v) [CommRing R] [Group G] (r : R) :
    groupAlgebraAugmentation R G (algebraMap R (MonoidAlgebra R G) r) = r := by
  simp only [groupAlgebraAugmentation, AlgHom.toRingHom_eq_coe, MonoidAlgebra.coe_algebraMap,
  Algebra.algebraMap_self, RingHom.coe_id, Function.comp_apply, id_eq, RingHom.coe_coe,
      MonoidAlgebra.lift_single,
  MonoidHom.one_apply, smul_eq_mul, mul_one]

/-- The abstract group-algebra augmentation is split by the coefficient inclusion. -/
theorem groupAlgebraAugmentation_surjective
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    Function.Surjective (groupAlgebraAugmentation R G) := by
  intro r
  refine ⟨algebraMap R (MonoidAlgebra R G) r, ?_⟩
  simp only [MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id,
      Function.comp_apply, id_eq,
  groupAlgebraAugmentation_single]

/-- The augmentation map \(R[G] \to R\) is viewed as an \(R\)-linear map. -/
noncomputable def groupAlgebraAugmentationLinearMap
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    MonoidAlgebra R G →ₗ[R] R where
  toFun := groupAlgebraAugmentation R G
  map_add' := by
    intro x y
    exact map_add (groupAlgebraAugmentation R G) x y
  map_smul' := by
    intro r x
    simp only [Algebra.smul_def, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
        RingHom.coe_id,
  Function.comp_apply, id_eq, map_mul, groupAlgebraAugmentation_single, RingHom.id_apply]

/--
The augmentation map is evaluated by projecting to the corresponding finite group-algebra stage
and summing coefficients via the usual group-algebra augmentation.
-/
@[simp]
theorem groupAlgebraAugmentationLinearMap_apply
    (R : Type u) (G : Type v) [CommRing R] [Group G] (x : MonoidAlgebra R G) :
    groupAlgebraAugmentationLinearMap R G x = groupAlgebraAugmentation R G x :=
  rfl

/-- The \(R\)-linear augmentation is split by the coefficient inclusion. -/
theorem groupAlgebraAugmentationLinearMap_surjective
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    Function.Surjective (groupAlgebraAugmentationLinearMap R G) := by
  simpa [groupAlgebraAugmentationLinearMap] using groupAlgebraAugmentation_surjective R G

/-- The augmentation ideal of an abstract group algebra. -/
noncomputable def groupAlgebraAugmentationIdeal
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    Ideal (MonoidAlgebra R G) :=
  RingHom.ker (groupAlgebraAugmentation R G)

/-- The augmentation ideal of an abstract group algebra, regarded as an \(R\)-submodule. -/
noncomputable def groupAlgebraAugmentationIdealSubmodule
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    Submodule R (MonoidAlgebra R G) :=
  (groupAlgebraAugmentationIdeal R G).restrictScalars R

/--
An abstract group-algebra element lies in the augmentation ideal iff its augmentation is zero.
-/
@[simp]
theorem mem_groupAlgebraAugmentationIdeal_iff
    {R : Type u} {G : Type v} [CommRing R] [Group G] {x : MonoidAlgebra R G} :
    x ∈ groupAlgebraAugmentationIdeal R G ↔ groupAlgebraAugmentation R G x = 0 :=
  Iff.rfl

/--
An abstract group-algebra element lies in the augmentation ideal submodule iff its augmentation
is zero.
-/
@[simp]
theorem mem_groupAlgebraAugmentationIdealSubmodule_iff
    {R : Type u} {G : Type v} [CommRing R] [Group G] {x : MonoidAlgebra R G} :
    x ∈ groupAlgebraAugmentationIdealSubmodule R G ↔ groupAlgebraAugmentation R G x = 0 :=
  Iff.rfl

/-- The inclusion of the abstract augmentation ideal into the group algebra is injective. -/
theorem groupAlgebraAugmentationIdeal_subtype_injective
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    Function.Injective
      (fun x : groupAlgebraAugmentationIdeal R G => (x : MonoidAlgebra R G)) := by
  intro x y hxy
  exact Subtype.ext hxy

/-- The abstract augmentation ideal is exactly the kernel of the augmentation. -/
theorem exact_groupAlgebraAugmentationIdeal_subtype
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    Function.Exact
      (fun x : groupAlgebraAugmentationIdeal R G => (x : MonoidAlgebra R G))
      (groupAlgebraAugmentation R G) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.2

/--
At the level of underlying functions, the subtype inclusion of the abstract augmentation ideal,
followed by the ordinary augmentation, is a short exact sequence.
-/
theorem groupAlgebraAugmentation_shortExact
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    Function.Injective
        (fun x : groupAlgebraAugmentationIdeal R G => (x : MonoidAlgebra R G)) ∧
      Function.Exact
        (fun x : groupAlgebraAugmentationIdeal R G => (x : MonoidAlgebra R G))
        (groupAlgebraAugmentation R G) ∧
      Function.Surjective (groupAlgebraAugmentation R G) := by
  exact ⟨groupAlgebraAugmentationIdeal_subtype_injective R G,
    exact_groupAlgebraAugmentationIdeal_subtype R G,
    groupAlgebraAugmentation_surjective R G⟩

/--
The inclusion of the abstract augmentation ideal into the group algebra as an \(R\)-linear map.
-/
noncomputable def groupAlgebraAugmentationIdealSubmoduleSubtypeLinearMap
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    groupAlgebraAugmentationIdealSubmodule R G →ₗ[R] MonoidAlgebra R G :=
  (groupAlgebraAugmentationIdealSubmodule R G).subtype

/--
The subtype linear map from the abstract augmentation-ideal submodule into the group algebra is
injective.
-/
theorem groupAlgebraAugmentationIdealSubmoduleSubtypeLinearMap_injective
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    Function.Injective (groupAlgebraAugmentationIdealSubmoduleSubtypeLinearMap R G) := by
  intro x y hxy
  exact Subtype.ext hxy

/-- The abstract augmentation ideal is the kernel of the \(R\)-linear augmentation. -/
theorem exact_groupAlgebraAugmentationIdealSubmoduleSubtypeLinearMap
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    Function.Exact
      (groupAlgebraAugmentationIdealSubmoduleSubtypeLinearMap R G)
      (groupAlgebraAugmentationLinearMap R G) := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.2

/--
The \(R\)-linear inclusion of the abstract augmentation-ideal submodule, followed by the linear
augmentation, is a short exact sequence of underlying functions.
-/
theorem groupAlgebraAugmentationLinearMap_shortExact
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    Function.Injective (groupAlgebraAugmentationIdealSubmoduleSubtypeLinearMap R G) ∧
      Function.Exact
        (groupAlgebraAugmentationIdealSubmoduleSubtypeLinearMap R G)
        (groupAlgebraAugmentationLinearMap R G) ∧
      Function.Surjective (groupAlgebraAugmentationLinearMap R G) := by
  exact ⟨groupAlgebraAugmentationIdealSubmoduleSubtypeLinearMap_injective R G,
    exact_groupAlgebraAugmentationIdealSubmoduleSubtypeLinearMap R G,
    groupAlgebraAugmentationLinearMap_surjective R G⟩

/-- The standard generator \(g-1\) of the abstract augmentation ideal. -/
noncomputable def groupAlgebraAugmentationGenerator
    (R : Type u) (G : Type v) [CommRing R] [Group G] (g : G) :
    MonoidAlgebra R G :=
  MonoidAlgebra.of R G g - 1

/-- The ideal generated by the standard abstract augmentation generators \(g-1\). -/
noncomputable def groupAlgebraAugmentationGeneratorIdeal
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    Ideal (MonoidAlgebra R G) :=
  Ideal.span (Set.range (groupAlgebraAugmentationGenerator R G))

/-- A standard abstract augmentation generator lies in the augmentation ideal. -/
theorem groupAlgebraAugmentationGenerator_mem_augmentationIdeal
    (R : Type u) (G : Type v) [CommRing R] [Group G] (g : G) :
    groupAlgebraAugmentationGenerator R G g ∈ groupAlgebraAugmentationIdeal R G := by
  simp only [groupAlgebraAugmentationGenerator, MonoidAlgebra.of_apply,
      mem_groupAlgebraAugmentationIdeal_iff,
  map_sub, groupAlgebraAugmentation_single, map_one, sub_self]

/-- A standard abstract augmentation generator lies in the ideal generated by such generators. -/
theorem groupAlgebraAugmentationGenerator_mem_generatorIdeal
    (R : Type u) (G : Type v) [CommRing R] [Group G] (g : G) :
    groupAlgebraAugmentationGenerator R G g ∈
      groupAlgebraAugmentationGeneratorIdeal R G := by
  exact Ideal.subset_span ⟨g, rfl⟩

/-- The standard-generator ideal is contained in the abstract augmentation ideal. -/
theorem groupAlgebraAugmentationGeneratorIdeal_le_augmentationIdeal
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    groupAlgebraAugmentationGeneratorIdeal R G ≤ groupAlgebraAugmentationIdeal R G := by
  refine Ideal.span_le.2 ?_
  rintro _ ⟨g, rfl⟩
  exact groupAlgebraAugmentationGenerator_mem_augmentationIdeal R G g

/--
Every abstract group-algebra element differs from its augmentation scalar by an element of the
standard-generator ideal.
-/
theorem exists_mem_groupAlgebraAugmentationGeneratorIdeal_add
    (R : Type u) (G : Type v) [CommRing R] [Group G] (x : MonoidAlgebra R G) :
    ∃ y ∈ groupAlgebraAugmentationGeneratorIdeal R G,
      x = y + algebraMap R (MonoidAlgebra R G) (groupAlgebraAugmentation R G x) := by
  refine MonoidAlgebra.induction_on
    (motive := fun x : MonoidAlgebra R G =>
      ∃ y ∈ groupAlgebraAugmentationGeneratorIdeal R G,
        x = y + algebraMap R (MonoidAlgebra R G) (groupAlgebraAugmentation R G x))
    x ?_ ?_ ?_
  · intro g
    refine
      ⟨groupAlgebraAugmentationGenerator R G g,
        groupAlgebraAugmentationGenerator_mem_generatorIdeal R G g, ?_⟩
    rw [groupAlgebraAugmentationGenerator, groupAlgebraAugmentation_of]
    rw [map_one]
    rw [sub_add_cancel]
  · intro x z hx hz
    rcases hx with ⟨y, hy, hxy⟩
    rcases hz with ⟨w, hw, hwz⟩
    refine ⟨y + w, (groupAlgebraAugmentationGeneratorIdeal R G).add_mem hy hw, ?_⟩
    have hy0 : groupAlgebraAugmentation R G y = 0 :=
      (mem_groupAlgebraAugmentationIdeal_iff (R := R) (G := G) (x := y)).1
        (groupAlgebraAugmentationGeneratorIdeal_le_augmentationIdeal R G hy)
    have hw0 : groupAlgebraAugmentation R G w = 0 :=
      (mem_groupAlgebraAugmentationIdeal_iff (R := R) (G := G) (x := w)).1
        (groupAlgebraAugmentationGeneratorIdeal_le_augmentationIdeal R G hw)
    rw [hxy, hwz, map_add]
    simp only [MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self, RingHom.coe_id,
        Function.comp_apply, id_eq,
  add_left_comm, add_assoc, map_add, hy0, groupAlgebraAugmentation_single, zero_add, hw0]
  · intro r x hx
    rcases hx with ⟨y, hy, hxy⟩
    refine ⟨r • y, ?_, ?_⟩
    · have hy' :
          algebraMap R (MonoidAlgebra R G) r * y ∈
            groupAlgebraAugmentationGeneratorIdeal R G :=
        (groupAlgebraAugmentationGeneratorIdeal R G).mul_mem_left _ hy
      simpa [Algebra.smul_def] using hy'
    · have hy0 : groupAlgebraAugmentation R G y = 0 :=
        (mem_groupAlgebraAugmentationIdeal_iff (R := R) (G := G) (x := y)).1
          (groupAlgebraAugmentationGeneratorIdeal_le_augmentationIdeal R G hy)
      rw [hxy, smul_add]
      simp only [Algebra.smul_def, MonoidAlgebra.coe_algebraMap, Algebra.algebraMap_self,
          RingHom.coe_id,
  Function.comp_apply, id_eq, MonoidAlgebra.single_mul_single, mul_one, map_add, map_mul,
  groupAlgebraAugmentation_single, hy0, mul_zero, zero_add]

/-- The abstract augmentation ideal is generated by the standard elements \(g-1\). -/
theorem groupAlgebraAugmentationGeneratorIdeal_eq_augmentationIdeal
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    groupAlgebraAugmentationGeneratorIdeal R G = groupAlgebraAugmentationIdeal R G := by
  refine le_antisymm
    (groupAlgebraAugmentationGeneratorIdeal_le_augmentationIdeal R G) ?_
  intro x hx
  rcases exists_mem_groupAlgebraAugmentationGeneratorIdeal_add R G x with ⟨y, hy, hxy⟩
  have haug : groupAlgebraAugmentation R G x = 0 :=
    (mem_groupAlgebraAugmentationIdeal_iff (R := R) (G := G) (x := x)).1 hx
  rw [hxy, haug]
  simpa using hy

/-- The standard generators \(g-1\), viewed inside the augmentation ideal. -/
noncomputable def groupAlgebraAugmentationGeneratorSubtype
    (R : Type u) (G : Type v) [CommRing R] [Group G] (g : G) :
    groupAlgebraAugmentationIdeal R G :=
  ⟨groupAlgebraAugmentationGenerator R G g,
    groupAlgebraAugmentationGenerator_mem_augmentationIdeal R G g⟩

/-- The augmentation ideal is spanned by the standard generators viewed in the ideal itself. -/
theorem groupAlgebraAugmentationGeneratorSubtype_span_eq_top
    (R : Type u) (G : Type v) [CommRing R] [Group G] :
    Submodule.span (MonoidAlgebra R G)
      (Set.range (groupAlgebraAugmentationGeneratorSubtype R G)) = ⊤ := by
  have hspan :
      Submodule.span (MonoidAlgebra R G)
        (Set.range fun g =>
          (⟨groupAlgebraAugmentationGenerator R G g,
            groupAlgebraAugmentationGenerator_mem_augmentationIdeal R G g⟩ :
            groupAlgebraAugmentationIdeal R G)) = ⊤ := by
    rw [Submodule.span_range_subtype_eq_top_iff
      (p := groupAlgebraAugmentationIdeal R G)
      (s := groupAlgebraAugmentationGenerator R G)
      (hs := groupAlgebraAugmentationGenerator_mem_augmentationIdeal R G)]
    simpa [groupAlgebraAugmentationGeneratorIdeal] using
      congrArg
        (fun I : Ideal (MonoidAlgebra R G) =>
          (I : Submodule (MonoidAlgebra R G) (MonoidAlgebra R G)))
        (groupAlgebraAugmentationGeneratorIdeal_eq_augmentationIdeal R G)
  unfold groupAlgebraAugmentationGeneratorSubtype
  exact hspan

/-- On a finite group algebra, the augmentation is the finite sum of coordinates. -/
theorem finiteGroupAlgebra_augmentation_apply_eq_sum
    (R : Type u) (G : Type v) [CommRing R] [Group G] [Finite G]
    (x : MonoidAlgebra R G) :
    letI : Fintype G := Fintype.ofFinite G
    groupAlgebraAugmentation R G x = ∑ g : G, x.coeff g := by
  classical
  let : Fintype G := Fintype.ofFinite G
  calc
    groupAlgebraAugmentation R G x = x.coeff.sum (fun _ r => r) := by
      simp only [groupAlgebraAugmentation, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          MonoidAlgebra.lift_apply,
  MonoidHom.one_apply, smul_eq_mul, mul_one]
    _ = ∑ g : G, x.coeff g := by
      exact Finsupp.sum_fintype x.coeff (fun _ r => r) (by intro g; simp only)

/--
The coefficient inclusion into a finite-stage group algebra is continuous for the product
topology.
-/
theorem finiteGroupAlgebra_algebraMap_continuous
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R]
    [Group G] [Finite G] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    Continuous (algebraMap R (MonoidAlgebra R G)) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  let e : MonoidAlgebra R G ≃ (G → R) :=
    (MonoidAlgebra.coeffEquiv (R := R) (M := G)).trans Finsupp.equivFunOnFinite
  have he : Topology.IsInducing (e : MonoidAlgebra R G → G → R) :=
    Topology.IsInducing.induced e
  rw [he.continuous_iff]
  apply continuous_pi
  intro g
  change Continuous fun r : R => (MonoidAlgebra.single (1 : G) r).coeff g
  by_cases hg : g = 1
  · subst g
    simpa only [MonoidAlgebra.coeff_single, Finsupp.single_apply, if_pos] using
      (continuous_id' : Continuous fun r : R => r)
  · rw [show (fun r : R => (MonoidAlgebra.single (1 : G) r).coeff g) =
        (fun _ : R => 0) from by
          funext r
          simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply,
            if_neg (Ne.symm hg)]]
    exact continuous_const

/-- The augmentation map is continuous on each finite-stage group algebra. -/
theorem finiteGroupAlgebra_augmentation_continuous
    (R : Type u) (G : Type v) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
    [Group G] [Finite G] :
    letI : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
    Continuous (groupAlgebraAugmentation R G) := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : TopologicalSpace (MonoidAlgebra R G) := finiteGroupAlgebraTopology R G
  change Continuous (fun x : MonoidAlgebra R G => groupAlgebraAugmentation R G x)
  rw [show (fun x : MonoidAlgebra R G => groupAlgebraAugmentation R G x) =
      (fun x : MonoidAlgebra R G => ∑ g : G, x.coeff g) from by
        funext x
        exact finiteGroupAlgebra_augmentation_apply_eq_sum R G x]
  apply continuous_finsetSum
  intro g _hg
  exact finiteGroupAlgebra_coordinate_continuous R G g

/-- The augmentation is natural for the finite-stage group-algebra functor. -/
theorem groupAlgebraAugmentation_mapDomainRingHom
    (R : Type u) (G : Type v) (H : Type w) [CommRing R] [Group G] [Group H]
    (φ : G →* H) (x : MonoidAlgebra R G) :
    groupAlgebraAugmentation R H (MonoidAlgebra.mapDomainRingHom R φ x) =
      groupAlgebraAugmentation R G x := by
  refine MonoidAlgebra.induction_linear x ?_ ?_ ?_
  · simp only [map_zero]
  · intro y z hy hz
    simp only [map_add, hy, hz]
  · intro g r
    rw [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single,
      groupAlgebraAugmentation_single, groupAlgebraAugmentation_single]

/-- The augmentation is natural in the coefficient ring. -/
theorem groupAlgebraAugmentation_mapRangeRingHom
    (R : Type u) (S : Type w) (G : Type v) [CommRing R] [CommRing S] [Group G]
    (f : R →+* S) (x : MonoidAlgebra R G) :
    groupAlgebraAugmentation S G (MonoidAlgebra.mapRingHom G f x) =
      f (groupAlgebraAugmentation R G x) := by
  refine MonoidAlgebra.induction_linear x ?_ ?_ ?_
  · simp only [map_zero]
  · intro y z hy hz
    simp only [map_add, hy, hz]
  · intro g r
    rw [MonoidAlgebra.mapRingHom_single, groupAlgebraAugmentation_single,
      groupAlgebraAugmentation_single]

end CompletedGroupAlgebra
