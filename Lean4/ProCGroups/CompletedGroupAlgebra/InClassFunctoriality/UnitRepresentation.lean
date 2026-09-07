import ProCGroups.CompletedGroupAlgebra.InClassFunctoriality.Comparison

set_option autoImplicit false

/-!
# Unit representations in the in-class completion

This file studies the continuous group-like unit representation in an in-class completed group
algebra. Its image spans densely, and scalar restriction along it equips profinite modules with a
continuous group action.
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

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The concrete class-indexed unit representation evaluates to the corresponding completed
group-like element.
-/
@[simp]
theorem completedGroupAlgebraUnitRepresentationInClassConcrete_val
    (C : ProCGroups.FiniteGroupClass.{v})
    (g : G) :
    ((completedGroupAlgebraUnitRepresentation R G (CompletedGroupAlgebraInClass C R G)
        (toCompletedGroupAlgebraInClassRingHom C R G) g :
        (CompletedGroupAlgebraInClass C R G)ˣ) : CompletedGroupAlgebraInClass C R G) =
      completedGroupAlgebraOfInClass C R G g :=
  rfl

/--
The \(C\)-indexed canonical unit representation is continuous after forgetting to
\(\widehat{R[G]}_{C}\).
-/
theorem continuous_completedGroupAlgebraUnitRepresentationInClassConcrete_val
    (C : ProCGroups.FiniteGroupClass.{v}) :
    Continuous fun g : G =>
      ((completedGroupAlgebraUnitRepresentation R G (CompletedGroupAlgebraInClass C R G)
        (toCompletedGroupAlgebraInClassRingHom C R G) g :
        (CompletedGroupAlgebraInClass C R G)ˣ) : CompletedGroupAlgebraInClass C R G) := by
  apply (continuous_completedGroupAlgebraOfInClass (R := R) (G := G) C).congr
  intro g
  exact (completedGroupAlgebraUnitRepresentationInClassConcrete_val
    (R := R) (G := G) C g).symm

/-- The dense abstract map lands in the span of class-indexed completed group-like elements. -/
theorem toCompletedGroupAlgebraInClassRingHom_mem_span_completedGroupAlgebraOfInClass
    (C : ProCGroups.FiniteGroupClass.{v})
    (x : MonoidAlgebra R G) :
    toCompletedGroupAlgebraInClassRingHom C R G x ∈
      Submodule.span R (Set.range (completedGroupAlgebraOfInClass C R G)) := by
  classical
  refine MonoidAlgebra.induction_linear
    (motive := fun x : MonoidAlgebra R G =>
      toCompletedGroupAlgebraInClassRingHom C R G x ∈
        Submodule.span R (Set.range (completedGroupAlgebraOfInClass C R G)))
    x ?_ ?_ ?_
  · -- The zero case.
      rw [show toCompletedGroupAlgebraInClassRingHom C R G (0 : MonoidAlgebra R G) =
          (0 : CompletedGroupAlgebraInClass C R G) by
        exact map_zero (toCompletedGroupAlgebraInClassRingHom C R G)]
      exact Submodule.zero_mem _
  · intro a b ha hb
    rw [map_add]
    exact Submodule.add_mem _ ha hb
  · intro g r
    have hsingle :
        toCompletedGroupAlgebraInClassRingHom C R G (MonoidAlgebra.single g r) =
          r • completedGroupAlgebraOfInClass C R G g := by
      rw [← MonoidAlgebra.smul_of]
      change toCompletedGroupAlgebraInClass C R G (r • MonoidAlgebra.of R G g) =
        r • completedGroupAlgebraOfInClass C R G g
      rw [toCompletedGroupAlgebraInClass_smul]
      rfl
    rw [hsingle]
    exact Submodule.smul_mem _ r (Submodule.subset_span ⟨g, rfl⟩)

/--
The \(C\)-indexed completed group-like elements topologically generate \(\widehat{R[G]}_{C}\) as
an \(R\)-module, for pro-\(C\) groups and formation classes.
-/
theorem completedGroupAlgebraOfInClass_dense_span
    (C : ProCGroups.FiniteGroupClass.{v})
    (hForm : ProCGroups.FiniteGroupClass.Formation C) (hG : HasOpenNormalBasisInClass C G) :
    closure (Submodule.span R (Set.range (completedGroupAlgebraOfInClass C R G)) :
      Set (CompletedGroupAlgebraInClass C R G)) = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro y
  have hy :
      y ∈ closure (Set.range (toCompletedGroupAlgebraInClassRingHom C R G)) := by
    have hdense : DenseRange (toCompletedGroupAlgebraInClassRingHom C R G) := by
      change DenseRange (toCompletedGroupAlgebraInClass C R G)
      exact denseRange_toCompletedGroupAlgebraInClass (R := R) (G := G) C hForm hG
    rw [hdense.closure_range]
    exact Set.mem_univ y
  exact closure_mono (by
    intro z hz
    rcases hz with ⟨x, rfl⟩
    exact toCompletedGroupAlgebraInClassRingHom_mem_span_completedGroupAlgebraOfInClass
      (R := R) (G := G) C x) hy

/--
A continuous module over the \(C\)-indexed completed group algebra inherits the natural
continuous \(G\)-module structure via the group-like units.
-/
theorem completedGroupAlgebraInClass_module_induces_continuous_gmodule
    (C : ProCGroups.FiniteGroupClass.{v})
    (A : Type (max u v)) [AddCommGroup A] [TopologicalSpace A]
    [Module (CompletedGroupAlgebraInClass C R G) A]
    [ContinuousSMul (CompletedGroupAlgebraInClass C R G) A] :
    letI : DistribMulAction G A :=
      unitRepresentationDistribMulAction G (CompletedGroupAlgebraInClass C R G) A
        (completedGroupAlgebraUnitRepresentation R G (CompletedGroupAlgebraInClass C R G)
            (toCompletedGroupAlgebraInClassRingHom C R G))
    ContinuousSMul G A := by
  let : DistribMulAction G A :=
    unitRepresentationDistribMulAction G (CompletedGroupAlgebraInClass C R G) A
      (completedGroupAlgebraUnitRepresentation R G (CompletedGroupAlgebraInClass C R G)
        (toCompletedGroupAlgebraInClassRingHom C R G))
  exact unitRepresentation_continuousSMul G (CompletedGroupAlgebraInClass C R G) A
    (completedGroupAlgebraUnitRepresentation R G (CompletedGroupAlgebraInClass C R G)
        (toCompletedGroupAlgebraInClassRingHom C R G))
    (continuous_completedGroupAlgebraUnitRepresentationInClassConcrete_val (R := R) (G := G) C )

end

end CompletedGroupAlgebra
