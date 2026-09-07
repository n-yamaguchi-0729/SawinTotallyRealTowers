import ProCGroups.CompletedGroupAlgebra.Basic.InClass.Index

set_option autoImplicit false

/-!
# Pulling back in-class quotient indices

An open-normal quotient index on the target pulls back along a continuous group homomorphism to
an index on the source. This file defines that comap, the induced finite quotient map, and its
monotonicity, compatibility, and surjectivity properties.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC
open ProCGroups.InverseSystems

universe u v w

variable (R : Type u) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The inverse image of a \(C\)-quotient of \(H\) along a continuous homomorphism \(G\to H\), again
as a \(C\)-quotient of \(G\), when \(C\) is hereditary.
-/
def completedGroupAlgebraComapIndexInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (V : CompletedGroupAlgebraIndexInClass H C) :
    CompletedGroupAlgebraIndexInClass G C :=
  let φc : G →ₜ* H := { toMonoidHom := φ, continuous_toFun := hφ }
  OrderDual.toDual
    (OpenNormalSubgroupInClass.comap (C := C) (G := G) hHer φc (OrderDual.ofDual V))

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The comap of an open normal subgroup along a continuous homomorphism is again open normal. -/
@[simp]
theorem completedGroupAlgebraComapIndexInClass_subgroup
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (V : CompletedGroupAlgebraIndexInClass H C) :
    (((OrderDual.ofDual (completedGroupAlgebraComapIndexInClass
        (G := G) (H := H) C hHer φ hφ V)).1 : OpenNormalSubgroup G) : Subgroup G) =
      (((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H).comap φ :=
  rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Comap indices are monotone with respect to refinement of open normal subgroups. -/
theorem completedGroupAlgebraComapIndexInClass_mono
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ)
    {V W : CompletedGroupAlgebraIndexInClass H C} (hVW : V ≤ W) :
    completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V ≤
      completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ W := by
  change (((OrderDual.ofDual W).1 : OpenNormalSubgroup H) : Subgroup H).comap φ ≤
    (((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H).comap φ
  exact Subgroup.comap_mono hVW

/-- The quotient homomorphism \(G/\varphi^{-1}(V) \to H/V\) for a \(C\)-indexed quotient. -/
def completedGroupAlgebraComapQuotientMapInClass
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (V : CompletedGroupAlgebraIndexInClass H C) :
    CompletedGroupAlgebraQuotientInClass G C
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V) →*
      CompletedGroupAlgebraQuotientInClass H C V :=
  QuotientGroup.map _ _ φ (by
    intro g hg
    exact hg)

/-- The quotient map attached to a comap index sends a coset to the coset of its image. -/
@[simp]
theorem completedGroupAlgebraComapQuotientMapInClass_mk
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (V : CompletedGroupAlgebraIndexInClass H C) (g : G) :
    completedGroupAlgebraComapQuotientMapInClass (G := G) (H := H) C hHer φ hφ V
        (QuotientGroup.mk'
          ((((OrderDual.ofDual (completedGroupAlgebraComapIndexInClass
            (G := G) (H := H) C hHer φ hφ V)).1 : OpenNormalSubgroup G) :
              Subgroup G)) g) =
      QuotientGroup.mk' ((((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H))
        (φ g) :=
  rfl

/--
A surjective group homomorphism induces a surjective map on the corresponding finite quotients.
-/
theorem completedGroupAlgebraComapQuotientMapInClass_surjective_of_surjective
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ) (hφsurj : Function.Surjective φ)
    (V : CompletedGroupAlgebraIndexInClass H C) :
    Function.Surjective
      (completedGroupAlgebraComapQuotientMapInClass (G := G) (H := H) C hHer φ hφ V) := by
  intro q
  rcases QuotientGroup.mk'_surjective
      ((((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H)) q with
    ⟨h, rfl⟩
  rcases hφsurj h with ⟨g, rfl⟩
  refine ⟨QuotientGroup.mk'
      ((((OrderDual.ofDual (completedGroupAlgebraComapIndexInClass
        (G := G) (H := H) C hHer φ hφ V)).1 : OpenNormalSubgroup G) : Subgroup G)) g, ?_⟩
  rw [completedGroupAlgebraComapQuotientMapInClass_mk]

/--
The class-restricted completed group-algebra pullback quotient map is compatible with transition
maps and coordinate projections for the completed group algebra.
-/
@[simp]
theorem completedGroupAlgebraComapQuotientMapInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{v}) (hHer : ProCGroups.FiniteGroupClass.Hereditary C)
    (φ : G →* H) (hφ : Continuous φ)
    {V W : CompletedGroupAlgebraIndexInClass H C} (hVW : V ≤ W) :
    (OpenNormalSubgroupInClass.map
        (C := C) (G := H)
        (U := OrderDual.ofDual V) (V := OrderDual.ofDual W) hVW).comp
        (completedGroupAlgebraComapQuotientMapInClass (G := G) (H := H) C hHer φ hφ W) =
      (completedGroupAlgebraComapQuotientMapInClass (G := G) (H := H) C hHer φ hφ V).comp
        (OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual
            (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ V))
          (V := OrderDual.ofDual
            (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ W))
          (completedGroupAlgebraComapIndexInClass_mono
            (G := G) (H := H) C hHer φ hφ hVW)) := by
  ext q
  rcases QuotientGroup.mk'_surjective
      ((((OrderDual.ofDual
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hHer φ hφ W)).1 :
          OpenNormalSubgroup G) : Subgroup G)) q with ⟨g, rfl⟩
  rfl

end

end CompletedGroupAlgebra
