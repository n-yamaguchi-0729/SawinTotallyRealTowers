import ProCGroups.CompletedGroupAlgebra.Basic.AllFinite.Index

set_option autoImplicit false

/-!
# Completed Group Algebra / All Finite Functoriality / Comap

This module constructs the inverse-image finite quotient attached to a continuous group
homomorphism and the induced quotient homomorphism. It is the index-level input for all-finite
functoriality and has no dependency on augmentation theory.
-/

open scoped Topology

namespace CompletedGroupAlgebra

noncomputable section

open ProCGroups
open ProCGroups.ProC

universe v

variable (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/--
The inverse image of an open-finite quotient of \(H\) along a continuous homomorphism \(G\to
H\), regarded as an open-finite quotient of the profinite group \(G\). This is the index-level
operation underlying Lemma 5.3.5(e)'s functoriality in the group variable.
-/
def completedGroupAlgebraComapIndex
    (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) : CompletedGroupAlgebraIndex G := by
  let V₀ : OpenNormalSubgroup H := (OrderDual.ofDual V).1
  let W : OpenNormalSubgroup G := ProCGroups.OpenNormalSubgroup.comap φ hφ V₀
  refine OrderDual.toDual ⟨W, ?_⟩
  let f : G ⧸ (W : Subgroup G) →* H ⧸ (V₀ : Subgroup H) :=
    QuotientGroup.map _ _ φ (by
      intro g hg
      simpa [W, V₀] using hg)
  have hf : Function.Injective f := by
    intro x y hxy
    rcases QuotientGroup.mk'_surjective (W : Subgroup G) x with ⟨a, rfl⟩
    rcases QuotientGroup.mk'_surjective (W : Subgroup G) y with ⟨b, rfl⟩
    apply QuotientGroup.eq.2
    change φ (a⁻¹ * b) ∈ (V₀ : Subgroup H)
    have hv : (φ a)⁻¹ * φ b ∈ (V₀ : Subgroup H) := QuotientGroup.eq.1 hxy
    simpa using hv
  let : Finite (H ⧸ (V₀ : Subgroup H)) := (OrderDual.ofDual V).2
  exact Finite.of_injective f hf

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- The subgroup underlying the comap index is the subgroup-theoretic comap. -/
@[simp]
theorem completedGroupAlgebraComapIndex_subgroup
    (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) :
    (((OrderDual.ofDual (completedGroupAlgebraComapIndex (G := G) φ hφ V)).1 :
        OpenNormalSubgroup G) : Subgroup G) =
      (((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H).comap φ :=
  rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup H] in
/-- Comap of all-finite completed-group-algebra indices is monotone. -/
theorem completedGroupAlgebraComapIndex_mono
    (φ : G →* H) (hφ : Continuous φ)
    {V W : CompletedGroupAlgebraIndex H} (hVW : V ≤ W) :
    completedGroupAlgebraComapIndex (G := G) φ hφ V ≤
      completedGroupAlgebraComapIndex (G := G) φ hφ W := by
  change (((OrderDual.ofDual W).1 : OpenNormalSubgroup H) : Subgroup H).comap φ ≤
    (((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H).comap φ
  exact Subgroup.comap_mono hVW

/--
The quotient homomorphism \(G/\varphi^{-1}(V) \to H/V\) induced by a continuous homomorphism
\(\varphi: G \to H\).
-/
def completedGroupAlgebraComapQuotientMap
    (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) :
    CompletedGroupAlgebraQuotient G (completedGroupAlgebraComapIndex (G := G) φ hφ V) →*
      CompletedGroupAlgebraQuotient H V :=
  QuotientGroup.map _ _ φ (by
    intro g hg
    exact hg)

/--
The quotient map associated with the inverse-image subgroup sends the class of \(g\in G\) to the
class of \(\varphi(g)\in H\).
-/
@[simp]
theorem completedGroupAlgebraComapQuotientMap_mk
    (φ : G →* H) (hφ : Continuous φ)
    (V : CompletedGroupAlgebraIndex H) (g : G) :
    completedGroupAlgebraComapQuotientMap (G := G) φ hφ V
        (QuotientGroup.mk'
          ((((OrderDual.ofDual (completedGroupAlgebraComapIndex (G := G) φ hφ V)).1 :
            OpenNormalSubgroup G) : Subgroup G)) g) =
      QuotientGroup.mk'
        ((((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H)) (φ g) :=
  rfl

/-- A surjective homomorphism induces a surjective map on the comap quotients. -/
theorem completedGroupAlgebraComapQuotientMap_surjective
    (φ : G →* H) (hφ : Continuous φ)
    (hφsurj : Function.Surjective φ) (V : CompletedGroupAlgebraIndex H) :
    Function.Surjective (completedGroupAlgebraComapQuotientMap (G := G) φ hφ V) := by
  intro q
  rcases QuotientGroup.mk'_surjective
      ((((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H)) q with
    ⟨h, rfl⟩
  rcases hφsurj h with ⟨g, rfl⟩
  refine ⟨QuotientGroup.mk'
      ((((OrderDual.ofDual (completedGroupAlgebraComapIndex (G := G) φ hφ V)).1 :
        OpenNormalSubgroup G) : Subgroup G)) g, ?_⟩
  rw [completedGroupAlgebraComapQuotientMap_mk]

end

end CompletedGroupAlgebra
