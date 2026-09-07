import Mathlib.Algebra.MonoidAlgebra.MapDomain
import ProCGroups.ProC.OpenNormalSubgroups.ProCGroup

set_option autoImplicit false

/-!
# Fox differential: completed — coefficient rings — completed group algebra

The principal declarations in this module are:

- `CompletedGroupAlgebraIndexInClass`
  The index set for a completed group algebra over finite quotients belonging to a class `C`.
- `CompletedGroupAlgebraQuotientInClass`
  The finite quotient of `G` attached to one class-restricted completed-group-algebra stage.
- `completedGroupAlgebraTransitionInClass_id`
  Identity case for completedGroupAlgebraTransitionInClass_id.
- `completedGroupAlgebraTransitionInClass_comp`
  Composition lemma completedGroupAlgebraTransitionInClass_comp.
-/

namespace FoxDifferential

open Set
open ProCGroups
open ProCGroups.InverseSystems
open ProCGroups.ProC
open scoped Topology

noncomputable section

universe u v w

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The index set for a completed group algebra over finite quotients belonging to a class `C`. -/
abbrev CompletedGroupAlgebraIndexInClass (C : ProCGroups.FiniteGroupClass.{u}) :=
  OrderDual (OpenNormalSubgroupInClass C G)

/-- The finite quotient of `G` attached to one class-restricted completed-group-algebra stage. -/
abbrev CompletedGroupAlgebraQuotientInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) : Type _ :=
  (openNormalSubgroupInClassSystem C G).X U

/-- The discrete group ring over one class-restricted finite quotient of `G`. -/
abbrev CompletedGroupAlgebraStageInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) : Type _ :=
  MonoidAlgebra ℤ (CompletedGroupAlgebraQuotientInClass G C U)

/-- The transition map between two class-restricted completed-group-algebra stages. -/
def completedGroupAlgebraTransitionInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    CompletedGroupAlgebraStageInClass G C V →+*
      CompletedGroupAlgebraStageInClass G C U :=
  MonoidAlgebra.mapDomainRingHom ℤ
    (OpenNormalSubgroupInClass.map
      (C := C) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)

/-- Identity case for completedGroupAlgebraTransitionInClass_id. -/
@[simp]
theorem completedGroupAlgebraTransitionInClass_id
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    completedGroupAlgebraTransitionInClass G C (le_rfl : U ≤ U) = RingHom.id _ := by
  rw [completedGroupAlgebraTransitionInClass, OpenNormalSubgroupInClass.map_id]
  exact MonoidAlgebra.mapDomainRingHom_id
    (R := ℤ) (M := CompletedGroupAlgebraQuotientInClass G C U)

/-- Composition lemma completedGroupAlgebraTransitionInClass_comp. -/
@[simp]
theorem completedGroupAlgebraTransitionInClass_comp
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V W : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) (hVW : V ≤ W) :
    (completedGroupAlgebraTransitionInClass G C hUV).comp
        (completedGroupAlgebraTransitionInClass G C hVW) =
      completedGroupAlgebraTransitionInClass G C (hUV.trans hVW) := by
  unfold completedGroupAlgebraTransitionInClass
  exact
    (MonoidAlgebra.mapDomainRingHom_comp (R := ℤ)
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual V) (V := OrderDual.ofDual W) hVW)).symm.trans
      (congrArg (MonoidAlgebra.mapDomainRingHom ℤ)
        (OpenNormalSubgroupInClass.map_comp
          (C := C) (G := G)
          (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) (W := OrderDual.ofDual W)
          hUV hVW))

/-- The class-restricted inverse system of finite-stage integral group rings. -/
def completedGroupAlgebraSystemInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    InverseSystem (I := CompletedGroupAlgebraIndexInClass G C) where
  X := CompletedGroupAlgebraStageInClass G C
  topologicalSpace := fun _ => ⊥
  map := fun {U V} hUV => completedGroupAlgebraTransitionInClass G C hUV
  continuous_map := by
    intro U V hUV
    let : TopologicalSpace (CompletedGroupAlgebraStageInClass G C U) := ⊥
    let : TopologicalSpace (CompletedGroupAlgebraStageInClass G C V) := ⊥
    let : DiscreteTopology (CompletedGroupAlgebraStageInClass G C V) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro U
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraTransitionInClass_id G C U)) x
  map_comp := by
    intro U V W hUV hVW
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraTransitionInClass_comp G C hUV hVW)) x

/-- The quotient ring map from `ℤ[G]` to one class-restricted finite stage. -/
def completedGroupAlgebraStageMapInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    MonoidAlgebra ℤ G →+* CompletedGroupAlgebraStageInClass G C U :=
  MonoidAlgebra.mapDomainRingHom ℤ
    (openNormalSubgroupInClassProj (C := C) (G := G) U)

/-- Evaluation formula for completedGroupAlgebraStageMapInClass_of. -/
@[simp]
theorem completedGroupAlgebraStageMapInClass_of
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) (g : G) :
    completedGroupAlgebraStageMapInClass G C U (MonoidAlgebra.of ℤ _ g) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U g) 1 := by
  classical
  change
    MonoidAlgebra.mapDomain
        (openNormalSubgroupInClassProj (C := C) (G := G) U)
        (MonoidAlgebra.single g 1) =
      MonoidAlgebra.single (openNormalSubgroupInClassProj (C := C) (G := G) U g) 1
  exact MonoidAlgebra.mapDomain_single

/-- Compatibility lemma completedGroupAlgebraStageMapInClass_compatible. -/
@[simp]
theorem completedGroupAlgebraStageMapInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{u})
    {U V : CompletedGroupAlgebraIndexInClass G C} (hUV : U ≤ V) :
    (completedGroupAlgebraTransitionInClass G C hUV).comp
        (completedGroupAlgebraStageMapInClass G C V) =
      completedGroupAlgebraStageMapInClass G C U := by
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
    (MonoidAlgebra.mapDomainRingHom_comp (R := ℤ)
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV)
      (openNormalSubgroupInClassProj (C := C) (G := G) V)).symm.trans
      (congrArg (MonoidAlgebra.mapDomainRingHom ℤ) hproj)

/-- Compatibility for a class-restricted completed group algebra family. -/
def CompletedGroupAlgebraCompatibleInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      CompletedGroupAlgebraStageInClass G C U) : Prop :=
  (completedGroupAlgebraSystemInClass G C).Compatible x

/-- The class-restricted completed group algebra as an inverse-limit subtype. -/
abbrev CompletedGroupAlgebraInClass (C : ProCGroups.FiniteGroupClass.{u}) : Type _ :=
  {x : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      CompletedGroupAlgebraStageInClass G C U //
    CompletedGroupAlgebraCompatibleInClass G C x}

/-- Projection from the class-restricted completed group algebra to one finite stage. -/
def completedGroupAlgebraProjectionInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraInClass G C → CompletedGroupAlgebraStageInClass G C U :=
  (completedGroupAlgebraSystemInClass G C).projection U

section ComapInClass

variable {G H : Type u}
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Pull back a class-restricted finite quotient along a continuous homomorphism.

The hereditary hypothesis is the precise extra closure property needed: the pulled-back quotient
embeds into the target quotient, so membership in `C` follows from closure under subgroups. -/
def completedGroupAlgebraComapIndexInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψ : ContinuousMonoidHom G H) (U : CompletedGroupAlgebraIndexInClass H C) :
    CompletedGroupAlgebraIndexInClass G C := by
  let V : OpenNormalSubgroup H := (OrderDual.ofDual U).1
  let W : OpenNormalSubgroup G := OpenNormalSubgroup.comap ψ.toMonoidHom ψ.continuous_toFun V
  refine OrderDual.toDual ⟨W, ?_⟩
  let f : G ⧸ (W : Subgroup G) →* H ⧸ (V : Subgroup H) :=
    QuotientGroup.map _ _ ψ.toMonoidHom (by
      intro g hg
      simpa [W] using hg)
  have hf : Function.Injective f := by
    intro x y hxy
    rcases QuotientGroup.mk'_surjective (W : Subgroup G) x with ⟨a, rfl⟩
    rcases QuotientGroup.mk'_surjective (W : Subgroup G) y with ⟨b, rfl⟩
    apply QuotientGroup.eq.2
    change ψ (a⁻¹ * b) ∈ (V : Subgroup H)
    have hv : (ψ a)⁻¹ * ψ b ∈ (V : Subgroup H) := QuotientGroup.eq.1 hxy
    simpa using hv
  exact hC.of_injective (OrderDual.ofDual U).2 f hf

/-- The finite quotient map induced by a continuous homomorphism after pulling back the stage. -/
def completedGroupAlgebraComapQuotientMapInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψ : ContinuousMonoidHom G H) (U : CompletedGroupAlgebraIndexInClass H C) :
    CompletedGroupAlgebraQuotientInClass G C
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hC ψ U) →*
      CompletedGroupAlgebraQuotientInClass H C U := by
  let V : OpenNormalSubgroup H := (OrderDual.ofDual U).1
  let W : OpenNormalSubgroup G := OpenNormalSubgroup.comap ψ.toMonoidHom ψ.continuous_toFun V
  exact QuotientGroup.map _ _ ψ.toMonoidHom (by
    intro g hg
    simpa [W, completedGroupAlgebraComapIndexInClass] using hg)

/-- Evaluation formula for completedGroupAlgebraComapQuotientMapInClass_mk. -/
@[simp]
theorem completedGroupAlgebraComapQuotientMapInClass_mk
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψ : ContinuousMonoidHom G H) (U : CompletedGroupAlgebraIndexInClass H C) (g : G) :
    completedGroupAlgebraComapQuotientMapInClass
        (G := G) (H := H) C hC ψ U
        (QuotientGroup.mk'
          ((((OrderDual.ofDual
            (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hC ψ U)).1 :
              OpenNormalSubgroup G) : Subgroup G)) g) =
      QuotientGroup.mk' ((((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H))
        (ψ g) := rfl

/-- Surjectivity lemma completedGroupAlgebraComapQuotientMapInClass_surjective_of_surjective. -/
theorem completedGroupAlgebraComapQuotientMapInClass_surjective_of_surjective
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψ : ContinuousMonoidHom G H) (hψ : Function.Surjective ψ)
    (U : CompletedGroupAlgebraIndexInClass H C) :
    Function.Surjective
      (completedGroupAlgebraComapQuotientMapInClass (G := G) (H := H) C hC ψ U) := by
  intro h
  rcases QuotientGroup.mk'_surjective
      ((((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H)) h with ⟨a, rfl⟩
  rcases hψ a with ⟨g, rfl⟩
  refine ⟨QuotientGroup.mk'
      ((((OrderDual.ofDual
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hC ψ U)).1 :
          OpenNormalSubgroup G) : Subgroup G)) g, ?_⟩
  rw [completedGroupAlgebraComapQuotientMapInClass_mk]

omit [IsTopologicalGroup G] in
/-- 有限群クラスを固定した 標準写像が対応する有限段階・係数段階・augmentation 構造と両立することを述べる。 -/
theorem completedGroupAlgebraComapIndexInClass_mono
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψ : ContinuousMonoidHom G H) {U V : CompletedGroupAlgebraIndexInClass H C}
    (hUV : U ≤ V) :
    completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hC ψ U ≤
      completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hC ψ V := by
  change
    Subgroup.comap ψ.toMonoidHom
        (((OrderDual.ofDual V).1 : OpenNormalSubgroup H) : Subgroup H) ≤
      Subgroup.comap ψ.toMonoidHom
        (((OrderDual.ofDual U).1 : OpenNormalSubgroup H) : Subgroup H)
  exact Subgroup.comap_mono hUV

/-- Compatibility lemma completedGroupAlgebraComapQuotientMapInClass_compatible. -/
@[simp]
theorem completedGroupAlgebraComapQuotientMapInClass_compatible
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (ψ : ContinuousMonoidHom G H) {U V : CompletedGroupAlgebraIndexInClass H C}
    (hUV : U ≤ V) :
    (OpenNormalSubgroupInClass.map
        (C := C) (G := H)
        (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV).comp
        (completedGroupAlgebraComapQuotientMapInClass (G := G) (H := H) C hC ψ V) =
      (completedGroupAlgebraComapQuotientMapInClass (G := G) (H := H) C hC ψ U).comp
        (OpenNormalSubgroupInClass.map
          (C := C) (G := G)
          (U := OrderDual.ofDual
            (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hC ψ U))
          (V := OrderDual.ofDual
            (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hC ψ V))
          (completedGroupAlgebraComapIndexInClass_mono (G := G) (H := H) C hC ψ hUV)) := by
  ext q
  rcases QuotientGroup.mk'_surjective
      ((((OrderDual.ofDual
        (completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hC ψ V)).1 :
          OpenNormalSubgroup G) : Subgroup G)) q with ⟨g, rfl⟩
  rfl

/-- Pulling a finite quotient back along the identity continuous homomorphism gives the same
class-restricted index.  This is intentionally an equality theorem, since dependent inverse-limit
indices are often not definitionally equal after target naturality rewrites. -/
@[simp]
theorem completedGroupAlgebraComapIndexInClass_id
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    (U : CompletedGroupAlgebraIndexInClass G C) :
    completedGroupAlgebraComapIndexInClass (G := G) (H := G) C hC
        (ContinuousMonoidHom.id G) U = U := by
  apply OrderDual.ofDual.injective
  ext x
  simp only [completedGroupAlgebraComapIndexInClass, ContinuousMonoidHom.coe_toMonoidHom,
  OrderDual.ofDual_toDual, OpenNormalSubgroup.toSubgroup_comap, Subsemigroup.mem_carrier,
  Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid, Subgroup.mem_comap, MonoidHom.coe_coe,
  ContinuousMonoidHom.id_toFun, OpenSubgroup.mem_toSubgroup]

omit [IsTopologicalGroup G] in
/-- Pullback of class-restricted finite quotients is functorial for continuous target maps.

This is the index-level rewrite needed when the two inverse-limit stage indices produced by a
composite target map are propositionally, but not definitionally, the same. -/
@[simp]
theorem completedGroupAlgebraComapIndexInClass_comp
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    {K : Type u} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (φ : G →ₜ* H) (ψ : H →ₜ* K) (U : CompletedGroupAlgebraIndexInClass K C) :
    completedGroupAlgebraComapIndexInClass (G := G) (H := K) C hC (ψ.comp φ) U =
      completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hC φ
        (completedGroupAlgebraComapIndexInClass (G := H) (H := K) C hC ψ U) := by
  apply OrderDual.ofDual.injective
  ext x
  simp only [completedGroupAlgebraComapIndexInClass, ContinuousMonoidHom.coe_toMonoidHom,
  OrderDual.ofDual_toDual, OpenNormalSubgroup.toSubgroup_comap, Subsemigroup.mem_carrier,
  Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid, Subgroup.mem_comap, MonoidHom.coe_coe,
  ContinuousMonoidHom.comp_toFun, OpenSubgroup.mem_toSubgroup]

omit [IsTopologicalGroup G] in
/-- Pulling back the canonical trivial quotient gives the canonical trivial quotient. -/
@[simp]
theorem completedGroupAlgebraComapIndexInClass_top
    (C : ProCGroups.FiniteGroupClass.{u}) (hC : ProCGroups.FiniteGroupClass.Hereditary C)
    [ProCGroups.FiniteGroupClass.ContainsTrivialQuotients C]
    (ψ : G →ₜ* H) :
    completedGroupAlgebraComapIndexInClass (G := G) (H := H) C hC ψ
        (OrderDual.toDual (OpenNormalSubgroupInClass.top (C := C) (G := H))) =
      OrderDual.toDual (OpenNormalSubgroupInClass.top (C := C) (G := G)) := by
  apply OrderDual.ofDual.injective
  ext x
  simp only [completedGroupAlgebraComapIndexInClass, ContinuousMonoidHom.coe_toMonoidHom,
  OrderDual.ofDual_toDual, OpenNormalSubgroup.toSubgroup_comap, Subsemigroup.mem_carrier,
  Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid, Subgroup.mem_comap, MonoidHom.coe_coe,
  OpenSubgroup.mem_toSubgroup]
  constructor <;> intro _ <;> trivial

end ComapInClass

end

end FoxDifferential
