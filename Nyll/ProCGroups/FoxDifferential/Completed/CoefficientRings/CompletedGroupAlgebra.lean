/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ProCGroups.CompletedGroupAlgebra.Basic.InClass.Stage
public import Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup

/-!
# Discrete integral group-algebra families for the Fox differential

Integral Fox coefficients use the common finite quotient and group-ring stage maps.
Their inverse system uses discrete stage topologies.
-/

@[expose] public section

namespace FoxDifferential

open _root_.CompletedGroupAlgebra
  (CompletedGroupAlgebraIndexInClass CompletedGroupAlgebraQuotientInClass)

open _root_.CompletedGroupAlgebra
  (CompletedGroupAlgebraStageInClass completedGroupAlgebraTransitionInClass
    completedGroupAlgebraTransitionInClass_id completedGroupAlgebraTransitionInClass_comp)

open Set
open ProCGroups
open ProCGroups.InverseSystems
open ProCGroups.ProC
open scoped Topology

noncomputable section

universe u v w

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The class-restricted inverse system of finite-stage integral group rings. -/
def completedGroupAlgebraSystemInClass
    (C : ProCGroups.FiniteGroupClass.{u}) :
    InverseSystem (I := CompletedGroupAlgebraIndexInClass G C) where
  X := CompletedGroupAlgebraStageInClass C ℤ G
  topologicalSpace := fun _ => ⊥
  map := fun {U V} hUV => completedGroupAlgebraTransitionInClass C ℤ G hUV
  continuous_map := by
    intro U V hUV
    let : TopologicalSpace (CompletedGroupAlgebraStageInClass C ℤ G U) := ⊥
    let : TopologicalSpace (CompletedGroupAlgebraStageInClass C ℤ G V) := ⊥
    let : DiscreteTopology (CompletedGroupAlgebraStageInClass C ℤ G V) := ⟨rfl⟩
    exact continuous_of_discreteTopology
  map_id := by
    intro U
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraTransitionInClass_id (R := ℤ) (G := G) C U)) x
  map_comp := by
    intro U V W hUV hVW
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (completedGroupAlgebraTransitionInClass_comp (R := ℤ) (G := G) C hUV hVW)) x

/-- Compatibility for a class-restricted completed group algebra family. -/
def CompletedGroupAlgebraCompatibleInClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (x : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      CompletedGroupAlgebraStageInClass C ℤ G U) : Prop :=
  (completedGroupAlgebraSystemInClass G C).Compatible x

/-- The class-restricted completed group algebra as an inverse-limit subtype. -/
abbrev CompletedGroupAlgebraInClass (C : ProCGroups.FiniteGroupClass.{u}) : Type _ :=
  {x : ∀ U : CompletedGroupAlgebraIndexInClass G C,
      CompletedGroupAlgebraStageInClass C ℤ G U //
    CompletedGroupAlgebraCompatibleInClass G C x}

/-- Projection from the class-restricted completed group algebra to one finite stage. -/
def completedGroupAlgebraProjectionInClass
    (C : ProCGroups.FiniteGroupClass.{u}) (U : CompletedGroupAlgebraIndexInClass G C) :
    CompletedGroupAlgebraInClass G C → CompletedGroupAlgebraStageInClass C ℤ G U :=
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
  Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid, Subgroup.mem_comap, MonoidHom.coe_ofClass,
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
  Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid, Subgroup.mem_comap, MonoidHom.coe_ofClass,
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
  Submonoid.mem_toSubsemigroup, Subgroup.mem_toSubmonoid, Subgroup.mem_comap, MonoidHom.coe_ofClass,
  OpenSubgroup.mem_toSubgroup]
  constructor <;> intro _ <;> trivial

end ComapInClass

end

end FoxDifferential
