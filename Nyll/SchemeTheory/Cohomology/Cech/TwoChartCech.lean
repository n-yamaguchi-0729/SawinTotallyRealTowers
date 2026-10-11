/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_TwoChartCech.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.CoherentBaseChange
import Mathlib.Algebra.Algebra.Hom
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Cech data on two charts

This file defines algebraic chart covers and their section modules, the Cech difference,
its kernel and cokernel, and their comparison maps under scalar extension. It also defines
two-term models whose kernel and cokernel comparisons remain bijective after base change.
-/

noncomputable section

open scoped TensorProduct

universe u v w

namespace TwoChartCech

/-- R-algebra data for two charts and their overlap. -/
structure Cover (R : Type u) [CommRing R] where
  /-- The ring assigned to the first chart. -/
  A0 : Type v
  /-- The ring assigned to the second chart. -/
  A1 : Type v
  /-- The ring assigned to the overlap of the two charts. -/
  A01 : Type v
  /-- The commutative ring structure on the first chart ring. -/
  [A0_commRing : CommRing A0]
  /-- The base ring algebra structure on the first chart ring. -/
  [A0_algebra : Algebra R A0]
  /-- The commutative ring structure on the second chart ring. -/
  [A1_commRing : CommRing A1]
  /-- The base ring algebra structure on the second chart ring. -/
  [A1_algebra : Algebra R A1]
  /-- The commutative ring structure on the overlap ring. -/
  [A01_commRing : CommRing A01]
  /-- The base ring algebra structure on the overlap ring. -/
  [A01_algebra : Algebra R A01]
  /-- Restriction from the first chart ring to the overlap ring. -/
  ρ0 : A0 →ₐ[R] A01
  /-- Restriction from the second chart ring to the overlap ring. -/
  ρ1 : A1 →ₐ[R] A01

attribute [instance] Cover.A0_commRing Cover.A0_algebra Cover.A1_commRing Cover.A1_algebra
  Cover.A01_commRing Cover.A01_algebra

/-- Modules on two charts and their overlap, with scalar compatible restriction maps. -/
structure Sections {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R) where
  /-- The module of sections on the first chart. -/
  M0 : Type w
  /-- The module of sections on the second chart. -/
  M1 : Type w
  /-- The module of sections on the overlap. -/
  M01 : Type w
  /-- The additive commutative group structure on the first chart sections. -/
  [M0_addCommGroup : AddCommGroup M0]
  /-- The action of the first chart ring on its section module. -/
  [M0_moduleA : Module 𝒰.A0 M0]
  /-- The base ring module structure on the first chart sections. -/
  [M0_module : Module R M0]
  /-- Compatibility of the base ring and first chart scalar actions. -/
  [M0_tower : IsScalarTower R 𝒰.A0 M0]
  /-- The additive commutative group structure on the second chart sections. -/
  [M1_addCommGroup : AddCommGroup M1]
  /-- The action of the second chart ring on its section module. -/
  [M1_moduleA : Module 𝒰.A1 M1]
  /-- The base ring module structure on the second chart sections. -/
  [M1_module : Module R M1]
  /-- Compatibility of the base ring and second chart scalar actions. -/
  [M1_tower : IsScalarTower R 𝒰.A1 M1]
  /-- The additive commutative group structure on the overlap sections. -/
  [M01_addCommGroup : AddCommGroup M01]
  /-- The action of the overlap ring on its section module. -/
  [M01_moduleA : Module 𝒰.A01 M01]
  /-- The base ring module structure on the overlap sections. -/
  [M01_module : Module R M01]
  /-- Compatibility of the base ring and overlap scalar actions. -/
  [M01_tower : IsScalarTower R 𝒰.A01 M01]
  /-- The base ring linear restriction from the first chart to the overlap. -/
  r0 : M0 →ₗ[R] M01
  /-- The base ring linear restriction from the second chart to the overlap. -/
  r1 : M1 →ₗ[R] M01
  /-- The first restriction transports chart scalars through `ρ0`. -/
  r0_smul : ∀ (a : 𝒰.A0) (m : M0), r0 (a • m) = 𝒰.ρ0 a • r0 m
  /-- The second restriction transports chart scalars through `ρ1`. -/
  r1_smul : ∀ (a : 𝒰.A1) (m : M1), r1 (a • m) = 𝒰.ρ1 a • r1 m

attribute [instance] Sections.M0_addCommGroup Sections.M0_moduleA Sections.M0_module
  Sections.M0_tower Sections.M1_addCommGroup Sections.M1_moduleA Sections.M1_module
  Sections.M1_tower Sections.M01_addCommGroup Sections.M01_moduleA Sections.M01_module
  Sections.M01_tower

namespace Sections

variable {R : Type u} [CommRing R] {𝒰 : Cover.{u, v} R} (S : Sections.{u, v, w} 𝒰)

/-- The Cech difference sending a pair of sections to `r1 s.2 - r0 s.1`. -/
def cechDiff : S.M0 × S.M1 →ₗ[R] S.M01 := (-S.r0).coprod S.r1

theorem cechDiff_apply (s : S.M0 × S.M1) : S.cechDiff s = S.r1 s.2 - S.r0 s.1 := by
  simp [cechDiff, LinearMap.coprod_apply, sub_eq_neg_add]

/-- Compatible pairs of chart sections, forming the kernel of the Cech difference. -/
abbrev H0 : Submodule R (S.M0 × S.M1) := LinearMap.ker S.cechDiff

theorem mem_H0_iff (s : S.M0 × S.M1) : s ∈ S.H0 ↔ S.r0 s.1 = S.r1 s.2 := by
  rw [LinearMap.mem_ker, cechDiff_apply, sub_eq_zero, eq_comm]

/-- Overlap sections modulo the image of the Cech difference. -/
abbrev H1 : Type w := S.M01 ⧸ LinearMap.range S.cechDiff

end Sections

namespace Cover

variable {R : Type u} [CommRing R] (𝒰 : Cover.{u, v} R)

/-- Two chart section data with transition unit `t`, multiplying the second restriction by `t`. -/
@[reducible] def lineBundle (t : 𝒰.A01ˣ) : Sections.{u, v, v} 𝒰 where
  M0 := 𝒰.A0
  M1 := 𝒰.A1
  M01 := 𝒰.A01
  r0 := 𝒰.ρ0.toLinearMap
  r1 := (t : 𝒰.A01) • 𝒰.ρ1.toLinearMap
  r0_smul a m := by simp
  r1_smul a m := by simp [mul_left_comm]

@[simp] theorem lineBundle_r0_apply (t : 𝒰.A01ˣ) (p : 𝒰.A0) : (𝒰.lineBundle t).r0 p = 𝒰.ρ0 p := rfl
@[simp] theorem lineBundle_r1_apply (t : 𝒰.A01ˣ) (p : 𝒰.A1) :
    (𝒰.lineBundle t).r1 p = (t : 𝒰.A01) * 𝒰.ρ1 p := rfl

theorem mem_H0_lineBundle_iff (t : 𝒰.A01ˣ) (p : 𝒰.A0 × 𝒰.A1) :
    p ∈ (𝒰.lineBundle t).H0 ↔ 𝒰.ρ0 p.1 = (t : 𝒰.A01) * 𝒰.ρ1 p.2 :=
  (𝒰.lineBundle t).mem_H0_iff p

/-- The two chart section datum with transition unit equal to one. -/
abbrev structureSheaf : Sections.{u, v, v} 𝒰 := 𝒰.lineBundle 1

theorem mem_H0_structureSheaf_iff (p : 𝒰.A0 × 𝒰.A1) :
    p ∈ 𝒰.structureSheaf.H0 ↔ 𝒰.ρ0 p.1 = 𝒰.ρ1 p.2 := by
  rw [mem_H0_lineBundle_iff, Units.val_one, one_mul]

end Cover

section Dock

variable {R : Type u} [CommRing R]
variable {C0 : Type v} {C1 : Type v} [AddCommGroup C0] [Module R C0] [AddCommGroup C1] [Module R C1]

/-- The natural map from the tensor product of a kernel to the kernel of the map after extending
scalars. -/
def kerBaseChangeHom (d : C0 →ₗ[R] C1) (A : Type w) [CommRing A] [Algebra R A] :
    A ⊗[R] (LinearMap.ker d) →ₗ[A] LinearMap.ker (d.baseChange A) :=
  ((LinearMap.ker d).subtype.baseChange A).codRestrict (LinearMap.ker (d.baseChange A))
    (fun x => by
      rw [LinearMap.mem_ker, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      have h : d ∘ₗ (LinearMap.ker d).subtype = 0 := by
        ext ⟨y, hy⟩
        exact hy
      rw [h, LinearMap.baseChange_zero, LinearMap.zero_apply])

theorem kerBaseChangeHom_apply_coe (d : C0 →ₗ[R] C1) (A : Type w) [CommRing A] [Algebra R A]
    (x : A ⊗[R] (LinearMap.ker d)) :
    (kerBaseChangeHom d A x : A ⊗[R] C0) = (LinearMap.ker d).subtype.baseChange A x :=
  rfl

/-- The map on kernels induced by a commuting square of linear maps. -/
def kerMap {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) : LinearMap.ker dK →ₗ[R] LinearMap.ker d :=
  ι0.restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, comm, LinearMap.comp_apply, hx, map_zero]

/-- The map on cokernels induced by a commuting square of linear maps. -/
def cokerMap {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) : (K1 ⧸ LinearMap.range dK) →ₗ[R] (C1 ⧸ LinearMap.range d) :=
  Submodule.mapQ _ _ ι1 fun y hy => by
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [Submodule.mem_comap, ← LinearMap.comp_apply, ← comm, LinearMap.comp_apply]
    exact LinearMap.mem_range_self _ _

/-- The induced map on kernels after extending scalars to `A`. -/
def kerMapBaseChange {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (A : Type w) [CommRing A] [Algebra R A] :
    LinearMap.ker (dK.baseChange A) →ₗ[A] LinearMap.ker (d.baseChange A) :=
  (ι0.baseChange A).restrict fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, comm, LinearMap.baseChange_comp,
      LinearMap.comp_apply, hx, map_zero]

/-- The induced map on cokernels after extending scalars to `A`. -/
def cokerMapBaseChange {K0 : Type v} {K1 : Type v} [AddCommGroup K0] [Module R K0] [AddCommGroup K1]
    [Module R K1] (dK : K0 →ₗ[R] K1) (d : C0 →ₗ[R] C1) (ι0 : K0 →ₗ[R] C0) (ι1 : K1 →ₗ[R] C1)
    (comm : d ∘ₗ ι0 = ι1 ∘ₗ dK) (A : Type w) [CommRing A] [Algebra R A] :
    ((A ⊗[R] K1) ⧸ LinearMap.range (dK.baseChange A)) →ₗ[A]
      ((A ⊗[R] C1) ⧸ LinearMap.range (d.baseChange A)) :=
  Submodule.mapQ _ _ (ι1.baseChange A) fun y hy => by
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hy
    rw [Submodule.mem_comap, ← LinearMap.comp_apply, ← LinearMap.baseChange_comp, ← comm,
      LinearMap.baseChange_comp, LinearMap.comp_apply]
    exact LinearMap.mem_range_self _ _

/-- A model with two terms whose comparison with `d` is bijective on kernels and cokernels after
every base change. -/
structure GrothendieckComplex (d : C0 →ₗ[R] C1) where
  /-- The model two-term complex. -/
  G : CoherentBaseChange.TwoTermComplex.{u, v} R
  /-- The degree zero comparison from the model complex to `C0`. -/
  ι0 : G.C0 →ₗ[R] C0
  /-- The degree one comparison from the model complex to `C1`. -/
  ι1 : G.C1 →ₗ[R] C1
  /-- The comparison maps commute with the two differentials. -/
  comm : d ∘ₗ ι0 = ι1 ∘ₗ G.d
  /-- The kernel comparison is bijective after every base change. -/
  bijective_kerMap : ∀ (A : Type u) [CommRing A] [Algebra R A],
    Function.Bijective (kerMapBaseChange G.d d ι0 ι1 comm A)
  /-- The cokernel comparison is bijective after every base change. -/
  bijective_cokerMap : ∀ (A : Type u) [CommRing A] [Algebra R A],
    Function.Bijective (cokerMapBaseChange G.d d ι0 ι1 comm A)

end Dock

/-- The two chart cover with every ring equal to `R` and both restriction maps equal to the
identity. -/
def Cover.trivial (R : Type u) [CommRing R] : Cover.{u, u} R where
  A0 := R
  A1 := R
  A01 := R
  ρ0 := AlgHom.id R R
  ρ1 := AlgHom.id R R

/-- The section datum of `N0` and `N1` restricting into `N01` by inclusion. -/
@[reducible] def Sections.ofSubmodules {R : Type u} [CommRing R] {F : Type v}
    [AddCommGroup F] [Module R F]
    (N0 N1 N01 : Submodule R F) (h0 : N0 ≤ N01) (h1 : N1 ≤ N01) :
    Sections.{u, u, v} (Cover.trivial R) :=
  letI : Module (Cover.trivial R).A0 N0 := inferInstanceAs (Module R N0)
  letI : Module (Cover.trivial R).A1 N1 := inferInstanceAs (Module R N1)
  letI : Module (Cover.trivial R).A01 N01 := inferInstanceAs (Module R N01)
  haveI : IsScalarTower R (Cover.trivial R).A0 N0 := ⟨fun a b m => mul_smul (a : R) (b : R) m⟩
  haveI : IsScalarTower R (Cover.trivial R).A1 N1 := ⟨fun a b m => mul_smul (a : R) (b : R) m⟩
  haveI : IsScalarTower R (Cover.trivial R).A01 N01 := ⟨fun a b m => mul_smul (a : R) (b : R) m⟩
  { M0 := N0
    M1 := N1
    M01 := N01
    r0 := Submodule.inclusion h0
    r1 := Submodule.inclusion h1
    r0_smul := fun _ _ => rfl
    r1_smul := fun _ _ => rfl }

theorem Sections.mem_H0_ofSubmodules_iff {R : Type u} [CommRing R] {F : Type v} [AddCommGroup F]
    [Module R F] (N0 N1 N01 : Submodule R F) (h0 : N0 ≤ N01) (h1 : N1 ≤ N01) (p : N0 × N1) :
    p ∈ (Sections.ofSubmodules N0 N1 N01 h0 h1).H0 ↔ (p.1 : F) = p.2 :=
  ((Sections.ofSubmodules N0 N1 N01 h0 h1).mem_H0_iff p).trans
    ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

section Gates

example (R : Type u) [CommRing R] (a b : R) :
    (a, b) ∈ (Cover.trivial R).structureSheaf.H0 ↔ a = b :=
  (Cover.trivial R).mem_H0_structureSheaf_iff (a, b)

example : ((1 : (Cover.trivial ℤ).A0), (1 : (Cover.trivial ℤ).A1)) ∉
    ((Cover.trivial ℤ).lineBundle (-1)).H0 := by
  rw [Cover.mem_H0_lineBundle_iff]
  change ¬ ((1 : ℤ) = (-1 : ℤ) * 1)
  decide

example : ((1 : (Cover.trivial ℤ).A0), (-1 : (Cover.trivial ℤ).A1)) ∈
    ((Cover.trivial ℤ).lineBundle (-1)).H0 := by
  rw [Cover.mem_H0_lineBundle_iff]
  change ((1 : ℤ) = (-1 : ℤ) * -1)
  decide

example (R : Type u) [CommRing R] : GrothendieckComplex (0 : R →ₗ[R] R) where
  G := { C0 := R, C1 := R, d := 0 }
  ι0 := LinearMap.id
  ι1 := LinearMap.id
  comm := by simp
  bijective_kerMap A _ _ := by
    have h : ∀ x,
        (kerMapBaseChange (0 : R →ₗ[R] R) 0 LinearMap.id LinearMap.id (by simp) A x) = x :=
      fun x => Subtype.ext (by simp [kerMapBaseChange, LinearMap.restrict_apply])
    exact ⟨fun x y hxy => by rwa [h, h] at hxy, fun y => ⟨y, h y⟩⟩
  bijective_cokerMap A _ _ := by
    have h : ∀ z,
        cokerMapBaseChange (0 : R →ₗ[R] R) 0 LinearMap.id LinearMap.id (by simp) A z = z := by
      intro z
      induction z using Submodule.Quotient.induction_on with
      | _ z =>
        change Submodule.Quotient.mk ((LinearMap.id.baseChange A) z) =
          Submodule.Quotient.mk z
        rw [LinearMap.baseChange_id, LinearMap.id_apply]
    exact ⟨fun x y hxy => by rwa [h, h] at hxy, fun y => ⟨y, h y⟩⟩

end Gates

end TwoChartCech

end
