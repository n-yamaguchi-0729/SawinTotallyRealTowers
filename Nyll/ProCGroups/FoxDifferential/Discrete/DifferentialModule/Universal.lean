/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.DifferentialModule.Basic

/-!
# Fox differential: discrete — differential module — universal

The principal declarations in this module are:

- `DifferentialHom`
  A \(\psi\)-differential map is a map satisfying the Fox Leibniz rule.
- `liftLinear`
  The linear map out of the free pre-module determined by \(\delta\).
- `liftLinear_single`
  The linear extension of a map evaluates on a single basis vector by scalar multiplication.
- `differentialHomLiftLinear_relationElement`
  A crossed differential kills each defining relation of the universal differential module.
-/

namespace FoxDifferential

noncomputable section

variable {H G : Type*} [Group H] [Group G]

section UniversalProperty

variable {A : Type*} [AddCommGroup A] [Module (GroupRing H) A]

/-- A \(\psi\)-differential map is a map satisfying the Fox Leibniz rule. -/
abbrev DifferentialHom (ψ : G →* H) (A : Type*) [AddCommGroup A] [Module (GroupRing H) A] :=
  ScalarCrossedHom (groupRingScalar ψ) A

/-- The linear map out of the free pre-module determined by \(\delta\). -/
def liftLinear (δ : G → A) : DifferentialPreModule H G →ₗ[GroupRing H] A :=
  Finsupp.linearCombination (GroupRing H) δ

omit [Group G] in
/-- The linear extension of a map evaluates on a single basis vector by scalar multiplication. -/
@[simp]
theorem liftLinear_single (δ : G → A) (g : G) (r : GroupRing H) :
    liftLinear δ (Finsupp.single g r) = r • δ g := by
  simp only [liftLinear, Finsupp.linearCombination_single]

/-- A crossed differential kills each defining relation of the universal differential module. -/
theorem differentialHomLiftLinear_relationElement
    (ψ : G →* H) (δ : DifferentialHom ψ A) (g₁ g₂ : G) :
    liftLinear δ (relationElement ψ g₁ g₂) = 0 := by
  simp only [liftLinear, relationElement, MonoidAlgebra.of_apply, Finsupp.smul_single,
    smul_eq_mul, mul_one, map_sub, Finsupp.linearCombination_single,
    ScalarCrossedHom.map_mul, groupRingScalar_apply, smul_add, one_smul, map_add,
    sub_self]

/--
The relation submodule is contained in the kernel of the linear extension of a crossed
differential.
-/
theorem differentialHomRelationSubmodule_le_ker
    (ψ : G →* H) (δ : DifferentialHom ψ A) :
    relationSubmodule ψ ≤ LinearMap.ker (liftLinear δ) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨g₁, g₂⟩, rfl⟩
  simpa [LinearMap.mem_ker] using
    differentialHomLiftLinear_relationElement (A := A) ψ δ g₁ g₂

/--
A crossed differential factors uniquely through the universal differential module as a linear
map.
-/
def differentialModuleLift (ψ : G →* H) (δ : DifferentialHom ψ A) :
    DifferentialModule ψ →ₗ[GroupRing H] A :=
  (relationSubmodule ψ).liftQ (liftLinear δ)
    (differentialHomRelationSubmodule_le_ker (A := A) ψ δ)

/-- The universal lift evaluates on universalDifferential g as the original crossed differential. -/
@[simp]
theorem differentialModuleLift_d (ψ : G →* H) (δ : DifferentialHom ψ A) (g : G) :
    differentialModuleLift ψ δ (universalDifferential ψ g) = δ g := by
  change
      (relationSubmodule ψ).liftQ (liftLinear δ)
          (differentialHomRelationSubmodule_le_ker (A := A) ψ δ)
          ((relationSubmodule ψ).mkQ (Finsupp.single g 1)) = δ g
  rw [Submodule.mkQ_apply, Submodule.liftQ_apply]
  simp only [liftLinear_single, one_smul]

/--
Linear maps out of the universal differential module are equal when they agree on all universal
differentials.
-/
@[ext]
theorem hom_ext (ψ : G →* H) {f g : DifferentialModule ψ →ₗ[GroupRing H] A}
    (hfg : ∀ g', f (universalDifferential ψ g') = g (universalDifferential ψ g')) : f = g := by
  apply Submodule.linearMap_qext _
  apply Finsupp.lhom_ext
  intro g' r
  have hsingle : ((relationSubmodule ψ).mkQ (Finsupp.single g' r) : DifferentialModule ψ) =
      r • universalDifferential ψ g' := by
    rw [← Finsupp.smul_single_one]
    rfl
  change f ((relationSubmodule ψ).mkQ (Finsupp.single g' r)) =
    g ((relationSubmodule ψ).mkQ (Finsupp.single g' r))
  rw [hsingle]
  simpa [map_smul] using congrArg (fun z => r • z) (hfg g')

/--
The universal lift is the unique linear map with prescribed values on universal differentials.
-/
theorem differentialModuleLift_unique
    (ψ : G →* H) (δ : DifferentialHom ψ A)
    (f : DifferentialModule ψ →ₗ[GroupRing H] A)
    (hf : ∀ g, f (universalDifferential ψ g) = δ g) :
    f = differentialModuleLift (A := A) ψ δ := by
  apply hom_ext ψ
  intro g
  rw [hf g, differentialModuleLift_d]

/-- Existence and uniqueness of the linear map representing a discrete Fox crossed differential. -/
theorem existsUnique_differentialModuleLift
    (ψ : G →* H) (δ : DifferentialHom ψ A) :
    ∃! f : DifferentialModule ψ →ₗ[GroupRing H] A,
      ∀ g, f (universalDifferential ψ g) = δ g := by
  refine ⟨differentialModuleLift (A := A) ψ δ, ?_, ?_⟩
  · intro g
    exact differentialModuleLift_d (A := A) ψ δ g
  · intro f hf
    exact differentialModuleLift_unique (A := A) ψ δ f hf

/-- The crossed differential induced by a linear map out of the universal differential module. -/
def differentialHomOfLinearMap
    (ψ : G →* H) (f : DifferentialModule ψ →ₗ[GroupRing H] A) : DifferentialHom ψ A where
  toFun g := f (universalDifferential ψ g)
  map_mul' := by
    intro g₁ g₂
    change f (universalDifferential ψ (g₁ * g₂)) =
      f (universalDifferential ψ g₁) +
        (MonoidAlgebra.of ℤ H (ψ g₁) : GroupRing H) •
          f (universalDifferential ψ g₂)
    rw [universalDifferential_mul, map_add, map_smul]

/-- The differential induced by a linear map evaluates that map on the universal
differential. -/
@[simp]
theorem differentialHomOfLinearMap_apply
    (ψ : G →* H) (f : DifferentialModule ψ →ₗ[GroupRing H] A) (g : G) :
    differentialHomOfLinearMap (A := A) ψ f g = f (universalDifferential ψ g) :=
  rfl

/--
Discrete Fox crossed differentials \(G \to A\) with respect to \(\psi: G \to H\) are represented
by \(\mathbb{Z}[H]\)-linear maps out of the universal differential module \(A_{\psi}\).
-/
def differentialHomEquivLinearMap (ψ : G →* H) :
    DifferentialHom ψ A ≃ (DifferentialModule ψ →ₗ[GroupRing H] A) where
  toFun δ := differentialModuleLift (A := A) ψ δ
  invFun f := differentialHomOfLinearMap (A := A) ψ f
  left_inv δ := by
    apply CrossedHom.ext
    intro g
    exact differentialModuleLift_d (A := A) ψ δ g
  right_inv f := by
    apply hom_ext ψ
    intro g
    exact differentialModuleLift_d (A := A) ψ
      (differentialHomOfLinearMap (A := A) ψ f) g

/--
The compatibility between the discrete representation theorem and the generic
crossed-differential-module representation theorem.
-/
theorem differentialHomEquivLinearMap_eq_generic
    (ψ : G →* H) (δ : DifferentialHom ψ A) :
    differentialHomEquivLinearMap (A := A) ψ δ =
      (crossedHomModuleEquivLinearMap
        (A := A) (groupRingScalar ψ) δ).comp
        (differentialModuleEquivCrossedDifferentialModule ψ).toLinearMap := by
  apply hom_ext ψ
  intro g
  change
    differentialModuleLift (A := A) ψ δ (universalDifferential ψ g) =
      crossedHomModuleLift (A := A) (groupRingScalar ψ) δ
        (universalCrossedDifferential (groupRingScalar ψ) g)
  rw [differentialModuleLift_d, crossedHomModuleLift_universal]

end UniversalProperty

end

end FoxDifferential
