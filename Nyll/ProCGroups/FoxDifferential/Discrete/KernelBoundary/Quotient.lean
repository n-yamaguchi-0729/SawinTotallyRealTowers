/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.FoxDifferential.Discrete.KernelBoundary.Basic

/-!
# Fox differential: discrete — kernel boundary — quotient

The principal declarations in this module are:

- `HeadQuotientOfSurjective`
  The quotient of \(A_{\psi}\) by the image of the head map.
- `toIdentityDifferentialModule`
  The canonical map from \(A_{\psi}\) to the derived module of the identity map on \(H\).
- `toIdentityDifferentialModule_d`
  The canonical map to the identity differential module sends the universal differential of \(g\) to
  the universal differential of its image.
- `toAugmentationIdeal_id_comp_toIdentityDifferentialModule`
  For the identity map, composing the identity differential module with the augmentation-ideal map
  gives the expected augmentation boundary.
-/

namespace FoxDifferential

noncomputable section

open FoxDifferential

variable {H G : Type*} [Group H] [Group G]

/-- The quotient of \(A_{\psi}\) by the image of the head map. -/
abbrev HeadQuotientOfSurjective (ψ : G →* H) (hψ : Function.Surjective ψ) : Type _ :=
  DifferentialModule ψ ⧸ kernelAbelianizationBoundaryRangeOfSurjective ψ hψ

/-- The canonical map from \(A_{\psi}\) to the derived module of the identity map on \(H\). -/
def toIdentityDifferentialModule (ψ : G →* H) :
    DifferentialModule ψ →ₗ[GroupRing H] DifferentialModule (MonoidHom.id H) :=
  differentialModuleLift ψ
    { toFun := fun g => universalDifferential (MonoidHom.id H) (ψ g)
      map_mul' := by
        intro g₁ g₂
        simpa [map_mul] using
          universalDifferential_mul (MonoidHom.id H) (ψ g₁) (ψ g₂) }

/--
The canonical map to the identity differential module sends the universal differential of \(g\)
to the universal differential of its image.
-/
@[simp]
theorem toIdentityDifferentialModule_d (ψ : G →* H) (g : G) :
    toIdentityDifferentialModule ψ (universalDifferential ψ g) = universalDifferential
        (MonoidHom.id H) (ψ g) := by
  rw [toIdentityDifferentialModule, differentialModuleLift_d]
  rfl

/--
For the identity map, composing the identity differential module with the augmentation-ideal map
gives the expected augmentation boundary.
-/
theorem toAugmentationIdeal_id_comp_toIdentityDifferentialModule
    (ψ : G →* H) :
    (toAugmentationIdeal (H := H) (MonoidHom.id H)).comp (toIdentityDifferentialModule ψ) =
      toAugmentationIdeal (H := H) ψ := by
  apply hom_ext ψ
  intro g
  change toAugmentationIdeal (H := H) (MonoidHom.id H)
      (toIdentityDifferentialModule ψ (universalDifferential ψ g)) =
    toAugmentationIdeal (H := H) ψ (universalDifferential ψ g)
  rw [toIdentityDifferentialModule_d, toAugmentationIdeal_d,
    toAugmentationIdeal_d]
  rfl

/--
Composing the surjective-case kernel-boundary map with the identity differential-module map
gives the corresponding identity-module boundary value.
-/
@[simp]
theorem toIdentityDifferentialModule_kernelAbelianizationBoundaryLinearOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) (x : KernelAbelianizationAdd ψ) :
    toIdentityDifferentialModule ψ
      (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ x) = 0 := by
  let := kernelAbelianizationModuleOfSurjective ψ hψ
  rw [kernelAbelianizationBoundaryLinearOfSurjective_apply]
  change
    (fun y : Abelianization ψ.ker =>
      toIdentityDifferentialModule ψ (kernelAbelianizationBoundaryAdd ψ (Additive.ofMul y)) = 0)
      (Additive.toMul x)
  refine QuotientGroup.induction_on (Additive.toMul x) ?_
  intro n
  change toIdentityDifferentialModule ψ
      (kernelAbelianizationBoundaryAdd ψ (Additive.ofMul (Abelianization.of n))) = 0
  have hinner :
      toIdentityDifferentialModule ψ
          (kernelAbelianizationBoundaryAdd ψ (Additive.ofMul (Abelianization.of n))) =
        toIdentityDifferentialModule ψ (universalDifferential ψ n.1) := by
    exact congrArg (toIdentityDifferentialModule ψ) (kernelAbelianizationBoundaryAdd_of ψ n)
  rw [hinner, toIdentityDifferentialModule_d, n.2, universalDifferential_one]

/--
The surjective-case kernel-boundary range lies in the kernel of the map to the identity
differential module.
-/
theorem kernelAbelianizationBoundaryRangeOfSurjective_le_ker_toIdentityDiffModule
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    kernelAbelianizationBoundaryRangeOfSurjective ψ hψ ≤
      LinearMap.ker (toIdentityDifferentialModule ψ) := by
  intro y hy
  rcases hy with ⟨x, rfl⟩
  simpa [LinearMap.mem_ker] using
    toIdentityDifferentialModule_kernelAbelianizationBoundaryLinearOfSurjective ψ hψ x

/-- The quotient map \(A_{\psi} / \operatorname{im}(\mathrm{head}) \to A_{\mathrm{id}}\). -/
def headQuotientToIdentityDifferentialModule
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    HeadQuotientOfSurjective ψ hψ →ₗ[GroupRing H] DifferentialModule (MonoidHom.id H) :=
  (kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).liftQ
    (toIdentityDifferentialModule ψ)
    (kernelAbelianizationBoundaryRangeOfSurjective_le_ker_toIdentityDiffModule ψ hψ)

/--
The map from the head quotient to the identity differential module has the stated value on
quotient classes.
-/
@[simp]
theorem headQuotientToIdentityDifferentialModule_mkQ
    (ψ : G →* H) (hψ : Function.Surjective ψ) (x : DifferentialModule ψ) :
    headQuotientToIdentityDifferentialModule ψ hψ
      ((kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ x) =
        toIdentityDifferentialModule ψ x := by
  rfl

/-- A section of \(\psi\) is viewed as a differential map into the head quotient. -/
def headQuotientSectionOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) (h : H) :
    HeadQuotientOfSurjective ψ hψ :=
  (kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ
    (universalDifferential ψ (Function.surjInv hψ h))

private theorem headQuotientSectionOfSurjective_map_mul
    (ψ : G →* H) (hψ : Function.Surjective ψ) (h₁ h₂ : H) :
    headQuotientSectionOfSurjective ψ hψ (h₁ * h₂) =
      headQuotientSectionOfSurjective ψ hψ h₁ +
        groupRingScalar (MonoidHom.id H) h₁ •
          headQuotientSectionOfSurjective ψ hψ h₂ := by
  let s : H → G := Function.surjInv hψ
  let q : Submodule (GroupRing H) (DifferentialModule ψ) :=
    kernelAbelianizationBoundaryRangeOfSurjective ψ hψ
  have hs12 : ψ (s (h₁ * h₂)) = h₁ * h₂ := by
    simpa [s] using Function.surjInv_eq hψ (h₁ * h₂)
  let n : ψ.ker := ⟨s (h₁ * h₂) * (s h₁ * s h₂)⁻¹, by
    calc
      ψ (s (h₁ * h₂) * (s h₁ * s h₂)⁻¹)
          = ψ (s (h₁ * h₂)) * (ψ (s h₁ * s h₂))⁻¹ := by simp only [mul_inv_rev, map_mul, map_inv]
      _ = (h₁ * h₂) * (h₂⁻¹ * h₁⁻¹) := by
            rw [hs12]
            simp only [map_mul, Function.surjInv_eq hψ h₁, Function.surjInv_eq hψ h₂,
                mul_inv_rev, s]
      _ = 1 := by simp only [mul_assoc, mul_inv_cancel_left, mul_inv_cancel]⟩
  have hn_zero : q.mkQ (universalDifferential ψ n.1) = 0 := by
    have hn_mem : universalDifferential ψ n.1 ∈ q := by
      let := kernelAbelianizationModuleOfSurjective ψ hψ
      rw [← kernelAbelianizationBoundaryLinearOfSurjective_of (ψ := ψ) (hψ := hψ) n]
      exact LinearMap.mem_range_self _ _
    exact (Submodule.Quotient.mk_eq_zero (p := q) (x := universalDifferential ψ n.1)).2 hn_mem
  have hs :
      universalDifferential ψ (s (h₁ * h₂)) = universalDifferential ψ n.1 +
          universalDifferential ψ (s h₁ * s h₂) := by
    have hmul := universalDifferential_mul ψ n.1 (s h₁ * s h₂)
    have hψn : (MonoidAlgebra.of ℤ H (ψ n.1) : GroupRing H) = 1 := by
      rw [n.2, groupRing_of_one (H := H)]
    rw [hψn, one_smul] at hmul
    simpa [n, s, mul_assoc] using hmul
  have hq :
      q.mkQ (universalDifferential ψ (s (h₁ * h₂))) = q.mkQ (universalDifferential ψ (s h₁ * s
          h₂)) := by
    have hq' := congrArg q.mkQ hs
    simpa [map_add, hn_zero] using hq'
  calc
    headQuotientSectionOfSurjective ψ hψ (h₁ * h₂)
        = q.mkQ (universalDifferential ψ (s (h₁ * h₂))) := rfl
    _ = q.mkQ (universalDifferential ψ (s h₁ * s h₂)) := hq
    _ = q.mkQ (universalDifferential ψ (s h₁) + (MonoidAlgebra.of ℤ H (ψ (s h₁))) •
        universalDifferential ψ (s h₂)) := by
          rw [universalDifferential_mul]
    _ = headQuotientSectionOfSurjective ψ hψ h₁ +
          (MonoidAlgebra.of ℤ H h₁ : GroupRing H) •
            headQuotientSectionOfSurjective ψ hψ h₂ := by
          simp only [Function.surjInv_eq hψ h₁,
  MonoidAlgebra.of_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_add,
      Submodule.Quotient.mk_smul,
  headQuotientSectionOfSurjective, q, s]

/-- The head-quotient section in the surjective case is a crossed differential. -/
def headQuotientSectionHomOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    DifferentialHom (MonoidHom.id H) (HeadQuotientOfSurjective ψ hψ) where
  toFun := headQuotientSectionOfSurjective ψ hψ
  map_mul' := by
    intro h₁ h₂
    simpa only [scalarCrossedAction_apply] using
      headQuotientSectionOfSurjective_map_mul ψ hψ h₁ h₂

/--
The inverse-direction map \(A_{\mathrm{id}} \to A_{\psi} / \operatorname{im}(\mathrm{head})\) is
induced by a surjective section of \(\psi\).
-/
def fromIdentityDifferentialModuleOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    DifferentialModule (MonoidHom.id H) →ₗ[GroupRing H] HeadQuotientOfSurjective ψ hψ :=
  differentialModuleLift (MonoidHom.id H) (headQuotientSectionHomOfSurjective ψ hψ)

/--
The surjective-case map from the identity differential module has the stated value on the
differential generator.
-/
@[simp]
theorem fromIdentityDifferentialModuleOfSurjective_d
    (ψ : G →* H) (hψ : Function.Surjective ψ) (h : H) :
    fromIdentityDifferentialModuleOfSurjective ψ hψ (universalDifferential (MonoidHom.id H) h) =
      headQuotientSectionOfSurjective ψ hψ h := by
  change
    differentialModuleLift (MonoidHom.id H)
        (headQuotientSectionHomOfSurjective ψ hψ)
        (universalDifferential (MonoidHom.id H) h) =
      headQuotientSectionOfSurjective ψ hψ h
  exact
    differentialModuleLift_d (A := HeadQuotientOfSurjective ψ hψ) (MonoidHom.id H)
      (headQuotientSectionHomOfSurjective ψ hψ) h

/--
The maps between the head quotient and the identity differential module are inverse on the
displayed side.
-/
theorem headQuotientToIdentityDiffModule_fromIdentityDiffModuleOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    (headQuotientToIdentityDifferentialModule ψ hψ).comp
      (fromIdentityDifferentialModuleOfSurjective ψ hψ) =
        LinearMap.id := by
  apply hom_ext (ψ := MonoidHom.id H)
  intro h
  rw [LinearMap.comp_apply, fromIdentityDifferentialModuleOfSurjective_d,
    headQuotientSectionOfSurjective, headQuotientToIdentityDifferentialModule_mkQ,
    toIdentityDifferentialModule_d]
  simp only [Function.surjInv_eq hψ h, LinearMap.id_coe, id_eq]

/--
The map from the identity differential module is a left inverse to the identity-differential
quotient map in the surjective case.
-/
theorem fromIdentityDifferentialModuleOfSurjective_comp_toIdentityDifferentialModule
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    (fromIdentityDifferentialModuleOfSurjective ψ hψ).comp
      (toIdentityDifferentialModule ψ) =
        (kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ := by
  apply hom_ext (ψ := ψ)
  intro g
  let s : H → G := Function.surjInv hψ
  let q : Submodule (GroupRing H) (DifferentialModule ψ) :=
    kernelAbelianizationBoundaryRangeOfSurjective ψ hψ
  let n : ψ.ker := ⟨g * (s (ψ g))⁻¹, by
    simp only [MonoidHom.mem_ker, map_mul, map_inv, Function.surjInv_eq hψ (ψ g),
        mul_inv_cancel, s]⟩
  have hn_zero : q.mkQ (universalDifferential ψ n.1) = 0 := by
    have hn_mem : universalDifferential ψ n.1 ∈ q := by
      let := kernelAbelianizationModuleOfSurjective ψ hψ
      rw [← kernelAbelianizationBoundaryLinearOfSurjective_of (ψ := ψ) (hψ := hψ) n]
      exact LinearMap.mem_range_self _ _
    exact (Submodule.Quotient.mk_eq_zero (p := q) (x := universalDifferential ψ n.1)).2 hn_mem
  have hgdecomp : universalDifferential ψ g = universalDifferential ψ n.1 +
      universalDifferential ψ (s (ψ g)) := by
    have hmul := universalDifferential_mul ψ n.1 (s (ψ g))
    have hψn : (MonoidAlgebra.of ℤ H (ψ n.1) : GroupRing H) = 1 := by
      rw [n.2, groupRing_of_one (H := H)]
    rw [hψn, one_smul] at hmul
    simpa [n, s, mul_assoc] using hmul
  have hq : q.mkQ (universalDifferential ψ g) = q.mkQ (universalDifferential ψ (s (ψ g))) := by
    have hq' := congrArg q.mkQ hgdecomp
    simpa [map_add, hn_zero] using hq'
  calc
    fromIdentityDifferentialModuleOfSurjective ψ hψ
        (toIdentityDifferentialModule ψ (universalDifferential ψ g))
        = q.mkQ (universalDifferential ψ (s (ψ g))) := by
            rw [toIdentityDifferentialModule_d, fromIdentityDifferentialModuleOfSurjective_d,
              headQuotientSectionOfSurjective]
    _ = q.mkQ (universalDifferential ψ g) := hq.symm

/--
The quotient \(A_{\psi} / im(head)\) is canonically identified with the derived module of
\(id_H\).
-/
def headQuotientEquivIdentityDifferentialModuleOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    HeadQuotientOfSurjective ψ hψ ≃ₗ[GroupRing H] DifferentialModule (MonoidHom.id H) where
  toLinearMap := headQuotientToIdentityDifferentialModule ψ hψ
  invFun := fromIdentityDifferentialModuleOfSurjective ψ hψ
  left_inv := by
    intro x
    have hcomp :
        (fromIdentityDifferentialModuleOfSurjective ψ hψ).comp
            (headQuotientToIdentityDifferentialModule ψ hψ) =
          LinearMap.id := by
      apply Submodule.linearMap_qext _
      apply LinearMap.ext
      intro y
      change fromIdentityDifferentialModuleOfSurjective ψ hψ
          (headQuotientToIdentityDifferentialModule ψ hψ
            ((kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ y)) =
        (kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ y
      rw [headQuotientToIdentityDifferentialModule_mkQ]
      exact LinearMap.congr_fun
        (fromIdentityDifferentialModuleOfSurjective_comp_toIdentityDifferentialModule ψ hψ) y
    exact LinearMap.congr_fun hcomp x
  right_inv := by
    intro x
    exact LinearMap.congr_fun
      (headQuotientToIdentityDiffModule_fromIdentityDiffModuleOfSurjective ψ hψ) x

/-- For a surjective \(\psi\), the Crowell head quotient is the augmentation ideal. -/
def headQuotientEquivAugmentationIdealOfSurjective
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    HeadQuotientOfSurjective ψ hψ ≃ₗ[GroupRing H] augmentationIdeal H :=
  by
    classical
    exact
      (headQuotientEquivIdentityDifferentialModuleOfSurjective ψ hψ).trans
        (FoxDifferential.identityDifferentialModuleEquivAugmentationIdeal (H := H))

/--
The head quotient is equivalent to the augmentation ideal and sends quotient classes to their
augmentation representatives.
-/
@[simp]
theorem headQuotientEquivAugmentationIdealOfSurjective_mkQ
    (ψ : G →* H) (hψ : Function.Surjective ψ) (x : DifferentialModule ψ) :
    headQuotientEquivAugmentationIdealOfSurjective ψ hψ
      ((kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ x) =
        toAugmentationIdeal (H := H) ψ x := by
  unfold headQuotientEquivAugmentationIdealOfSurjective
  rw [LinearEquiv.trans_apply]
  change (FoxDifferential.identityDifferentialModuleEquivAugmentationIdeal (H := H))
      (headQuotientToIdentityDifferentialModule ψ hψ
        ((kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ x)) = _
  rw [headQuotientToIdentityDifferentialModule_mkQ]
  have hid := congrArg
      (fun f : DifferentialModule (MonoidHom.id H) →ₗ[GroupRing H] augmentationIdeal H =>
        f (toIdentityDifferentialModule ψ x))
      (FoxDifferential.identityDifferentialModuleEquivAugmentationIdeal_toLinearMap (H := H))
  exact hid.trans <|
    LinearMap.congr_fun (toAugmentationIdeal_id_comp_toIdentityDifferentialModule (H := H) ψ) x

/--
The range of the surjective-case kernel-abelianization boundary is the kernel of the map to the
augmentation ideal.
-/
theorem kernelAbelianizationBoundaryRangeOfSurjective_eq_ker_toAugmentationIdeal
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    kernelAbelianizationBoundaryRangeOfSurjective ψ hψ =
      LinearMap.ker (toAugmentationIdeal (H := H) ψ) := by
  apply le_antisymm
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    change toAugmentationIdeal (H := H) ψ
        (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ x) = 0
    apply Subtype.ext
    exact toGroupRing_kernelAbelianizationBoundaryLinearOfSurjective (H := H) ψ hψ x
  · intro y hy
    have hy0 : toAugmentationIdeal (H := H) ψ y = 0 := by
      simpa [LinearMap.mem_ker] using hy
    have hq0 :
        headQuotientEquivAugmentationIdealOfSurjective ψ hψ
          ((kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ y) = 0 := by
      rw [headQuotientEquivAugmentationIdealOfSurjective_mkQ]
      exact hy0
    have hq : ((kernelAbelianizationBoundaryRangeOfSurjective ψ hψ).mkQ y :
        HeadQuotientOfSurjective ψ hψ) = 0 := by
      exact (headQuotientEquivAugmentationIdealOfSurjective ψ hψ).injective
        (by simpa using hq0)
    exact (Submodule.Quotient.mk_eq_zero (p := kernelAbelianizationBoundaryRangeOfSurjective ψ hψ)
      (x := y)).1 hq

/-- Exactness at \(A_{\psi}\), formulated against the augmentation ideal. -/
theorem exact_kernelAbelianizationBoundaryLinearOfSurjective_toAugmentationIdeal
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    Function.Exact
      (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ)
      (toAugmentationIdeal (H := H) ψ) := by
  intro y
  constructor
  · intro hy
    have hyker : y ∈ LinearMap.ker (toAugmentationIdeal (H := H) ψ) := by
      simpa [LinearMap.mem_ker] using hy
    rw [← kernelAbelianizationBoundaryRangeOfSurjective_eq_ker_toAugmentationIdeal
      (H := H) (ψ := ψ) hψ] at hyker
    exact hyker
  · rintro ⟨x, rfl⟩
    apply Subtype.ext
    exact toGroupRing_kernelAbelianizationBoundaryLinearOfSurjective (H := H) ψ hψ x

/-- Exactness at \(A_{\psi}\), against the usual map \(A_{\psi}\ \to \mathbb{Z}[H]\). -/
theorem exact_kernelAbelianizationBoundaryLinearOfSurjective_toGroupRing
    (ψ : G →* H) (hψ : Function.Surjective ψ) :
    Function.Exact
      (kernelAbelianizationBoundaryLinearOfSurjective ψ hψ)
      (toGroupRing ψ) := by
  intro y
  constructor
  · intro hy
    have hy' : toAugmentationIdeal (H := H) ψ y = 0 := by
      apply Subtype.ext
      exact hy
    exact (exact_kernelAbelianizationBoundaryLinearOfSurjective_toAugmentationIdeal
      (H := H) ψ hψ y).1 hy'
  · rintro ⟨x, rfl⟩
    exact toGroupRing_kernelAbelianizationBoundaryLinearOfSurjective (H := H) ψ hψ x
end

end FoxDifferential
