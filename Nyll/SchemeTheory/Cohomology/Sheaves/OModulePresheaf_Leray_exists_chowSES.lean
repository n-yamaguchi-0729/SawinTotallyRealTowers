/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_exists_chowSES.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafLerayBicomplex
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_Leray_exists_hom_relHPresheaf_zero
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_isCoherent_coker
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_isQuasicoherent_coker
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_Leray_isCoherent_relHPresheaf_chow
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow
import Mathlib.RingTheory.Noetherian.Basic

/-!
A short exact sequence from the Chow devissage construction for a module presheaf.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_Leray_exists_chowSES
attribute [-instance] ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq

noncomputable section

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Opposite
open _root_.CategoryTheory.Limits

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

section General

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}

namespace Hom
open _root_.AlgebraicGeometry.OModulePresheaf.Hom
end Hom
namespace Hom
open scoped _root_.AlgebraicGeometry.OModulePresheaf.Hom in
private def _root_.AlgebraicGeometry.OModulePresheaf.Hom.symmOfBijective {F G : OModulePresheaf π}
    (φ : Hom F G)
    (hφ : ∀ U : V.Opens, Function.Bijective (φ.app U)) : Hom G F where
  app U := ((LinearEquiv.ofBijective (φ.app U) (hφ U)).symm : G.obj U →ₗ[R] F.obj U)
  app_smul U a y := by
    apply (hφ U).1
    change φ.app U ((LinearEquiv.ofBijective (φ.app U) (hφ U)).symm (a • y))
      = φ.app U (a • (LinearEquiv.ofBijective (φ.app U) (hφ U)).symm y)
    rw [φ.app_smul]
    erw [(LinearEquiv.ofBijective (φ.app U) (hφ U)).apply_symm_apply,
      (LinearEquiv.ofBijective (φ.app U) (hφ U)).apply_symm_apply]
  naturality {U U'} h := by
    refine LinearMap.ext fun y => (hφ U).1 ?_
    change φ.app U ((LinearEquiv.ofBijective (φ.app U) (hφ U)).symm (G.res h y))
      = φ.app U (F.res h ((LinearEquiv.ofBijective (φ.app U') (hφ U')).symm y))
    rw [φ.naturality_apply]
    erw [(LinearEquiv.ofBijective (φ.app U) (hφ U)).apply_symm_apply,
      (LinearEquiv.ofBijective (φ.app U') (hφ U')).apply_symm_apply]

end Hom
open _root_.AlgebraicGeometry.OModulePresheaf
namespace Hom
open scoped _root_.AlgebraicGeometry.OModulePresheaf.Hom in
private theorem _root_.AlgebraicGeometry.OModulePresheaf.Hom.symmOfBijective_bijective {F G :
    OModulePresheaf π} (φ : Hom F G)
    (hφ : ∀ U : V.Opens, Function.Bijective (φ.app U)) (U : V.Opens) :
    Function.Bijective ((φ.symmOfBijective hφ).app U) :=
  (LinearEquiv.ofBijective (φ.app U) (hφ U)).symm.bijective

end Hom
open _root_.AlgebraicGeometry.OModulePresheaf
variable (π) in
theorem isQuasicoherent_unit : (unit π).IsQuasicoherent := by
  intro U f
  have := U.2.isLocalization_basicOpen f
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · have hcore : ∀ x' : Γ(V, V.basicOpen f), ∃ (n : ℕ) (y : Γ(V, U.1)),
        (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom y
          = (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n) * x' := fun x' => by
      obtain ⟨⟨y, _, n, rfl⟩, hxy⟩ :=
        IsLocalization.surj (S := Γ(V, V.basicOpen f)) (.powers f) x'
      exact ⟨n, y, hxy.symm.trans (mul_comm _ _)⟩
    exact hcore x
  · have hy' : algebraMap Γ(V, U.1) Γ(V, V.basicOpen f) y = 0 := hy
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (.powers f) _ _).mp hy'
    exact ⟨n, hn⟩

end General

namespace Leray
open _root_.AlgebraicGeometry.OModulePresheaf.Leray
open _root_.AlgebraicGeometry.OModulePresheaf.Leray

section UnitToPullOpen

variable {R : Type u} [CommRing R] {V' Z : Scheme.{u}}
variable (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))

/--
The pullback map from structure-sheaf sections on the base to sections on their preimages in the
source.
-/
def unitToPullOpen : Hom (unit πZ) (pullOpen p πZ (⊤ : V'.Opens)) where
  app U :=
    { toFun := fun s => (p.appLE U ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U) inf_le_right).hom s
      map_add' := fun s₁ s₂ => map_add _ s₁ s₂
      map_smul' := fun r s => by
        have hcore : ∀ s' : Γ(Z, U),
            (p.appLE U ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U) inf_le_right).hom
                ((Z.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom
                  ((πZ.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)) * s')
              = (V'.presheaf.map (homOfLE le_top).op).hom
                  (((p ≫ πZ).app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r))
                * (p.appLE U _ inf_le_right).hom s' := fun s' => by
          erw [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]; rfl
        exact hcore s }
  app_smul U a s := by
    have hcore : ∀ s' : Γ(Z, U),
        (p.appLE U ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U) inf_le_right).hom (a * s')
          = (p.appLE U _ inf_le_right).hom a * (p.appLE U _ inf_le_right).hom s' :=
      fun s' => map_mul _ a s'
    exact hcore s
  naturality {U U'} h := by
    refine LinearMap.ext fun s => ?_
    change (p.appLE U ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U) inf_le_right).hom
        ((Z.presheaf.map (homOfLE h).op).hom s)
      = (V'.presheaf.map
          (homOfLE (inf_le_inf_left _ ((Opens.map p.base).monotone h))).op).hom
          ((p.appLE U' ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U') inf_le_right).hom s)
    have hleft := Scheme.Hom.map_appLE p
      (U := U) (U' := U') (V := (⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U)
      inf_le_right (homOfLE h).op
    have hright := Scheme.Hom.appLE_map p
      (U := U') (V := (⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U')
      (V' := (⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U) inf_le_right
      (homOfLE (inf_le_inf_left _ ((Opens.map p.base).monotone h))).op
    exact (congrArg
      (fun f : Γ(Z, U') ⟶ Γ(V', (⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U) =>
        f.hom (show Γ(Z, U') from s)) hleft).trans
      (congrArg
        (fun f : Γ(Z, U') ⟶ Γ(V', (⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U) =>
          f.hom (show Γ(Z, U') from s)) hright).symm

theorem unitToPullOpen_app (U : Z.Opens) (s : Γ(Z, U)) :
    (unitToPullOpen p πZ).app U s
      = (p.appLE U ((⊤ : V'.Opens) ⊓ (Opens.map p.base).obj U) inf_le_right).hom s := rfl

end UnitToPullOpen

section Chow

attribute [local instance] MvPolynomial.gradedAlgebra

variable {R : Type u} [CommRing R] {Z : Scheme.{u}}
variable (πZ : Z ⟶ Spec (CommRingCat.of R)) [IsIntegral Z]
variable (D : ChowDatumProj πZ)

omit [AlgebraicGeometry.IsIntegral Z] in
theorem chow_restrict_isIso {W : Z.Opens} (hWU : W ≤ D.U) :
    IsIso (D.p ∣_ W) := by
  have heq : (isPullback_morphismRestrict D.p W).flip.isoPullback.hom ≫
      (Limits.pullback.congrHom rfl (Z.homOfLE_ι hWU).symm).hom ≫
      (Limits.pullbackLeftPullbackSndIso D.p D.U.ι (Z.homOfLE hWU)).inv ≫
      Limits.pullback.snd _ _ = D.p ∣_ W := by
    simp only [Limits.pullbackLeftPullbackSndIso_inv_snd_snd, Limits.pullback.congrHom_hom]
    erw [Limits.pullback.lift_snd]
    rw [Category.comp_id, (isPullback_morphismRestrict D.p W).flip.isoPullback_hom_snd]
  exact heq ▸ inferInstance

omit [IsIntegral Z] in
theorem chow_appLE_bijective_of_le_U {W : Z.Opens} (hWU : W ≤ D.U) :
    Function.Bijective
      (D.p.appLE W ((⊤ : D.V'.Opens) ⊓ (Opens.map D.p.base).obj W) inf_le_right).hom := by
  have := chow_restrict_isIso πZ D hWU
  have happiso : IsIso ((D.p ∣_ W).app ⊤) := inferInstance
  have : IsIso (D.p.appLE W ((⊤ : D.V'.Opens) ⊓ (Opens.map D.p.base).obj W) inf_le_right) := by
    refine (D.p.appLE_congr (image_morphismRestrict_preimage D.p W ⊤).le
        (Scheme.Opens.ι_image_top W)
        (show (D.p ⁻¹ᵁ W).ι ''ᵁ ((D.p ∣_ W) ⁻¹ᵁ ⊤)
            = (⊤ : D.V'.Opens) ⊓ (Opens.map D.p.base).obj W from by
          rw [Opens.map_top, Scheme.Opens.ι_image_top]; exact (top_inf_eq _).symm)
        (fun g => IsIso g)).mp ?_
    exact morphismRestrict_app' D.p W ⊤ ▸ happiso
  exact ConcreteCategory.bijective_of_isIso _

theorem unitToPullOpen_injective_chow (U : Z.Opens) :
    Function.Injective ((unitToPullOpen D.p πZ).app U) := by
  rw [injective_iff_map_eq_zero]
  intro s hs
  have h0 : (D.p.appLE U ((⊤ : D.V'.Opens) ⊓ (Opens.map D.p.base).obj U) inf_le_right).hom s
      = 0 := hs
  have h0W : (D.p.appLE (U ⊓ D.U)
      ((⊤ : D.V'.Opens) ⊓ (Opens.map D.p.base).obj (U ⊓ D.U)) inf_le_right).hom
      ((Z.presheaf.map (homOfLE inf_le_left).op).hom s) = 0 := by
    erw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE,
      ← Scheme.Hom.appLE_map _ inf_le_right (homOfLE (inf_le_inf_left _
        ((Opens.map D.p.base).monotone (inf_le_left : U ⊓ D.U ≤ U)))).op,
      CommRingCat.comp_apply, h0, map_zero]
  have hsW : (Z.presheaf.map (homOfLE (inf_le_left : U ⊓ D.U ≤ U)).op).hom s = 0 :=
    (chow_appLE_bijective_of_le_U πZ D (inf_le_right : U ⊓ D.U ≤ D.U)).1
      (h0W.trans (map_zero _).symm)
  rcases (U : Set Z).eq_empty_or_nonempty with hU | hU
  · obtain rfl : U = ⊥ := SetLike.ext' hU
    exact @Subsingleton.elim _ (inferInstance : Subsingleton Γ(Z, (⊥ : Z.Opens))) s 0
  · have : Nonempty (U ⊓ D.U : Z.Opens) :=
      (nonempty_preirreducible_inter U.isOpen D.U.isOpen hU D.hU_dense.nonempty).to_subtype
    exact map_injective_of_isIntegral Z (homOfLE inf_le_left) (hsW.trans (map_zero _).symm)

theorem exists_chowSES' [IsNoetherianRing R] [IsProper πZ] :
    ∃ (Q : OModulePresheaf πZ) (_S : OModulePresheaf.SES (OModulePresheaf.unit πZ)
          (relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) 0) Q),
      Q.IsCoherent ∧ Q.IsQuasicoherent ∧ Q.SupportedIn ⟨(D.U : Set Z)ᶜ, D.U.isOpen.isClosed_compl⟩
        := by
  set K' := ProjSpace.stdCoverPullback D.ιN
  obtain ⟨φ, hφ, -⟩ := exists_hom_relHPresheaf_zero D.p πZ K'
  let ψ : Hom (pullOpen D.p πZ (⊤ : D.V'.Opens)) (relHPresheaf D.p πZ K' 0) := φ.symmOfBijective hφ
  have hψ : ∀ U, Function.Bijective (ψ.app U) := φ.symmOfBijective_bijective hφ
  let χ : Hom (unit πZ) (relHPresheaf D.p πZ K' 0) := ψ.comp (unitToPullOpen D.p πZ)
  have hχinj : ∀ U, Function.Injective (χ.app U) := fun U =>
    (hψ U).1.comp (unitToPullOpen_injective_chow πZ D U)
  refine ⟨coker χ,
    { inc := χ
      proj := (imCokerSES χ).proj
      injective := hχinj
      surjective := (imCokerSES χ).surjective
      exact := fun U => (Submodule.ker_mkQ (LinearMap.range (χ.app U))).symm },
    isCoherent_coker χ (isCoherent_relHPresheaf_chow πZ D 0),
    isQuasicoherent_coker χ (isQuasicoherent_relHPresheaf_chow πZ D 0) (isQuasicoherent_unit πZ),
    fun W hW => ?_⟩
  have hWU : (W : Z.Opens) ≤ D.U := fun x hx =>
    not_not.mp fun hc => (Set.ext_iff.mp hW x).mp ⟨hx, hc⟩
  refine Submodule.Quotient.subsingleton_iff.mpr (LinearMap.range_eq_top.mpr ?_)
  exact (hψ W.1).2.comp (chow_appLE_bijective_of_le_U πZ D hWU).2

end Chow

end Leray

end AlgebraicGeometry.OModulePresheaf

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs in
open CategoryTheory _root_.AlgebraicGeometry
  OModulePresheaf_Leray_exists_chowSES.AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.OModulePresheaf.Leray.exists_chowSES {R : Type u} [CommRing R]
    [IsNoetherianRing R]
    {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsProper πZ] [IsIntegral Z] (D : ChowDatumProj πZ) :
    ∃ (Q : OModulePresheaf πZ) (_S : OModulePresheaf.SES (OModulePresheaf.unit πZ)
          (OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) 0) Q),
      Q.IsCoherent ∧ Q.IsQuasicoherent ∧ Q.SupportedIn ⟨(D.U : Set Z)ᶜ, D.U.isOpen.isClosed_compl⟩
        :=
  AlgebraicGeometry.OModulePresheaf.Leray.exists_chowSES' πZ D

end
end AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_Leray_exists_chowSES
end ProofImplementation

attribute [-instance] AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero
  DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II
  DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I
  ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup
  ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg
  ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid
  ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule
  ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero
  ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul
  ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] AlgebraicGeometry.OModulePresheaf.prod_obj
  AlgebraicGeometry.OModulePresheaf.restrOpen_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq
  AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj
  AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app
  AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj
  AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec
  AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U
  AlgebraicGeometry.OModulePresheaf.sndHom_app DoubleComplex.Bounded.mk.injEq
  DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq
  DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq
  ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq
  ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
