/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_isCoherent_relHPresheaf_chow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.AlgebraicGeometry.Noetherian
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafLerayDoubleComplex
import Nyll.SchemeTheory.Cohomology.Cech.OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Nyll.SchemeTheory.ProjectiveSpace.StandardChartsBaseChange
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafLerayBicomplex

/-!
Coherence of the relative cohomology presheaf in the Chow construction.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_Leray_isCoherent_relHPresheaf_chow
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
namespace Leray
open _root_.AlgebraicGeometry.OModulePresheaf.Leray
open _root_.AlgebraicGeometry.OModulePresheaf.Leray
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

section Local

variable {R : Type u} [CommRing R]

theorem res_res' {V : Scheme.{u}} {O₁ O₂ O₃ : V.Opens} (h12 : O₁ ≤ O₂) (h23 : O₂ ≤ O₃) (x : Γ(V,
    O₃)) :
    (V.presheaf.map (homOfLE h12).op).hom ((V.presheaf.map (homOfLE h23).op).hom x)
      = (V.presheaf.map (homOfLE (h12.trans h23)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl

theorem res_refl' {V : Scheme.{u}} {O : V.Opens} (h : O ≤ O) (x : Γ(V, O)) :
    (V.presheaf.map (homOfLE h).op).hom x = x := by
  have : (homOfLE h : O ⟶ O) = 𝟙 O := rfl
  rw [this, op_id, V.presheaf.map_id]; rfl

theorem algebraOfHom_compat {V : Scheme.{u}} (π : V ⟶ Spec (CommRingCat.of R)) (W : V.Opens) :
    ∀ c, letI := Scheme.TwoAffineOpenCover.algebraOfHom π W
      algebraMap R Γ(V, W) c = (V.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom
        (π.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) :=
  fun _ => rfl

theorem specMap_algebraMap_eq_fromSpec_comp {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f U
    Spec.map (CommRingCat.ofHom (algebraMap R Γ(X, U))) = hU.fromSpec ≫ f := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom f U
  have halg : CommRingCat.ofHom (algebraMap R Γ(X, U))
      = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appLE ⊤ U (le_top : U ≤ f ⁻¹ᵁ ⊤) := rfl
  rw [halg, Spec.map_comp, ← Scheme.isoSpec_Spec_inv, ← IsAffineOpen.fromSpec_top,
    IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top (Spec (CommRingCat.of R))) hU
      (le_top : U ≤ f ⁻¹ᵁ ⊤)]

theorem isNoeth_of_proper [IsNoetherianRing R] {V : Scheme.{u}}
    (π : V ⟶ Spec (CommRingCat.of R)) [IsProper π] : IsNoetherian V := by
  have : LocallyOfFiniteType π := inferInstance
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace π
  exact {}

end Local

section RelHPresheafChow

variable {R : Type u} [CommRing R] {Z : Scheme.{u}}
variable (πZ : Z ⟶ Spec (CommRingCat.of R)) (D : ChowDatumProj πZ)

theorem lift_isClosedImm [IsSeparated πZ] :
    IsClosedImmersion (Limits.pullback.lift D.ιN D.p D.hoverN) := by
  have hbase : MorphismProperty.IsStableUnderBaseChange
      (fun {X Y : Scheme.{u}} (f : X ⟶ Y) => IsSeparated f) :=
    IsSeparated.isStableUnderBaseChange
  have : IsSeparated (Limits.pullback.fst (ProjSpace.π R D.Nd) πZ) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := fun {X Y : Scheme.{u}} (f : X ⟶ Y) => IsSeparated f)
      (IsPullback.of_hasPullback (ProjSpace.π R D.Nd) πZ).flip inferInstance
  have : IsClosedImmersion (Limits.pullback.lift D.ιN D.p D.hoverN
      ≫ Limits.pullback.fst (ProjSpace.π R D.Nd) πZ) := by
    rw [Limits.pullback.lift_fst]; exact D.hιN_closed
  exact IsClosedImmersion.of_comp _ (Limits.pullback.fst (ProjSpace.π R D.Nd) πZ)


theorem finite_relHPresheaf_obj_chow [IsNoetherianRing R] [IsProper πZ]
    {W : Z.Opens} (hW : IsAffineOpen W) (b : ℕ) :
    Module.Finite Γ(Z, W) ((relHPresheaf D.p πZ
      (ProjSpace.stdCoverPullback D.ιN) b).obj W) := by
  have : IsSeparated (D.p ≫ πZ) := inferInstance
  have := lift_isClosedImm πZ D
  let : Algebra R Γ(Z, W) := Scheme.TwoAffineOpenCover.algebraOfHom πZ W
  have : IsNoetherian Z := isNoeth_of_proper πZ
  have hNoeth : IsNoetherianRing Γ(Z, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  set K' := ProjSpace.stdCoverPullback D.ιN
  set pW : D.V'.Opens := (Opens.map D.p.base).obj W
  suffices key : Module.Finite Γ(Z, W) (relAltH D.p πZ K' W b) by exact key
  have hsq : (pW.ι ≫ D.ιN) ≫ ProjSpace.π R D.Nd
      = ((D.p ∣_ W) ≫ hW.isoSpec.hom)
        ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z, W))) := by
    rw [Category.assoc, D.hoverN, Category.assoc,
      show hW.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R Γ(Z, W))) = W.ι ≫ πZ from by
        rw [specMap_algebraMap_eq_fromSpec_comp πZ hW,
            ← hW.isoSpec_inv_ι, ← Category.assoc, hW.isoSpec.hom_inv_id_assoc],
      ← Category.assoc, ← morphismRestrict_ι D.p W, Category.assoc]
  let ιW := (ProjSpace.isPullback_map R Γ(Z, W) D.Nd).lift _ _ hsq
  have hιW_fst := (ProjSpace.isPullback_map R Γ(Z, W) D.Nd).lift_fst _ _ hsq
  have hιW_snd := (ProjSpace.isPullback_map R Γ(Z, W) D.Nd).lift_snd _ _ hsq
  have hιW_cl : IsClosedImmersion ιW := by
    have : IsProper (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd) := hιW_snd ▸ inferInstance
    have hprop : IsProper ιW := IsProper.of_comp ιW (ProjSpace.π Γ(Z, W) D.Nd)
    have : Mono (pW.ι ≫ D.ιN) := mono_comp _ _
    have hmono : Mono ιW := mono_of_mono_fac hιW_fst
    exact (IsClosedImmersion.iff_isProper_and_mono ιW).mpr ⟨hprop, hmono⟩
  have hiva := @OModulePresheaf.cechFinite_unit_of_isClosedImmersion_proj Γ(Z, W) _ hNoeth D.Nd _
    ιW hιW_cl
  have hopen : ∀ {q} (τ : K'.Idx q),
      pW.ι ''ᵁ (ProjSpace.stdCoverPullback ιW).inter τ
        = K'.inter τ ⊓ (Opens.map D.p.base).obj W := fun τ => by
    have hchart : ∀ j, (ProjSpace.stdCoverPullback ιW).U j = pW.ι ⁻¹ᵁ K'.U j := fun j => by
      change ιW ⁻¹ᵁ (ProjSpace.stdCover Γ(Z, W) D.Nd).U j
        = pW.ι ⁻¹ᵁ (D.ιN ⁻¹ᵁ (ProjSpace.stdCover R D.Nd).U j)
      rw [← Scheme.Hom.comp_preimage, ← hιW_fst, Scheme.Hom.comp_preimage,
        show (ProjSpace.stdCover R D.Nd).U j
          = AlgebraicGeometry.Proj.basicOpen _ (MvPolynomial.X j.down) from rfl,
        ProjSpace.map_preimage_basicOpen_X R Γ(Z, W) D.Nd j.down]
      rfl
    rw [show (ProjSpace.stdCoverPullback ιW).inter τ
          = pW.ι ⁻¹ᵁ K'.inter τ from
        (iInf_congr fun j => hchart (τ.1 j)).trans (map_iInf_fin pW.ι _).symm,
      Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  let instMR : ∀ O : (pW : Scheme.{u}).Opens, Module Γ(Z, W) Γ((pW : Scheme.{u}), O) :=
    fun O => (OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).module O
  have hact : ∀ (O : (pW : Scheme.{u}).Opens),
      (Scheme.ΓSpecIso (CommRingCat.of Γ(Z, W))).inv
          ≫ (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd).app ⊤
          ≫ (pW : Scheme.{u}).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op
        = D.p.appLE W (pW.ι ''ᵁ O) (Scheme.Opens.ι_image_le _ _) := fun O => by
    rw [show (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd).app ⊤
          ≫ (pW : Scheme.{u}).presheaf.map (homOfLE (le_top : O ≤ ⊤)).op
        = hW.isoSpec.hom.appTop ≫ (D.p ∣_ W).appLE ⊤ O le_top from
        hιW_snd ▸ Scheme.Hom.comp_appLE _ _ ⊤ O le_top,
      IsAffineOpen.isoSpec_hom_appTop,
      show (Scheme.ΓSpecIso (CommRingCat.of Γ(Z, W))).inv = (Scheme.ΓSpecIso Γ(Z, W)).inv
        from rfl,
      Category.assoc (obj := CommRingCat), Iso.inv_hom_id_assoc]
    erw [morphismRestrict_appLE, Scheme.Opens.topIso_inv]
    erw [Scheme.Hom.map_appLE]
  let φC : ∀ q, (OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).cochain
        (ProjSpace.stdCoverPullback ιW) q
      ≃ₗ[Γ(Z, W)] relAltC D.p πZ K' W q := fun q =>
    { toFun := fun f τ => (D.V'.presheaf.map (homOfLE (hopen τ).ge).op).hom (f τ)
      invFun := fun g τ => (D.V'.presheaf.map (homOfLE (hopen τ).le).op).hom (g τ)
      left_inv := fun f => funext fun τ =>
        (res_res' _ _ _).trans (res_refl' _ _)
      right_inv := fun g => funext fun τ =>
        (res_res' _ _ _).trans (res_refl' _ _)
      map_add' := fun _ _ => funext fun τ => map_add _ _ _
      map_smul' := fun r f => funext fun τ => by
        have hstep : ∀ (x : Γ(D.V', pW.ι ''ᵁ
            (ProjSpace.stdCoverPullback ιW).inter τ)),
            (D.V'.presheaf.map (homOfLE (hopen τ).ge).op).hom
                ((D.p.appLE W _ (Scheme.Opens.ι_image_le _ _)).hom r * x)
              = (D.p.appLE W (K'.inter τ ⊓ (Opens.map D.p.base).obj W)
                  inf_le_right).hom r
                * (D.V'.presheaf.map (homOfLE (hopen τ).ge).op).hom x := fun x => by
          rw [map_mul, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
        refine (congrArg _ (?_ : (r • f) τ = _)).trans (hstep (f τ))
        exact congrArg₂ (α := Γ(D.V', _)) (· * ·)
          (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom (hact _)) r) rfl }
  have hcomm : ∀ q f, φC (q + 1)
        ((OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).d
          (ProjSpace.stdCoverPullback ιW) q f)
      = relAltd D.p πZ K' W q (φC q f) := fun q f => funext fun τ => by
    change (D.V'.presheaf.map (homOfLE (hopen τ).ge).op).hom
        ((OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).d (ProjSpace.stdCoverPullback ιW)
          q f τ)
      = relAltd D.p πZ K' W q (φC q f) τ
    erw [OModulePresheaf.d_apply, relAltd_apply']
    refine (map_sum ((D.V'.presheaf.map (homOfLE (hopen τ).ge).op).hom : _ →+* _) _ _).trans
      (Finset.sum_congr rfl fun j _ => (map_zsmul
          ((D.V'.presheaf.map (homOfLE (hopen τ).ge).op).hom : _ →+* _) _ _).trans
        (congrArg (((-1 : ℤ) ^ (j : ℕ)) • ·) ?_))
    exact (res_res' (V := D.V') (hopen τ).ge _
        (f (K'.face τ j))).trans
      (res_res' (V := D.V') (inf_le_inf_right _ (K'.inter_le_inter_face τ j))
        (hopen (K'.face τ j)).ge (f (K'.face τ j))).symm
  let Φker : ∀ q, ↥(LinearMap.ker ((OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).d
        (ProjSpace.stdCoverPullback ιW) q))
      →ₗ[Γ(Z, W)] relAltH D.p πZ K' W q := fun q =>
    { toFun := fun x => Submodule.Quotient.mk ⟨φC q x.1, LinearMap.mem_ker.mpr
        ((hcomm q x.1).symm.trans ((congrArg _ (LinearMap.mem_ker.mp x.2)).trans (map_zero _)))⟩
      map_add' := fun _ _ => congrArg Submodule.Quotient.mk (Subtype.ext (map_add _ _ _))
      map_smul' := fun a x => congrArg Submodule.Quotient.mk
        (Subtype.ext ((φC q).map_smul a x.1)) }
  have hΦsurj : ∀ q, Function.Surjective (Φker q) := fun q z => z.inductionOn' fun y =>
    ⟨⟨(φC q).symm y.1, LinearMap.mem_ker.mpr ((φC (q + 1)).injective
        ((hcomm q _).trans ((congrArg _ ((φC q).apply_symm_apply y.1)).trans
          ((LinearMap.mem_ker.mp y.2).trans (map_zero _).symm))))⟩,
      congrArg Submodule.Quotient.mk (Subtype.ext ((φC q).apply_symm_apply y.1))⟩
  rcases b with _ | b'
  · have := hiva.1; exact Module.Finite.of_surjective (Φker 0) (hΦsurj 0)
  · have hfinite : Module.Finite Γ(Z, W)
        ((OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).HSucc
          (ProjSpace.stdCoverPullback ιW) b') := hiva.2 b'
    let B : Submodule Γ(Z, W)
        (LinearMap.ker ((OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).d
          (ProjSpace.stdCoverPullback ιW) (b' + 1))) :=
      (LinearMap.range ((OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).d
        (ProjSpace.stdCoverPullback ιW) b')).comap
        (LinearMap.ker ((OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).d
          (ProjSpace.stdCoverPullback ιW) (b' + 1))).subtype
    have hB : B ≤ LinearMap.ker (Φker (b' + 1)) := by
      intro x hxB
      obtain ⟨y, hy⟩ :
          ∃ y : (OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).cochain
              (ProjSpace.stdCoverPullback ιW) b',
            (OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).d
              (ProjSpace.stdCoverPullback ιW) b' y = x.1 := hxB
      apply LinearMap.mem_ker.mpr
      apply (Submodule.Quotient.mk_eq_zero (relAltHB D.p πZ K' W (b' + 1))).mpr
      exact ⟨φC b' y, (hcomm b' y).symm.trans (congrArg (φC (b' + 1)) hy)⟩
    let ΦH : (OModulePresheaf.unit (ιW ≫ ProjSpace.π Γ(Z, W) D.Nd)).HSucc
        (ProjSpace.stdCoverPullback ιW) b' →ₗ[Γ(Z, W)] relAltH D.p πZ K' W (b' + 1) :=
      B.liftQ (Φker (b' + 1)) hB
    apply Module.Finite.of_surjective ΦH
    apply (LinearMap.range_eq_top (f := ΦH)).mp
    exact (Submodule.range_liftQ B (Φker (b' + 1)) hB).trans
      (LinearMap.range_eq_top_of_surjective (Φker (b' + 1)) (hΦsurj (b' + 1)))

theorem isCoherent_relHPresheaf_chow' [IsNoetherianRing R] [IsProper πZ] (b : ℕ) :
    (relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).IsCoherent :=
  fun W => finite_relHPresheaf_obj_chow πZ D W.2 b

end RelHPresheafChow

end AlgebraicGeometry.OModulePresheaf.Leray

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem _root_.AlgebraicGeometry.OModulePresheaf.Leray.isCoherent_relHPresheaf_chow {R : Type u}
    [CommRing R] [IsNoetherianRing R]
    {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsProper πZ] (D : ChowDatumProj πZ) (b : ℕ) :
    (OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).IsCoherent :=
  AlgebraicGeometry.OModulePresheaf.Leray.isCoherent_relHPresheaf_chow' πZ D b

end
end OModulePresheaf_Leray_isCoherent_relHPresheaf_chow
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation

attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module
  ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd
  ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg
  ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR
  ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup
  ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ
  ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module
  ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup
  ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq
  ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq
  ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq
  ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec
  ProjSpaceCech.GradedModule.Hom.mk.injEq
