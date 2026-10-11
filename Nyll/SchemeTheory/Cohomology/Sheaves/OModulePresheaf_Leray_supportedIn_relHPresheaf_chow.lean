/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_supportedIn_relHPresheaf_chow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Noetherian
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafLerayBicomplex
import Nyll.SchemeTheory.Cohomology.Cech.Scheme_OrderedAffineCoverOf_ker_d_succ_le_range_d_of_isAffineOpen
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_Leray_nonempty_relHPresheaf_obj_equiv_of_isAffineOpen

/-!
Support of the relative cohomology presheaf arising from the Chow construction.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_Leray_supportedIn_relHPresheaf_chow

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

theorem preimage_isAffineOpen {W : Z.Opens} (hW : IsAffineOpen W)
    (hWU : W ≤ D.U) : IsAffineOpen ((Opens.map D.p.base).obj W) := by
  have : IsAffine (W : Scheme.{u}) := hW
  have : IsAffine (Limits.pullback D.p W.ι) :=
    IsAffine.of_isIso ((Limits.pullback.congrHom rfl (Z.homOfLE_ι hWU).symm).hom ≫
      (Limits.pullbackLeftPullbackSndIso D.p D.U.ι (Z.homOfLE hWU)).inv ≫
      Limits.pullback.snd _ _)
  exact .of_isIso (isPullback_morphismRestrict D.p W).flip.isoPullback.hom

theorem supportedIn_relHPresheaf_chow' [IsSeparated πZ] (b : ℕ) (hb : 1 ≤ b) :
    (relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).SupportedIn
      ⟨(D.U : Set Z)ᶜ, D.U.isOpen.isClosed_compl⟩ := by
  have : IsSeparated (D.p ≫ πZ) := inferInstance
  let : ∀ O : D.V'.Opens, Module R Γ(D.V', O) := Scheme.OrderedAffineCoverOf.moduleSections (D.p ≫
    πZ)
  set K' := ProjSpace.stdCoverPullback D.ιN
  intro W hW
  have hWU : (W : Z.Opens) ≤ D.U := fun x hx =>
    not_not.mp fun hc => (Set.ext_iff.mp hW x).mp ⟨hx, hc⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, (Nat.sub_add_cancel hb).symm⟩
  have haffpW : IsAffineOpen ((Opens.map D.p.base).obj (W : Z.Opens)) :=
    preimage_isAffineOpen πZ D W.2 hWU
  have hacy := Scheme.OrderedAffineCoverOf.ker_d_succ_le_range_d_of_isAffineOpen (D.p ≫ πZ)
    (restrictToPreimage D.p πZ K' W.2) haffpW b'
  have hsub : Subsingleton ((restrictToPreimage D.p πZ K' W.2).HSucc (D.p ≫ πZ) b') :=
    Submodule.Quotient.subsingleton_iff.mpr
      (Submodule.eq_top_iff'.mpr fun z => hacy z.2)
  obtain ⟨e⟩ := (nonempty_relHPresheaf_obj_equiv_of_isAffineOpen D.p πZ K' W.2).2 b'
  exact e.toEquiv.subsingleton_congr.mpr hsub

end RelHPresheafChow

end AlgebraicGeometry.OModulePresheaf.Leray

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem _root_.AlgebraicGeometry.OModulePresheaf.Leray.supportedIn_relHPresheaf_chow {R : Type u}
    [CommRing R]
    {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsSeparated πZ] (D : ChowDatumProj πZ) (b : ℕ) (hb :
      1 ≤ b) :
    (OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).SupportedIn
      ⟨(D.U : Set Z)ᶜ, D.U.isOpen.isClosed_compl⟩ :=
  AlgebraicGeometry.OModulePresheaf.Leray.supportedIn_relHPresheaf_chow' πZ D b hb

end
end OModulePresheaf_Leray_supportedIn_relHPresheaf_chow
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation

attribute [-instance] DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR
  DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp
  DoubleComplex.instAddCommGroupE₂I
attribute [-simp] DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec
  DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec
  DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq
