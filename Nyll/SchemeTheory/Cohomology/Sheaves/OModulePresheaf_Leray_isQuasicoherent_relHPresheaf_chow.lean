/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Noetherian
import Nyll.SchemeTheory.ProjectiveSpace.Cover
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafLerayBicomplex

/-!
Quasicoherence of the relative cohomology presheaf in the Chow construction.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs
namespace OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow

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

theorem isQuasicoherent_relHPresheaf_chow' [IsSeparated πZ] (b : ℕ) :
    (relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN) b).IsQuasicoherent := by
  have : IsClosedImmersion D.ιN := D.hιN_closed
  have : IsSeparated (D.p ≫ πZ) := inferInstance
  set K' := ProjSpace.stdCoverPullback D.ιN
  let : ∀ O : D.V'.Opens, Module R Γ(D.V', O) := Scheme.OrderedAffineCoverOf.moduleSections (D.p ≫
    πZ)
  intro U f
  set g : ∀ {q} (τ : K'.Idx q),
      Γ(D.V', K'.inter τ ⊓ (Opens.map D.p.base).obj U.1) := fun τ =>
    (D.p.appLE U.1 (K'.inter τ ⊓ (Opens.map D.p.base).obj U.1) inf_le_right).hom f
  have hbo : ∀ {q} (τ : K'.Idx q),
      D.V'.basicOpen (g τ) = K'.inter τ
        ⊓ (Opens.map D.p.base).obj (Z.basicOpen f) := fun τ => by
    rw [show g τ = (D.V'.presheaf.map (homOfLE inf_le_right).op).hom ((D.p.app U.1).hom f) from rfl,
      Scheme.basicOpen_res, ← Scheme.preimage_basicOpen,
      inf_assoc, inf_eq_right.mpr ((Opens.map D.p.base).monotone (Z.basicOpen_le f))]
  have haff : ∀ {q} (τ : K'.Idx q),
      IsAffineOpen (K'.inter τ ⊓ (Opens.map D.p.base).obj U.1) := fun τ =>
    Scheme.OrderedAffineCover.fiberAffineOpen D.p πZ (K'.isAffineOpen_inter (D.p ≫ πZ) τ) U.2
  let resC : ∀ q, relAltC D.p πZ K' U.1 q
      →ₗ[R] relAltC D.p πZ K' (Z.basicOpen f) q := fun q =>
    relRes D.p πZ K' (Z.basicOpen_le f) q
  have hres_d : ∀ q, resC (q + 1) ∘ₗ relAltd D.p πZ K' U.1 q
      = relAltd D.p πZ K' (Z.basicOpen f) q ∘ₗ resC q := fun q =>
    relRes_comm D.p πZ K' (Z.basicOpen_le f) q
  have hres_smul : ∀ q (a : Γ(Z, U.1)) (y : relAltC D.p πZ K' U.1 q),
      resC q (a • y) = (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom a • resC q y :=
    fun q a y => funext fun τ =>
      (pullOpen D.p πZ (K'.inter τ)).res_smul
        (Z.basicOpen_le f) a (y τ)
  have hCsurj : ∀ q (x : relAltC D.p πZ K' (Z.basicOpen f) q),
      ∃ (N : ℕ) (y : relAltC D.p πZ K' U.1 q),
        resC q y = (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom (f ^ N) • x := by
    intro q x
    have hex : ∀ (τ : K'.Idx q)
        (x' : Γ(D.V', K'.inter τ ⊓ (Opens.map D.p.base).obj (Z.basicOpen f))),
        ∃ (n : ℕ) (a : Γ(D.V', K'.inter τ ⊓ (Opens.map D.p.base).obj U.1)),
        (D.V'.presheaf.map (homOfLE (inf_le_inf_left _
            ((Opens.map D.p.base).monotone (Z.basicOpen_le f)))).op).hom a
          = (D.V'.presheaf.map (homOfLE (inf_le_inf_left _
              ((Opens.map D.p.base).monotone (Z.basicOpen_le f)))).op).hom (g τ) ^ n * x' :=
      fun τ x' => by
      have := (haff τ).isLocalization_basicOpen (g τ)
      obtain ⟨⟨a, _, n, rfl⟩, ha⟩ :=
        IsLocalization.surj (S := Γ(D.V', D.V'.basicOpen (g τ))) (.powers (g τ))
          ((D.V'.presheaf.map (homOfLE (hbo τ).le).op).hom x')
      have ha' : (D.V'.presheaf.map (homOfLE (D.V'.basicOpen_le (g τ))).op).hom a
          = (D.V'.presheaf.map (homOfLE (hbo τ).le).op).hom x'
            * (D.V'.presheaf.map (homOfLE (D.V'.basicOpen_le (g τ))).op).hom (g τ ^ n) := ha.symm
      refine ⟨n, a, ?_⟩
      rw [← res_res' (hbo τ).ge (D.V'.basicOpen_le (g τ)),
        ← res_res' (hbo τ).ge (D.V'.basicOpen_le (g τ)), ha',
        map_mul, res_res', res_refl', map_pow, map_pow,
        res_res', mul_comm]
    choose n a ha using fun τ => hex τ (x τ)
    refine ⟨Finset.univ.sup n, fun τ => g τ ^ (Finset.univ.sup n - n τ) * a τ, funext fun τ => ?_⟩
    have hcore : ∀ (x' : Γ(D.V', K'.inter τ
        ⊓ (Opens.map D.p.base).obj (Z.basicOpen f))),
        (D.V'.presheaf.map (homOfLE (inf_le_inf_left _
            ((Opens.map D.p.base).monotone (Z.basicOpen_le f)))).op).hom
            (g τ ^ (Finset.univ.sup n - n τ) * a τ)
          = (D.V'.presheaf.map (homOfLE (inf_le_inf_left _
              ((Opens.map D.p.base).monotone (Z.basicOpen_le f)))).op).hom
              (g τ) ^ Finset.univ.sup n * x'
          → (D.V'.presheaf.map (homOfLE (inf_le_inf_left _
              ((Opens.map D.p.base).monotone (Z.basicOpen_le f)))).op).hom
              (g τ ^ (Finset.univ.sup n - n τ) * a τ)
            = (D.p.appLE (Z.basicOpen f) (K'.inter τ
                  ⊓ (Opens.map D.p.base).obj (Z.basicOpen f)) inf_le_right).hom
                ((Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom (f ^ Finset.univ.sup n))
              * x' := fun x' hx' => hx'.trans (congrArg (· * x') (by
      rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE, ← Scheme.Hom.appLE_map _ inf_le_right
          (homOfLE (inf_le_inf_left _ ((Opens.map D.p.base).monotone (Z.basicOpen_le f)))).op,
        CommRingCat.comp_apply, map_pow, map_pow])).symm
    exact hcore (x τ) (by
      erw [map_mul, map_pow, ha, ← mul_assoc, ← pow_add,
        Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ τ))])
  have hCann : ∀ q (y : relAltC D.p πZ K' U.1 q), resC q y = 0 →
      ∃ M : ℕ, (f ^ M : Γ(Z, U.1)) • y = 0 := by
    intro q y hy
    have hex : ∀ (τ : K'.Idx q)
        (y' : Γ(D.V', K'.inter τ ⊓ (Opens.map D.p.base).obj U.1)),
        (D.V'.presheaf.map (homOfLE (inf_le_inf_left _
            ((Opens.map D.p.base).monotone (Z.basicOpen_le f)))).op).hom y' = 0 →
        ∃ m, g τ ^ m * y' = 0 := fun τ y' hy' => by
      have := (haff τ).isLocalization_basicOpen (g τ)
      obtain ⟨⟨_, m, rfl⟩, hm⟩ :=
        (IsLocalization.map_eq_zero_iff (S := Γ(D.V', D.V'.basicOpen (g τ)))
          (.powers (g τ)) y').mp (by
          rw [show algebraMap _ _ y'
            = (D.V'.presheaf.map (homOfLE (D.V'.basicOpen_le (g τ))).op).hom y' from rfl,
            ← res_res' (hbo τ).le (inf_le_inf_left _
              ((Opens.map D.p.base).monotone (Z.basicOpen_le f))), hy', map_zero])
      exact ⟨m, hm⟩
    choose m hm using fun τ => hex τ (y τ) (congrFun hy τ)
    refine ⟨Finset.univ.sup m, funext fun τ => ?_⟩
    have hcore : ∀ (y' : Γ(D.V', K'.inter τ ⊓ (Opens.map D.p.base).obj U.1)),
        g τ ^ m τ * y' = 0 →
        (D.p.appLE U.1 _ inf_le_right).hom (f ^ Finset.univ.sup m) * y' = 0 := fun y' hy0 => by
      rw [map_pow, ← Nat.sub_add_cancel (Finset.le_sup (Finset.mem_univ τ)), pow_add,
        mul_assoc, hy0, mul_zero]
    exact hcore (y τ) (hm τ)
  refine ⟨fun x => x.inductionOn' fun x₀ => ?_, fun y => y.inductionOn' fun y₀ hy => ?_⟩
  · obtain ⟨N, y, hyN⟩ := hCsurj b x₀.1
    obtain ⟨M, hM⟩ := hCann (b + 1) (relAltd D.p πZ K' U.1 b y) (by
      rw [← LinearMap.comp_apply, hres_d, LinearMap.comp_apply, hyN,
        relAltd_Γsmul, LinearMap.mem_ker.mp x₀.2, smul_zero])
    refine ⟨M + N, Submodule.Quotient.mk ⟨(f ^ M : Γ(Z, U.1)) • y, LinearMap.mem_ker.mpr
      ((relAltd_Γsmul D.p πZ K' U.1 b _ y).trans hM)⟩,
      congrArg Submodule.Quotient.mk (Subtype.ext
        (show resC b ((f ^ M : Γ(Z, U.1)) • y) = _ from ?_))⟩
    simp only [hres_smul, hyN, map_pow, smul_smul, ← pow_add]; rfl
  · have hyB : (relResKer D.p πZ K' (Z.basicOpen_le f) b y₀)
        ∈ relAltHB D.p πZ K' (Z.basicOpen f) b :=
      (Submodule.Quotient.mk_eq_zero _).mp hy
    rcases b with _ | b'
    · obtain ⟨M, hM⟩ := hCann 0 y₀.1 (congrArg Subtype.val ((Submodule.mem_bot R).mp hyB))
      exact ⟨M, (Submodule.Quotient.mk_eq_zero _).mpr
        ((Submodule.mem_bot R).mpr (Subtype.ext hM))⟩
    · obtain ⟨w, hw⟩ := hyB
      obtain ⟨N, w', hw'⟩ := hCsurj b' w
      obtain ⟨M, hM⟩ := hCann (b' + 1)
        ((f ^ N : Γ(Z, U.1)) • y₀.1 - relAltd D.p πZ K' U.1 b' w') (by
        rw [map_sub, hres_smul, ← LinearMap.comp_apply, hres_d, LinearMap.comp_apply, hw',
          relAltd_Γsmul,
          show resC (b' + 1) y₀.1
            = relAltd D.p πZ K' (Z.basicOpen f) b' w from hw.symm,
          sub_self])
      refine ⟨M + N, (Submodule.Quotient.mk_eq_zero _).mpr ⟨(f ^ M : Γ(Z, U.1)) • w', ?_⟩⟩
      refine (eq_comm.mpr (sub_eq_zero.mp ?_) :
        relAltd D.p πZ K' U.1 b' ((f ^ M : Γ(Z, U.1)) • w')
          = (f ^ (M + N) : Γ(Z, U.1)) • y₀.1)
      rw [relAltd_Γsmul D.p πZ K' U.1 b' _ w', pow_add, mul_smul, ← smul_sub]
      exact hM

end RelHPresheafChow

end AlgebraicGeometry.OModulePresheaf.Leray

attribute [local instance] MvPolynomial.gradedAlgebra in
theorem _root_.AlgebraicGeometry.OModulePresheaf.Leray.isQuasicoherent_relHPresheaf_chow {R : Type
    u} [CommRing R]
    {Z : Scheme.{u}} (πZ : Z ⟶ Spec (.of R)) [IsSeparated πZ] (D : ChowDatumProj πZ) (b : ℕ) :
    (OModulePresheaf.Leray.relHPresheaf D.p πZ (ProjSpace.stdCoverPullback D.ιN)
      b).IsQuasicoherent :=
  AlgebraicGeometry.OModulePresheaf.Leray.isQuasicoherent_relHPresheaf_chow' πZ D b

end
end OModulePresheaf_Leray_isQuasicoherent_relHPresheaf_chow
end AlgebraicCurves.Cohomology.Sheaves.Proofs
end ProofImplementation
