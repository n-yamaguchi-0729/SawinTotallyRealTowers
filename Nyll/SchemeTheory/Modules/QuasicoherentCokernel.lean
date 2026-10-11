/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.QuasicoherentLocal
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Quasicoherence of actual cokernels

On an affine scheme, the actual morphism is transported through its
canonical tilde isomorphisms. The existing tilde adjunction preserves its
cokernel. Restriction and the shared affine-presentation criterion then
give the result on arbitrary schemes.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

private def affineTildeIso {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [M.IsQuasicoherent] :
    (tilde.functor R).obj ((moduleSpecΓFunctor (R := R)).obj M) ≅ M := by
  let f : (tilde.functor R).obj ((moduleSpecΓFunctor (R := R)).obj M) ⟶ M :=
    fromTildeΓ (R := R) M
  have : IsIso (C := (Spec R).Modules) f :=
    isIso_fromTildeΓ_of_isQuasicoherent (R := R) M
  exact asIso (C := (Spec R).Modules) f

/-- The actual cokernel of a morphism between quasicoherent modules on
an affine scheme is quasicoherent. -/
theorem isQuasicoherent_cokernel_toSpec
    {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    (cokernel φ).IsQuasicoherent := by
  let GM : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj M
  let GN : ModuleCat.{u} R := (moduleSpecΓFunctor (R := R)).obj N
  let eM : (tilde.functor R).obj GM ≅ M := affineTildeIso (R := R) M
  let eN : (tilde.functor R).obj GN ≅ N := affineTildeIso (R := R) N
  let f : GM ⟶ GN := (tilde.functor R).preimage (eM.hom ≫ φ ≫ eN.inv)
  have hf : (tilde.functor R).map f ≫ eN.hom = eM.hom ≫ φ := by
    rw [(tilde.functor R).map_preimage]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have : PreservesColimitsOfSize.{u, u} (tilde.functor R) :=
    (tilde.adjunction (R := R)).leftAdjoint_preservesColimits
  let e : (tilde.functor R).obj (cokernel f) ≅ cokernel φ :=
    PreservesCokernel.iso (tilde.functor R) f ≪≫
      cokernel.mapIso ((tilde.functor R).map f) φ eM eN hf
  have hQ : ((tilde.functor R).obj (cokernel f)).IsQuasicoherent :=
    inferInstanceAs (tilde (R := R) (cokernel f)).IsQuasicoherent
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    ((sheafOfModulesEquivalence (Spec R)).functor.mapIso e) hQ

/-- The actual categorical cokernel of a morphism between quasicoherent
modules on any scheme is quasicoherent. -/
theorem isQuasicoherent_cokernel
    {X : Scheme.{u}} {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    (cokernel φ).IsQuasicoherent := by
  apply isQuasicoherent_of_affineSpecRestrictions (cokernel φ)
  intro U hU
  let F : X.Modules ⥤ (Spec Γ(X, U)).Modules := restrictFunctor hU.fromSpec
  have : (F.obj M).IsQuasicoherent := isQuasicoherent_restrictFunctor hU.fromSpec M
  have : (F.obj N).IsQuasicoherent := isQuasicoherent_restrictFunctor hU.fromSpec N
  have : PreservesColimitsOfSize.{u, u} F :=
    (restrictAdjunction hU.fromSpec).leftAdjoint_preservesColimits
  have : F.PreservesZeroMorphisms := { map_zero := fun _ _ => rfl }
  have hQ : (cokernel (F.map φ)).IsQuasicoherent :=
    isQuasicoherent_cokernel_toSpec (R := Γ(X, U))
      (M := F.obj M) (N := F.obj N) (F.map φ)
  let e := (sheafOfModulesEquivalence (Spec Γ(X, U))).functor.mapIso
    (PreservesCokernel.iso F φ).symm
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, U)).ringCatSheaf).prop_of_iso e hQ

end AlgebraicGeometry.Scheme.Modules
