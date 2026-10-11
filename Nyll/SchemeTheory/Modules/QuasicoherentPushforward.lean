/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.PushforwardLocalization
import Nyll.SchemeTheory.Modules.PushforwardRestrict
import Nyll.SchemeTheory.Modules.QuasicoherentLocal
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.CategoryTheory.ObjectProperty.ClosedUnderIsomorphisms

/-!
# Quasicoherent direct images for open and affine morphisms

The affine-target theorem is transported from the actual `Spec` theorem through
`isoSpec`. The arbitrary-target theorem uses the actual open-restriction comparison
on each affine target open, then the native affine-cover criterion.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- The direct image of a quasicoherent module from a quasi-compact,
quasi-separated source to an affine target is quasicoherent. -/
theorem isQuasicoherent_pushforward_of_qcqs_toAffine
    {X Y : Scheme.{u}} [IsAffine Y] (j : X ⟶ Y)
    [CompactSpace X] [QuasiSeparatedSpace X] (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward j).obj M).IsQuasicoherent := by
  have hSpec : ((pushforward (j ≫ Y.isoSpec.hom)).obj M).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs_toSpec (j ≫ Y.isoSpec.hom) M
  have : ((pushforward Y.isoSpec.hom).obj ((pushforward j).obj M)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec Γ(Y, ⊤)).ringCatSheaf).prop_of_iso
      ((sheafOfModulesEquivalence (Spec Γ(Y, ⊤))).functor.mapIso
        ((pushforwardComp j Y.isoSpec.hom).app M).symm) hSpec
  have hRestrict :
      (((pushforward Y.isoSpec.hom).obj ((pushforward j).obj M)).restrict
        Y.isoSpec.hom).IsQuasicoherent :=
    isQuasicoherent_restrictFunctor Y.isoSpec.hom
      ((pushforward Y.isoSpec.hom).obj ((pushforward j).obj M))
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((sheafOfModulesEquivalence Y).functor.mapIso
      ((restrictFunctorAdjCounitIso Y.isoSpec.hom).app ((pushforward j).obj M)))
    hRestrict

/-- The actual direct image of a quasicoherent module under a quasi-compact
open immersion is quasicoherent over an arbitrary target scheme. -/
theorem isQuasicoherent_pushforward_of_quasiCompact_openImmersion
    {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] [QuasiCompact j]
    (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward j).obj M).IsQuasicoherent := by
  apply isQuasicoherent_of_affineSpecRestrictions ((pushforward j).obj M)
  intro U hU
  have : IsAffine U.toScheme := hU
  have : CompactSpace (j ⁻¹ᵁ U).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (j ∣_ U)
  have : QuasiSeparatedSpace (j ⁻¹ᵁ U).toScheme :=
    (j ∣_ U).isOpenEmbedding.quasiSeparatedSpace
  have hLocal :
      ((pushforward (j ∣_ U)).obj (M.restrict (j ⁻¹ᵁ U).ι)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs_toAffine
      (j ∣_ U) (M.restrict (j ⁻¹ᵁ U).ι)
  have : (((pushforward j).obj M).restrict U.ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((sheafOfModulesEquivalence U.toScheme).functor.mapIso
        ((pushforwardRestrictIso j U).app M)) hLocal
  have hRestrict :
      ((((pushforward j).obj M).restrict U.ι).restrict hU.isoSpec.inv).IsQuasicoherent :=
    isQuasicoherent_restrictFunctor hU.isoSpec.inv
      (((pushforward j).obj M).restrict U.ι)
  exact (SheafOfModules.isQuasicoherent (Spec Γ(Y, U)).ringCatSheaf).prop_of_iso
    ((sheafOfModulesEquivalence (Spec Γ(Y, U))).functor.mapIso
      (((restrictFunctorComp hU.isoSpec.inv U.ι).app ((pushforward j).obj M)).symm ≪≫
        (restrictFunctorCongr hU.isoSpec_inv_ι).app ((pushforward j).obj M)))
    hRestrict

/-- The actual direct image of a quasicoherent module along an affine
morphism is quasicoherent, over an arbitrary target scheme. -/
theorem isQuasicoherent_pushforward_of_isAffineHom
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsAffineHom g]
    (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward g).obj M).IsQuasicoherent := by
  apply isQuasicoherent_of_affineSpecRestrictions ((pushforward g).obj M)
  intro U hU
  have : IsAffine U.toScheme := hU
  have : IsAffine (g ⁻¹ᵁ U).toScheme := hU.preimage g
  have hLocal :
      ((pushforward (g ∣_ U)).obj (M.restrict (g ⁻¹ᵁ U).ι)).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_qcqs_toAffine
      (g ∣_ U) (M.restrict (g ⁻¹ᵁ U).ι)
  have : (((pushforward g).obj M).restrict U.ι).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent U.toScheme.ringCatSheaf).prop_of_iso
      ((sheafOfModulesEquivalence U.toScheme).functor.mapIso
        ((pushforwardRestrictIso g U).app M)) hLocal
  have hRestrict :
      ((((pushforward g).obj M).restrict U.ι).restrict hU.isoSpec.inv).IsQuasicoherent :=
    isQuasicoherent_restrictFunctor hU.isoSpec.inv
      (((pushforward g).obj M).restrict U.ι)
  exact (SheafOfModules.isQuasicoherent (Spec Γ(Y, U)).ringCatSheaf).prop_of_iso
    ((sheafOfModulesEquivalence (Spec Γ(Y, U))).functor.mapIso
      (((restrictFunctorComp hU.isoSpec.inv U.ι).app ((pushforward g).obj M)).symm ≪≫
        (restrictFunctorCongr hU.isoSpec_inv_ι).app ((pushforward g).obj M)))
    hRestrict

end AlgebraicGeometry.Scheme.Modules
