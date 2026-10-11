/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Modules.GlobalSectionLocalization
import Nyll.SchemeTheory.Modules.PushforwardSectionComparison
import Nyll.SchemeTheory.Modules.PushforwardCoefficients
import Nyll.SchemeTheory.Modules.NativeSectionObjects
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.QuasiSeparated
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Quasicoherent pushforward along quasi-compact open immersions

Proves localization of pushforward sections for a quasicoherent module along a quasi-compact
open immersion into an affine scheme. This gives quasicoherence of the direct image.
-/

noncomputable section

universe u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

private def sourceRing (X : Scheme.{u}) : CommRingCat.{u} := Γ(X, ⊤)

private def sourceCoefficient {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) : R →+* sourceRing X :=
  j.pushforwardGlobalCoefficient

private def sourceBasicOpen {R : CommRingCat.{u}} {X : Scheme.{u}}
    (σ : R →+* sourceRing X) (r : R) : X.Opens :=
  X.basicOpen (σ r)

private def sourceModuleOver {R : CommRingCat.{u}} {X : Scheme.{u}}
    (M : X.Modules) (σ : R →+* sourceRing X) : X.Opensᵒᵖ ⥤ ModuleCat.{u} R :=
  globalModulePresheaf M ⋙ ModuleCat.restrictScalars σ

private theorem sourceModuleOver_localizes {R : CommRingCat.{u}} {X : Scheme.{u}}
    (M : X.Modules) [M.IsQuasicoherent] [CompactSpace X] [QuasiSeparatedSpace X]
    (σ : R →+* sourceRing X) (r : R) (W : X.Opens) (hW : W = sourceBasicOpen σ r) :
    IsLocalizedModule (Submonoid.powers r) ((sourceModuleOver M σ).map W.leTop.op).hom := by
  subst W
  exact isLocalizedModule_restrictGlobalScalars_of_qcqs M σ r

private lemma sourceBasicOpen_eq_preimage {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (r : R) :
    j.sectionComparisonOpen (PrimeSpectrum.basicOpen r) = sourceBasicOpen (sourceCoefficient j) r :=
  j.preimage_basicOpen_pushforwardGlobalCoefficient r

/-- The already computed source presheaf is a sheaf by its actual comparison with the
pushforward. -/
private def sourceSheafOnTarget {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) : TopCat.Sheaf (ModuleCat.{u} R) (Spec R) where
  obj := sourceModuleOnTarget j M
  property := TopCat.Presheaf.isSheaf_of_iso (pushforwardModulePresheafIso j M)
    (modulesSpecToSheaf.obj ((pushforward j).obj M)).property

private def sourceSheafIso {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) :
    modulesSpecToSheaf.obj ((pushforward j).obj M) ≅ sourceSheafOnTarget j M :=
  ObjectProperty.isoMk _ (pushforwardModulePresheafIso j M)

private theorem sourceSheaf_isLocalizing {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    [CompactSpace X] [QuasiSeparatedSpace X] : IsLocalizing (sourceSheafOnTarget j M) := by
  intro r
  change IsLocalizedModule (Submonoid.powers r)
    ((sourceModuleOver M (sourceCoefficient j)).map
      (j.sectionComparisonOpen (PrimeSpectrum.basicOpen r)).leTop.op).hom
  exact sourceModuleOver_localizes M (sourceCoefficient j) r
    (j.sectionComparisonOpen (PrimeSpectrum.basicOpen r)) (sourceBasicOpen_eq_preimage j r)

private theorem isLocalizing_pushforward_of_qcqs {R : CommRingCat.{u}} {X : Scheme.{u}}
    (j : X ⟶ Spec R) (M : X.Modules) [M.IsQuasicoherent]
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsLocalizing (modulesSpecToSheaf.obj ((pushforward j).obj M)) :=
  (isLocalizing_iff_of_iso (sourceSheafIso j M)).mpr (sourceSheaf_isLocalizing j M)

/-- Quasicoherent modules on a quasi-compact open subscheme of an affine
scheme have genuinely localizing pushforward sections over the base ring. -/
theorem isLocalizing_pushforward_of_quasiCompact_openImmersion_toSpec
    {R : CommRingCat.{u}} {X : Scheme.{u}} (j : X ⟶ Spec R)
    [IsOpenImmersion j] [QuasiCompact j] (M : X.Modules) [M.IsQuasicoherent] :
    IsLocalizing (modulesSpecToSheaf.obj ((pushforward j).obj M)) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace j
  have : QuasiSeparatedSpace (Spec R) :=
    inferInstanceAs (QuasiSeparatedSpace (PrimeSpectrum R))
  have : QuasiSeparatedSpace X := j.isOpenEmbedding.quasiSeparatedSpace
  exact isLocalizing_pushforward_of_qcqs j M

private theorem isQuasicoherent_of_isLocalizing {R : CommRingCat.{u}}
    (N : (Spec R).Modules) (hN : IsLocalizing (modulesSpecToSheaf.obj N)) :
    N.IsQuasicoherent :=
  (isQuasicoherent_iff_isIso_fromTildeΓ N).mpr
    ((isIso_fromTildeΓ_iff_isLocalizing N).mpr hN)

/-- The actual direct image of a quasicoherent module from a quasi-compact,
quasi-separated scheme to `Spec R` is quasicoherent. -/
theorem isQuasicoherent_pushforward_of_qcqs_toSpec
    {R : CommRingCat.{u}} {X : Scheme.{u}} (g : X ⟶ Spec R)
    [CompactSpace X] [QuasiSeparatedSpace X] (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward g).obj M).IsQuasicoherent :=
  isQuasicoherent_of_isLocalizing ((pushforward g).obj M)
    (isLocalizing_pushforward_of_qcqs g M)

/-- The actual direct image of a quasicoherent module along a quasi-compact
open immersion into an affine scheme is quasicoherent. -/
theorem isQuasicoherent_pushforward_of_quasiCompact_openImmersion_toSpec
    {R : CommRingCat.{u}} {X : Scheme.{u}} (j : X ⟶ Spec R)
    [IsOpenImmersion j] [QuasiCompact j] (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward j).obj M).IsQuasicoherent :=
  isQuasicoherent_of_isLocalizing ((pushforward j).obj M)
    (isLocalizing_pushforward_of_quasiCompact_openImmersion_toSpec j M)

end AlgebraicGeometry.Scheme.Modules
