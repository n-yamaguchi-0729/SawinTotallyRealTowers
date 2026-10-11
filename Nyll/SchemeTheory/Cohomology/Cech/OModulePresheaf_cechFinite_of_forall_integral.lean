/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_forall_integral.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafIdealFiltration
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_hasDevissageStep
import Nyll.SchemeTheory.Cohomology.Cech.OModulePresheaf_cechFinite_pushforward_of_isIntegral_of_ih
import Nyll.SchemeTheory.Cohomology.Cech.OModulePresheaf_cechFinite_of_forall_cechFinite_idealPowQuot
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_isCoherent_idealPowQuot
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_isQuasicoherent_idealPowQuot
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_supportedIn_idealPowQuot
import Nyll.SchemeTheory.Cohomology.Cech.OModulePresheaf_cechFinite_of_affSES_mid
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Noetherian.Basic
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions

/-!
Cech finiteness from the corresponding assertion on integral closed subschemes of the support.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_cechFinite_of_forall_integral

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
namespace Driver
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

theorem isNoetherian_of_isProper [IsNoetherianRing R] (π : V ⟶ Spec (.of R)) [IsProper π] :
    IsNoetherian V := by
  have : LocallyOfFiniteType π := inferInstance
  have : IsLocallyNoetherian (Spec (CommRingCat.of R)) := inferInstance
  have : IsLocallyNoetherian V := LocallyOfFiniteType.isLocallyNoetherian π
  have : CompactSpace V := QuasiCompact.compactSpace_of_compactSpace π
  exact {}

theorem cechFinite_of_supportedIn_empty (π : V ⟶ Spec (.of R)) [IsSeparated π] (K :
    V.OrderedAffineCover)
    (F : OModulePresheaf π) {Y : Closeds V} (hY : (Y : Set V) = ∅) (hFs : F.SupportedIn Y) :
      F.CechFinite K := by
  have hCF : ∀ q, Subsingleton (F.cochain K q) := fun q =>
    ⟨fun a b => funext fun s => @Subsingleton.elim _
      (hFs ⟨_, Scheme.OrderedAffineCover.isAffineOpen_inter π K s⟩ (
        by rw [hY]; exact Set.inter_empty _)) _ _⟩
  rw [OModulePresheaf.cechFinite_iff]
  refine ⟨?_, fun i => ?_⟩
  · have := hCF 0; infer_instance
  · have := hCF (i + 1); infer_instance

end AlgebraicGeometry.OModulePresheaf.Driver

open AlgebraicGeometry.OModulePresheaf.Driver in
theorem _root_.AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_integral
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))
      [IsProper π]
    (K : V.OrderedAffineCover)
    (hInt : ∀ Z₀ : TopologicalSpace.Closeds V, (Z₀ : Set V).Nonempty →
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme →
      (∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' →
        G.CechFinite K) →
      (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal
        Z₀).subschemeι).CechFinite K) :
    ∀ (Y : TopologicalSpace.Closeds V) (F : OModulePresheaf π),
      F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y → F.CechFinite K := by
  have : IsSeparated π := inferInstance
  have : IsNoetherian V := isNoetherian_of_isProper π
  have : IsLocallyNoetherian V := inferInstance
  intro Y
  induction Y using WellFoundedLT.induction with
  | _ Y ihY =>
  intro F hFc hFq hFs
  by_cases hYne : (Y : Set V).Nonempty
  · have hStep : ∀ F' : OModulePresheaf π, F'.IsCoherent → F'.IsQuasicoherent → F'.SupportedIn Y →
        OModulePresheaf.IdealAnnihilates π (Scheme.IdealSheafData.vanishingIdeal Y) F' →
          F'.CechFinite K := by
      intro F' hFc' hFq' hFs' hAnn'
      obtain ⟨S⟩ := AlgebraicGeometry.OModulePresheaf.hasDevissageStep π F' hFc' hFq' Y hYne hFs'
        hAnn'
      have hG₃ : S.G₃.CechFinite K := ihY S.Z₁ S.Z₁_lt S.G₃ S.isCoherent_G₃ S.isQuasicoherent_G₃
        S.supportedIn_G₃
      have hCP : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal
        S.Z₀).subschemeι S.H).CechFinite K := by
        rcases lt_or_eq_of_le S.Z₀_le with hlt | heq
        · exact ihY S.Z₀ hlt _ S.isCoherent_pushforward S.isQuasicoherent_pushforward
            S.supportedIn_pushforward
        · have ih0 : ∀ Y' < S.Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent →
              G.SupportedIn Y' →
              G.CechFinite K := fun Y' hY' => ihY Y' (heq ▸ hY')
          exact AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_of_isIntegral_of_ih π K
            S.Z₀_nonempty
            S.isIntegral (hInt S.Z₀ S.Z₀_nonempty S.isIntegral ih0) ih0 S.H S.isCoherent_pushforward
            S.isQuasicoherent_pushforward
      exact AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_mid S.ses K hCP hG₃
    exact AlgebraicGeometry.OModulePresheaf.cechFinite_of_forall_cechFinite_idealPowQuot π K Y F
      hFc hFq hFs fun k =>
      hStep _ (AlgebraicGeometry.OModulePresheaf.isCoherent_idealPowQuot π _ F k hFc)
        (AlgebraicGeometry.OModulePresheaf.isQuasicoherent_idealPowQuot π _ F k hFq)
        (AlgebraicGeometry.OModulePresheaf.supportedIn_idealPowQuot π _ F k hFs)
        (AlgebraicGeometry.OModulePresheaf.idealAnnihilates_idealPowQuot π _ F k)
  · exact cechFinite_of_supportedIn_empty π K F (Set.not_nonempty_iff_eq_empty.mp hYne) hFs
end AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_cechFinite_of_forall_integral
end ProofImplementation
