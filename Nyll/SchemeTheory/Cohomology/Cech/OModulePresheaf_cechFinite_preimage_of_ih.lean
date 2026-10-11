/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_preimage_of_ih.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafConstructions
import Nyll.SchemeTheory.Cohomology.Cech.OModulePresheaf_cechFinite_pushforward_iff
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Čech finiteness under closed-subscheme preimage by induction
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_cechFinite_preimage_of_ih

universe u

open _root_.CategoryTheory
open _root_.AlgebraicGeometry
open _root_.TopologicalSpace
open _root_.Opposite

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
namespace Descend
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (i : Z ⟶ V)
  [IsClosedImmersion i]
variable (F : OModulePresheaf (i ≫ π))

theorem isCoherent_pushforward (hFc : F.IsCoherent) : (pushforward π i F).IsCoherent := fun U => by
  let : Module Γ(V, U.1) (F.obj (i ⁻¹ᵁ U.1)) := (pushforward π i F).moduleSections U.1
  let : Algebra Γ(V, U.1) Γ(Z, i ⁻¹ᵁ U.1) := (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  have : IsScalarTower Γ(V, U.1) Γ(Z, i ⁻¹ᵁ U.1) (F.obj (i ⁻¹ᵁ U.1)) :=
    ⟨fun a b x => by change ((i.appLE U.1 _ le_rfl).hom a * b) • x = _; rw [mul_smul]; rfl⟩
  have : Module.Finite Γ(V, U.1) Γ(Z, i ⁻¹ᵁ U.1) :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) fun x => by
      obtain ⟨a, ha⟩ := i.app_surjective U.1 U.2 x
      refine ⟨a, ?_⟩
      change (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom a = x
      rw [Scheme.Hom.appLE_eq_app]
      exact ha
  have := hFc ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩
  exact Module.Finite.trans (R := Γ(V, U.1)) Γ(Z, i ⁻¹ᵁ U.1) (F.obj (i ⁻¹ᵁ U.1))

theorem isQuasicoherent_pushforward (hFq : F.IsQuasicoherent) : (pushforward π i
    F).IsQuasicoherent := fun U f => by
  let : Module Γ(V, U.1) (F.obj (i ⁻¹ᵁ U.1)) := (pushforward π i F).moduleSections U.1
  set g : Γ(Z, i ⁻¹ᵁ U.1) := (i.app U.1).hom f with hg_def
  have hbo : i ⁻¹ᵁ V.basicOpen f = Z.basicOpen g := Scheme.preimage_basicOpen i f
  obtain ⟨hs, ha⟩ := hFq ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ g
  have hpow : ∀ n (y : F.obj (i ⁻¹ᵁ U.1)),
      (f ^ n : Γ(V, U.1)) • y = (g ^ n : Γ(Z, i ⁻¹ᵁ U.1)) • y := fun n y => by
    change (i.appLE U.1 (i ⁻¹ᵁ U.1) le_rfl).hom (f ^ n) • y = _
    rw [map_pow, Scheme.Hom.appLE_eq_app]
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨n, y, hny⟩ := hs (F.res hbo.ge (show F.obj (i ⁻¹ᵁ V.basicOpen f) from x))
    refine ⟨n, y, ?_⟩
    have key := congrArg (F.res hbo.le) hny
    rw [← LinearMap.comp_apply, ← F.res_comp, F.res_smul,
      ← LinearMap.comp_apply (g := F.res hbo.ge), ← F.res_comp,
      LinearMap.congr_fun (F.res_refl _) x] at key
    change F.res _ y = (i.appLE (V.basicOpen f) (i ⁻¹ᵁ V.basicOpen f) le_rfl).hom
        ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom (f ^ n))
      • (show F.obj (i ⁻¹ᵁ V.basicOpen f) from x)
    refine key.trans ?_
    congr 1
    rw [← CommRingCat.comp_apply (f := V.presheaf.map _), Scheme.Hom.map_appLE,
      ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp, map_pow, map_pow]
    congr 1
  · refine (ha y ?_).imp fun n hn => (hpow n y).trans hn
    refine (LinearMap.congr_fun (F.res_comp hbo.ge ((Opens.map i.base).monotone (V.basicOpen_le
      f))) y).trans ?_
    exact (congrArg (F.res hbo.ge)
      (show F.res ((Opens.map i.base).monotone (V.basicOpen_le f)) y = 0 from hy)).trans (map_zero
        _)

theorem supportedIn_pushforward_image {Y' : Closeds Z} (hFs : F.SupportedIn Y') :
    (pushforward π i F).SupportedIn ⟨i.base '' Y', i.isClosedEmbedding.isClosedMap _ Y'.2⟩ := fun
      U hU =>
  hFs ⟨i ⁻¹ᵁ U.1, U.2.preimage i⟩ (by
    refine Set.eq_empty_of_forall_notMem fun x ⟨hxU, hxY'⟩ => ?_
    exact Set.eq_empty_iff_forall_notMem.mp hU (i.base x) ⟨hxU, ⟨x, hxY', rfl⟩⟩)

end AlgebraicGeometry.OModulePresheaf.Descend

open AlgebraicGeometry.OModulePresheaf.Descend in
theorem _root_.AlgebraicGeometry.OModulePresheaf.cechFinite_preimage_of_ih
    {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (K : V.OrderedAffineCover)
    {Z₀ : TopologicalSpace.Closeds V}
    (ih : ∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y'
      → G.CechFinite K)
    (F : OModulePresheaf ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π))
    (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent)
    (Y' : TopologicalSpace.Closeds (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme) (hY' : Y'
      < ⊤)
    (hFs : F.SupportedIn Y') :
    F.CechFinite (K.preimage (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι) := by
  have hrange : Set.range (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base = (Z₀ : Set V)
    :=
    (Scheme.IdealSheafData.range_subschemeι _).trans
      (Scheme.IdealSheafData.coe_support_vanishingIdeal Z₀)
  let Y'' : Closeds V := ⟨(Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base '' Y',
    (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.isClosedEmbedding.isClosedMap _ Y'.2⟩
  have hY''_lt : Y'' < Z₀ := by
    refine lt_of_le_of_ne (fun v ⟨_, _, hvx⟩ => show v ∈ (Z₀ : Set V) from hvx ▸ hrange ▸
      Set.mem_range_self _)
      (fun heq => hY'.ne (SetLike.coe_injective (Set.eq_univ_of_forall fun x => ?_)))
    have hx : (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base x ∈ (Y'' : Set V) :=
      heq.symm ▸ (show (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.base x ∈ (Z₀ : Set V)
        from hrange ▸ Set.mem_range_self x)
    obtain ⟨x', hx', hxx'⟩ := hx
    exact (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι.isClosedEmbedding.injective hxx' ▸
      hx'
  exact (AlgebraicGeometry.OModulePresheaf.cechFinite_pushforward_iff
    (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι F K).mp
    (ih Y'' hY''_lt _ (isCoherent_pushforward π _ F hFc) (isQuasicoherent_pushforward π _ F hFq)
      (supportedIn_pushforward_image π _ F hFs))
end AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_cechFinite_preimage_of_ih
end ProofImplementation
