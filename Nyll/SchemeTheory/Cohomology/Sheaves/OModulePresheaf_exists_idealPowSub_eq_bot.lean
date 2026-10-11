/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_exists_idealPowSub_eq_bot.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafIdealFiltration

/-!
A sufficiently high ideal power annihilates a coherent module presheaf supported on its vanishing
locus.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_exists_idealPowSub_eq_bot

open _root_.AlgebraicGeometry
open _root_.CategoryTheory
open _root_.TopologicalSpace
open _root_.Opposite

noncomputable section

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
namespace G4T
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

universe u

theorem support_vanishingIdeal {V : Scheme.{u}} (Z : Closeds V) :
    (Scheme.IdealSheafData.vanishingIdeal Z).support = Z :=
  SetLike.coe_injective (Scheme.IdealSheafData.coe_support_vanishingIdeal Z)

section Terminates

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem basicOpen_disjoint_of_mem_vanishingIdeal (Y : Closeds V)
    (U : V.affineOpens) (f : Γ(V, U.1))
    (hf : f ∈ (Scheme.IdealSheafData.vanishingIdeal Y).ideal U) :
    ((V.basicOpen f : V.Opens) : Set V) ∩ Y = ∅ := by
  set iY := (Scheme.IdealSheafData.vanishingIdeal Y).subschemeι
  have hpre : iY ⁻¹ᵁ V.basicOpen f = ⊥ := by
    rw [Scheme.preimage_basicOpen,
      show (iY.app U.1).hom f = 0 from
        (idealSections_eq_ideal (Scheme.IdealSheafData.vanishingIdeal Y) U ▸ hf :
          f ∈ idealSections (Scheme.IdealSheafData.vanishingIdeal Y) U.1),
      Scheme.basicOpen_zero]
  have hrange : Set.range iY.base = (Y : Set V) :=
    (Scheme.IdealSheafData.range_subschemeι _).trans
      (congrArg SetLike.coe (support_vanishingIdeal Y))
  refine Set.eq_empty_of_forall_notMem fun x ⟨hxD, hxY⟩ => ?_
  obtain ⟨z, rfl⟩ := hrange ▸ hxY
  exact (congrArg (z ∈ ·) (congrArg SetLike.coe hpre)).mp hxD

theorem exists_idealPowSub_eq_bot [IsLocallyNoetherian V] (Y : Closeds V)
    (F : OModulePresheaf π) (hFc : OModulePresheaf.IsCoherent F)
    (hFq : OModulePresheaf.IsQuasicoherent F) (hFs : OModulePresheaf.SupportedIn F Y)
    (U : V.affineOpens) :
    ∃ N, idealPowSub π (Scheme.IdealSheafData.vanishingIdeal Y) F N U.1 = ⊥ := by
  let := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule; have := F.isScalarTower U.1
  have := IsLocallyNoetherian.component_noetherian U
  set I := Scheme.IdealSheafData.vanishingIdeal Y
  set ann : Ideal Γ(V, U.1) := Module.annihilator Γ(V, U.1) (F.obj U.1)
  have hrad : I.ideal U ≤ ann.radical := fun f hf => by
    have hDdisj := basicOpen_disjoint_of_mem_vanishingIdeal Y U f hf
    have := hFs ⟨V.basicOpen f, U.2.basicOpen f⟩ hDdisj
    have hann : ∀ y : F.obj U.1, ∃ n, (f ^ n : Γ(V, U.1)) • y = 0 :=
      fun y => (hFq U f).2 y (Subsingleton.elim _ _)
    obtain ⟨s, hs⟩ := Module.finite_def.mp (hFc U)
    choose ny hny using fun y : s => hann y
    refine ⟨s.attach.sup ny, Module.mem_annihilator.mpr fun y => ?_⟩
    have hy : y ∈ Submodule.span Γ(V, U.1) s := hs ▸ Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
    · intro z hz
      have hle : ny ⟨z, hz⟩ ≤ s.attach.sup ny := Finset.le_sup (Finset.mem_attach s ⟨z, hz⟩)
      rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hny ⟨z, hz⟩, smul_zero]
    · exact smul_zero _
    · exact fun _ _ _ _ ha hb => by rw [smul_add, ha, hb, add_zero]
    · exact fun c z _ hz => by rw [smul_comm, hz, smul_zero]
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hrad (IsNoetherian.noetherian _)
  refine ⟨N, le_bot_iff.mp fun x hx => ?_⟩
  rw [idealPowSub, Submodule.restrictScalars_mem,
    idealSections_eq_ideal] at hx
  exact Submodule.smul_induction_on hx
    (fun a ha z _ => (Module.mem_annihilator.mp (hN ha) z) ▸ Submodule.zero_mem _)
    (fun _ _ h₁ h₂ => Submodule.add_mem _ h₁ h₂)

end Terminates

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs in
open _root_.AlgebraicGeometry OModulePresheaf_exists_idealPowSub_eq_bot.AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.OModulePresheaf.exists_idealPowSub_eq_bot {R : Type u} [CommRing
    R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsLocallyNoetherian V] (Y :
    TopologicalSpace.Closeds V) (F : OModulePresheaf π) (hFc : F.IsCoherent) (hFq :
    F.IsQuasicoherent) (hFs : F.SupportedIn Y) (U : V.affineOpens) : ∃ N : ℕ,
    OModulePresheaf.idealPowSub π (Scheme.IdealSheafData.vanishingIdeal Y) F N U.1 = ⊥ :=
  AlgebraicGeometry.OModulePresheaf.G4T.exists_idealPowSub_eq_bot π Y F hFc hFq hFs U
end AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_exists_idealPowSub_eq_bot
end ProofImplementation
