/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPowQuot.lean
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
Quasicoherence of quotients of a quasicoherent module presheaf by ideal powers.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_isQuasicoherent_idealPowQuot

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

section Closure

variable {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R))

theorem isQuasicoherent_idealPow (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    (hFq : OModulePresheaf.IsQuasicoherent F) :
    OModulePresheaf.IsQuasicoherent (idealPow π I F k) := fun U f => by
  let := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule; have := F.isScalarTower U.1
  let := (Scheme.TwoAffineOpenCover.algebraOfHom π (V.basicOpen f)).toModule; have :=
    F.isScalarTower (V.basicOpen f)
  let : Algebra Γ(V, U.1) Γ(V, V.basicOpen f) :=
    (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom.toAlgebra
  have := U.2.isLocalization_basicOpen f
  have hmap : idealSections I (V.basicOpen f) ^ k
      = (I.ideal U ^ k).map (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom := by
    rw [idealSections_eq_ideal (V := V) I ⟨V.basicOpen f, U.2.basicOpen f⟩,
      ← I.map_ideal (U := ⟨V.basicOpen f, U.2.basicOpen f⟩) (V := U) (V.basicOpen_le f),
      Ideal.map_pow]
    rfl
  set ρ := (V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom
  have halg : algebraMap (V.presheaf.obj (Opposite.op (U.1))) (V.presheaf.obj (Opposite.op
    (V.basicOpen f))) = ρ := rfl
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · have hxv : (idealPowSub π I F k (V.basicOpen f)).subtype x
        ∈ (I.ideal U ^ k).map ρ • (⊤ : Submodule Γ(V, V.basicOpen f) (F.obj (V.basicOpen f))) :=
      hmap ▸ x.2
    suffices hsurj : ∀ v : F.obj (V.basicOpen f), v ∈ (I.ideal U ^ k).map ρ • ⊤ →
        ∃ (n : ℕ) (w : F.obj U.1), w ∈ idealPowSub π I F k U.1
          ∧ F.res (V.basicOpen_le f) w = ρ (f ^ n) • v by
      obtain ⟨n, w, hw, hwv⟩ := hsurj _ hxv
      exact ⟨n, ⟨w, hw⟩, Subtype.ext hwv⟩
    intro v hv
    refine Submodule.smul_induction_on hv ?_ ?_
    · intro a ha z _
      obtain ⟨⟨⟨b, hb⟩, ⟨_, m, rfl⟩⟩, habm⟩ :=
        (IsLocalization.mem_map_algebraMap_iff (.powers f) Γ(V, V.basicOpen f)).mp ha
      simp only [halg] at habm
      obtain ⟨n₀, w₀, hw₀⟩ := (hFq U f).1 z
      refine ⟨m + n₀, b • w₀, ?_, ?_⟩
      · rw [idealPowSub, Submodule.restrictScalars_mem,
          idealSections_eq_ideal]
        exact Submodule.smul_mem_smul hb trivial
      · have hρb : ρ b = a * ρ (f ^ m) := habm.symm
        have hscal : ρ b * ρ (f ^ n₀) = ρ (f ^ (m + n₀)) * a := by
          rw [hρb, mul_comm _ a, mul_assoc, ← ρ.map_mul, ← pow_add]
        calc F.res (V.basicOpen_le f) (b • w₀)
            = ρ b • ρ (f ^ n₀) • z := by rw [F.res_smul, hw₀]
          _ = (ρ b * ρ (f ^ n₀)) • z := (mul_smul _ _ z).symm
          _ = (ρ (f ^ (m + n₀)) * a) • z := by rw [hscal]
          _ = ρ (f ^ (m + n₀)) • a • z := mul_smul _ _ z
    · rintro v₁ v₂ ⟨n₁, w₁, hw₁, hv₁⟩ ⟨n₂, w₂, hw₂, hv₂⟩
      refine ⟨max n₁ n₂, f ^ (max n₁ n₂ - n₁) • w₁ + f ^ (max n₁ n₂ - n₂) • w₂,
        add_mem (idealPowSub_smul_mem π I F k U.1 _ _ hw₁)
          (idealPowSub_smul_mem π I F k U.1 _ _ hw₂), ?_⟩
      rw [map_add, F.res_smul, F.res_smul, hv₁, hv₂, smul_add,
        ← mul_smul, ← mul_smul, ← map_mul, ← map_mul,
        ← pow_add, ← pow_add, Nat.sub_add_cancel (le_max_left _ _),
        Nat.sub_add_cancel (le_max_right _ _)]
  · have hy' : F.res (V.basicOpen_le f) ((idealPowSub π I F k U.1).subtype y)
        = 0 := congrArg (idealPowSub π I F k (V.basicOpen f)).subtype hy
    obtain ⟨n, hn⟩ := (hFq U f).2 _ hy'
    exact ⟨n, Subtype.ext hn⟩

theorem isQuasicoherent_idealPowQuot (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ)
    (hFq : OModulePresheaf.IsQuasicoherent F) :
    OModulePresheaf.IsQuasicoherent (idealPowQuot π I F k) := fun U f => by
  let := (Scheme.TwoAffineOpenCover.algebraOfHom π U.1).toModule; have := F.isScalarTower U.1
  have hk := isQuasicoherent_idealPow π I F k hFq U f
  have hk1 := isQuasicoherent_idealPow π I F (k + 1) hFq U f
  set Df : V.affineOpens := ⟨V.basicOpen f, U.2.basicOpen f⟩
  refine ⟨fun x => ?_, fun y hy => ?_⟩
  · obtain ⟨x', rfl⟩ := (idealPowSES π I F k).surjective Df x
    obtain ⟨n, y', hy'⟩ := hk.1 x'
    refine ⟨n, (idealPowSES π I F k).proj.app U y', ?_⟩
    rw [← LinearMap.comp_apply,
      ← (idealPowSES π I F k).proj.naturality (U := Df) (U' := U)
        (show Df.1 ≤ U.1 from V.basicOpen_le f),
      LinearMap.comp_apply, hy', (idealPowSES π I F k).proj.app_smul]
  · obtain ⟨y', rfl⟩ := (idealPowSES π I F k).surjective U y
    have hcomp0 : ((idealPowSES π I F k).proj.app U).comp
        ((idealPowSES π I F k).inc.app U) = 0 :=
      LinearMap.range_le_ker_iff.mp ((idealPowSES π I F k).exact U).le
    have hy' : (idealPow π I F k).res (V.basicOpen_le f) y'
        ∈ idealPowSuccSub π I F k Df.1 := by
      have hnat := (idealPowSES π I F k).proj.naturality (U := Df) (U' := U)
        (show Df.1 ≤ U.1 from V.basicOpen_le f)
      have hmk0 : (idealPowSuccSub π I F k Df.1).mkQ
          ((idealPow π I F k).res (V.basicOpen_le f) y') = 0 :=
        (LinearMap.congr_fun hnat y').trans (by rw [LinearMap.comp_apply]; exact hy)
      exact (Submodule.Quotient.mk_eq_zero _).mp hmk0
    obtain ⟨n, z, hz⟩ := hk1.1
      ⟨(idealPowSub π I F k Df.1).subtype
        ((idealPow π I F k).res (V.basicOpen_le f) y'), hy'⟩
    have hdiff : (idealPow π I F k).res (V.basicOpen_le f)
          ((idealPowSES π I F k).inc.app U z - f ^ n • y') = 0 := by
      rw [map_sub, (idealPow π I F k).res_smul]
      refine Subtype.ext (sub_eq_zero_of_eq ?_)
      have hnat := (idealPowSES π I F k).inc.naturality (U := Df) (U' := U)
        (show Df.1 ≤ U.1 from V.basicOpen_le f)
      calc (idealPowSub π I F k Df.1).subtype
              ((idealPow π I F k).res _
                ((idealPowSES π I F k).inc.app U z))
          = (idealPowSub π I F k Df.1).subtype
              ((idealPowSES π I F k).inc.app Df
                ((idealPow π I F (k + 1)).res _ z)) :=
            congrArg _ (LinearMap.congr_fun hnat.symm z)
        _ = (idealPowSub π I F (k + 1) Df.1).subtype
              ((idealPow π I F (k + 1)).res _ z) := rfl
        _ = _ := (congrArg _ hz).trans rfl
    obtain ⟨m, hm⟩ := hk.2 _ hdiff
    refine ⟨m + n, ?_⟩
    have hkey : (f ^ (m + n) : Γ(V, U.1)) • y'
        = (idealPowSES π I F k).inc.app U (f ^ m • z)
          - f ^ m • ((idealPowSES π I F k).inc.app U z - f ^ n • y') := by
      rw [smul_sub, (idealPowSES π I F k).inc.app_smul, sub_sub_cancel,
        ← mul_smul, ← pow_add]
    rw [← (idealPowSES π I F k).proj.app_smul, hkey, map_sub,
      ← LinearMap.comp_apply, hcomp0, LinearMap.zero_apply, zero_sub, neg_eq_zero, hm,
      map_zero]

end Closure

end AlgebraicGeometry.OModulePresheaf.G4T

end

universe u

open _root_.AlgebraicCurves.Cohomology.Sheaves.Proofs in
open _root_.AlgebraicGeometry OModulePresheaf_isQuasicoherent_idealPowQuot.AlgebraicGeometry in
theorem _root_.AlgebraicGeometry.OModulePresheaf.isQuasicoherent_idealPowQuot {R : Type u}
    [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (I : V.IdealSheafData) (F :
    OModulePresheaf π) (k : ℕ) (hFq : F.IsQuasicoherent) : (OModulePresheaf.idealPowQuot π I F
    k).IsQuasicoherent :=
  AlgebraicGeometry.OModulePresheaf.G4T.isQuasicoherent_idealPowQuot π I F k hFq
end AlgebraicCurves.Cohomology.Sheaves.Proofs.OModulePresheaf_isQuasicoherent_idealPowQuot
end ProofImplementation
