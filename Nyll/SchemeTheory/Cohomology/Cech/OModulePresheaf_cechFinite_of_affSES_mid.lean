/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_mid.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.RingTheory.Noetherian.Basic
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheafHom
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_d_comp_d
import Nyll.SchemeTheory.RingTheory.Module_Finite_of_ker_le_range_of_isNoetherianRing

/-!
Cech finiteness of the middle term of an affine short exact sequence from the other two terms.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_cechFinite_of_affSES_mid

open _root_.AlgebraicGeometry
open _root_.CategoryTheory

namespace AlgebraicGeometry
open _root_.AlgebraicGeometry
namespace OModulePresheaf
open _root_.AlgebraicGeometry.OModulePresheaf
namespace LES
open _root_.AlgebraicGeometry.OModulePresheaf
open _root_.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)} [IsSeparated π]
variable (K : V.OrderedAffineCover) {F₁ F₂ F₃ : OModulePresheaf π} (S : AffSES F₁ F₂ F₃)

local notation "ιC" => AffHom.cochainMap (π := π) K S.inc
local notation "πC" => AffHom.cochainMap (π := π) K S.proj

omit [IsSeparated π] in
theorem mem_comap_range_iff {F : OModulePresheaf π} {i : ℕ} (x : LinearMap.ker (F.d K (i + 1))) :
    x ∈ (LinearMap.range (F.d K i)).comap (LinearMap.ker (F.d K (i + 1))).subtype
      ↔ ∃ c, F.d K i c = x.1 := by
  simp only [Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range]

omit [IsSeparated π] in
theorem d_d_apply (F : OModulePresheaf π) (i : ℕ) (c : F.cochain K i) : F.d K (i + 1) (F.d K i c)
    = 0 := by
  have h := LinearMap.congr_fun (F.d_comp_d K i) c
  rwa [LinearMap.comp_apply, LinearMap.zero_apply] at h

theorem cochain_ses (i : ℕ) :
    Function.Injective (ιC i) ∧ Function.Surjective (πC i) ∧ LinearMap.range (ιC i) =
      LinearMap.ker (πC i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f g hfg
    exact funext fun s => S.injective (K.affineInter π s) (congrFun hfg s)
  · intro g
    choose lift hlift using fun s => S.surjective (K.affineInter π s) (g s)
    exact ⟨lift, funext hlift⟩
  · refine le_antisymm ?_ ?_
    · rintro _ ⟨f, rfl⟩
      refine LinearMap.mem_ker.mpr (funext fun s => ?_)
      change S.proj.app (K.affineInter π s) (S.inc.app (K.affineInter π s) (f s)) = 0
      have hzero : S.inc.app (K.affineInter π s) (f s) ∈ LinearMap.ker (S.proj.app (K.affineInter
        π s)) :=
        (S.exact (K.affineInter π s)) ▸ LinearMap.mem_range_self _ (f s)
      exact hzero
    · intro g hg
      have hgs : ∀ s, g s ∈ LinearMap.range (S.inc.app (K.affineInter π s)) := fun s =>
        (S.exact (K.affineInter π s)).symm ▸ LinearMap.mem_ker.mpr (congrFun (LinearMap.mem_ker.mp
          hg) s)
      choose lift hlift using hgs
      exact ⟨lift, funext hlift⟩

theorem ker_kerMap_le_range (i : ℕ) :
    LinearMap.ker (S.proj.kerMap K i) ≤ LinearMap.range (S.inc.kerMap K i) := by
  intro f hf
  have hf0 : f.1 ∈ LinearMap.range (ιC i) :=
    (cochain_ses K S i).2.2 ▸ LinearMap.mem_ker.mpr (congrArg Subtype.val (LinearMap.mem_ker.mp hf))
  obtain ⟨g, hg⟩ := hf0
  have hgc : g ∈ LinearMap.ker (F₁.d K i) :=
    LinearMap.mem_ker.mpr <| (cochain_ses K S (i + 1)).1 <| by
      rw [← LinearMap.comp_apply, AffHom.cochainMap_comp_d, LinearMap.comp_apply, hg,
        LinearMap.mem_ker.mp f.2, map_zero]
  exact ⟨⟨g, hgc⟩, Subtype.ext hg⟩

theorem ker_HSuccMap_le_range (i : ℕ) :
    LinearMap.ker (S.proj.HSuccMap K i) ≤ LinearMap.range (S.inc.HSuccMap K i) := by
  intro z hz
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hπf : ∃ w, F₃.d K i w = (S.proj.kerMap K (i + 1) f).1 := by
    rw [LinearMap.mem_ker, AffHom.HSuccMap_mk] at hz
    exact (mem_comap_range_iff K _).mp ((Submodule.Quotient.mk_eq_zero _).mp hz)
  obtain ⟨w, hw⟩ := hπf
  obtain ⟨w', hw'⟩ := (cochain_ses K S i).2.1 w
  have hdiff : f.1 - F₂.d K i w' ∈ LinearMap.range (ιC (i + 1)) := by
    rw [(cochain_ses K S (i + 1)).2.2]
    refine LinearMap.mem_ker.mpr ?_
    have hchain := LinearMap.congr_fun (AffHom.cochainMap_comp_d K S.proj i) w'
    simp only [LinearMap.comp_apply] at hchain
    rw [map_sub, hchain, hw', hw]
    exact sub_self _
  obtain ⟨g, hg⟩ := hdiff
  have hgc : g ∈ LinearMap.ker (F₁.d K (i + 1)) :=
    LinearMap.mem_ker.mpr <| (cochain_ses K S (i + 2)).1 <| by
      rw [← LinearMap.comp_apply, AffHom.cochainMap_comp_d, LinearMap.comp_apply, hg,
        map_sub, LinearMap.mem_ker.mp f.2, d_d_apply, sub_zero, map_zero]
  refine ⟨Submodule.Quotient.mk ⟨g, hgc⟩, ?_⟩
  rw [AffHom.HSuccMap_mk]
  refine (Submodule.Quotient.eq _).mpr ((mem_comap_range_iff K _).mpr ⟨-w', ?_⟩)
  change F₂.d K i (-w') = ιC (i + 1) g - f.1
  rw [map_neg, hg]; abel

end AlgebraicGeometry.OModulePresheaf.LES

universe u
open _root_.AlgebraicCurves.Cohomology.Cech.Proofs in
open _root_.AlgebraicGeometry OModulePresheaf_cechFinite_of_affSES_mid.AlgebraicGeometry
  _root_.AlgebraicGeometry.OModulePresheaf
  OModulePresheaf_cechFinite_of_affSES_mid.AlgebraicGeometry.OModulePresheaf in
theorem _root_.AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_mid {R : Type u} [CommRing
    R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K :
      V.OrderedAffineCover)
    (h₁ : F₁.CechFinite K) (h₃ : F₃.CechFinite K) : F₂.CechFinite K :=
  ⟨by have := h₁.1; have := h₃.1
      exact Module.Finite.of_ker_le_range_of_isNoetherianRing (S.inc.kerMap K 0) (S.proj.kerMap K 0)
        (LES.ker_kerMap_le_range K S 0),
    fun i => by
      have := h₁.2 i; have := h₃.2 i
      exact Module.Finite.of_ker_le_range_of_isNoetherianRing (S.inc.HSuccMap K i)
        (S.proj.HSuccMap K i)
        (LES.ker_HSuccMap_le_range K S i)⟩
end AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_cechFinite_of_affSES_mid
end ProofImplementation
