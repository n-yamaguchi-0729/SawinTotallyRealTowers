/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_OModulePresheaf_cechFinite_of_affSES_left.lean
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
import Nyll.SchemeTheory.Cohomology.Sheaves.OModulePresheaf_AffSES_exists_connectingHom

/-!
Cech finiteness of the left term of an affine short exact sequence from the other two terms.
-/

section ProofImplementation

namespace AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_cechFinite_of_affSES_left

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

end AlgebraicGeometry.OModulePresheaf.LES

universe u
open _root_.AlgebraicCurves.Cohomology.Cech.Proofs in
open _root_.AlgebraicGeometry OModulePresheaf_cechFinite_of_affSES_left.AlgebraicGeometry
  _root_.AlgebraicGeometry.OModulePresheaf
  OModulePresheaf_cechFinite_of_affSES_left.AlgebraicGeometry.OModulePresheaf in
theorem _root_.AlgebraicGeometry.OModulePresheaf.cechFinite_of_affSES_left {R : Type u} [CommRing
    R] [IsNoetherianRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
    [IsSeparated π] {F₁ F₂ F₃ : OModulePresheaf π} (S : OModulePresheaf.AffSES F₁ F₂ F₃) (K :
      V.OrderedAffineCover)
    (h₂ : F₂.CechFinite K) (h₃ : F₃.CechFinite K) : F₁.CechFinite K := by
  obtain ⟨δ₀, δ, -, -, h0, hS⟩ := S.exists_connectingHom K
  refine ⟨?_, fun i => ?_⟩
  · have : IsNoetherian R (F₂.H0 K) := haveI := h₂.1; isNoetherian_of_isNoetherianRing_of_finite R _
    exact Module.Finite.of_injective (S.inc.kerMap K 0)
      fun x y h => Subtype.ext ((LES.cochain_ses K S 0).1 (congrArg Subtype.val h))
  · rcases i with _ | j
    · have := h₃.1; have := h₂.2 0
      exact Module.Finite.of_ker_le_range_of_isNoetherianRing δ₀ (S.inc.HSuccMap K 0) h0
    · have := h₃.2 j; have := h₂.2 (j + 1)
      exact Module.Finite.of_ker_le_range_of_isNoetherianRing (δ j) (S.inc.HSuccMap K (j + 1)) (hS
        j)
end AlgebraicCurves.Cohomology.Cech.Proofs.OModulePresheaf_cechFinite_of_affSES_left
end ProofImplementation
