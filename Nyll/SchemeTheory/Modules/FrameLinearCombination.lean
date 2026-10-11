/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_exists_frame_of_frame_sum_smul.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.BigOperators
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Tactic.Push

/-!
# Scheme Modules exists frame of frame sum smul
-/

section ProofImplementation

namespace AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_frame_of_frame_sum_smul

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace FrameSumSol

variable {X : Scheme.{u}} (M : X.Modules)

/-- Restrict a global section of `M` to the open subset `W`. -/
noncomputable abbrev res (m : Γ(M, ⊤)) (W : X.Opens) : Γ(M, W) := M.presheaf.map (homOfLE (le_top :
  W ≤ ⊤)).op m

theorem res_map (m : Γ(M, ⊤)) {W W' : X.Opens} (i : W' ⟶ W) : M.presheaf.map i.op (res M m W) = res
  M m W' := by
  simp only [res, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

theorem smul_res (m : Γ(M, ⊤)) {W W' : X.Opens} (i : W' ⟶ W) (g : Γ(X, W)) :
    M.presheaf.map i.op (g • res M m W) = X.presheaf.map i.op g • res M m W' := by
  rw [Scheme.Modules.map_smul, res_map]

theorem main {ι : Type*} [Fintype ι] (a : ι → Γ(X, ⊤)) (t : ι → Γ(M, ⊤)) (x : X)
    (h : ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • res M (∑ j, a j • t j) V) :
    ∃ (j : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • res M (t j) V := by
  classical
  obtain ⟨U, hxU, hU⟩ := h
  set s : Γ(M, ⊤) := ∑ j, a j • t j with hs
  have hbU := hU U le_rfl
  choose hj hhj using fun j => hbU.2 (res M (t j) U)
  have hhj' : ∀ j, hj j • res M s U = res M (t j) U := hhj
  have hsum : ∑ j, X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (a j) * hj j = 1 := by
    apply hbU.1
    change (∑ j, X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (a j) * hj j) • res M s U = (1 : Γ(X,
      U)) • res M s U
    rw [one_smul, Finset.sum_smul]
    simp_rw [mul_smul, hhj']
    rw [hs]
    simp only [res, map_sum, Scheme.Modules.map_smul]
  obtain ⟨j, hju⟩ : ∃ j, IsUnit (X.presheaf.germ U x hxU (hj j)) := by
    by_contra hcon
    push Not at hcon
    have h1 : X.presheaf.germ U x hxU (∑ j, X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op (a j) * hj
      j) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
      rw [map_sum]
      refine Ideal.sum_mem _ fun j _ => ?_
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ ((IsLocalRing.mem_maximalIdeal _).2 (hcon j))
    rw [hsum, map_one] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)
  refine ⟨j, X.basicOpen (hj j), (X.mem_basicOpen (hj j) x hxU).2 hju, fun V hV => ?_⟩
  have hVU : V ≤ U := hV.trans (X.basicOpen_le _)
  have hu : IsUnit (X.presheaf.map (homOfLE hVU).op (hj j)) := by
    have h0 := RingedSpace.isUnit_res_basicOpen (X := X.toLocallyRingedSpace.toSheafedSpace) (hj j)
    have hcomp : X.presheaf.map (homOfLE hVU).op (hj j) =
        X.presheaf.map (homOfLE hV).op (X.presheaf.map (homOfLE (X.basicOpen_le (hj j))).op (hj j))
          := by
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
      rfl
    rw [hcomp]
    exact h0.map (CommRingCat.Hom.hom (X.presheaf.map (homOfLE hV).op))
  have htV : res M (t j) V = X.presheaf.map (homOfLE hVU).op (hj j) • res M s V := by
    rw [← smul_res M s (homOfLE hVU) (hj j), hhj', res_map]
  have hbV := hU V hVU
  have hmul : Function.Bijective fun g : Γ(X, V) => g * X.presheaf.map (homOfLE hVU).op (hj j) := by
    obtain ⟨u', hu'⟩ := hu
    rw [← hu']
    exact (Units.mulRight u').bijective
  have key : (fun g : Γ(X, V) => g • res M (t j) V) =
      (fun g : Γ(X, V) => g • res M s V) ∘ (fun g => g * X.presheaf.map (homOfLE hVU).op (hj j)) :=
        by
    funext g
    simp only [Function.comp_apply, htV, mul_smul]
  rw [key]
  exact hbV.comp hmul

end FrameSumSol

theorem _root_.AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_sum_smul
    {X : Scheme.{u}} (M : X.Modules) {ι : Type*} [Fintype ι] (a : ι → Γ(X, ⊤)) (t : ι → Γ(M, ⊤)) (x
      : X)
    (h : ∃ U : X.Opens, x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (∑ j,
        a j • t j) : Γ(M, V))) :
    ∃ (j : ι) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (M.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (t j)
        : Γ(M, V)) :=
  FrameSumSol.main M a t x h
end AlgebraicCurves.Geometry.Sheaves.Proofs.Scheme_Modules_exists_frame_of_frame_sum_smul
end ProofImplementation
