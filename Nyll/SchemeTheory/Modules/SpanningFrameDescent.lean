/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Nyll.SchemeTheory.Modules.Invertible
import Nyll.SchemeTheory.Modules.FrameLinearCombination
import Nyll.SchemeTheory.Modules.FrameDescent
import Nyll.SchemeTheory.Modules.FrameLocality

/-! SpanningFrameDescent for scheme modules. -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules.IsInvertible

/-- A spanning family after a surjective pullback supplies frame opens downstairs. -/
theorem exists_iSup_eq_top_bijective_smul_of_span_pullback_of_surjective
    {X X' : Scheme.{u}} (c : X' ⟶ X) [Surjective c]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) {N : ℕ} (σ : Fin (N + 1) → Γ(L, ⊤))
    (σ' : Fin (N + 1) → Γ((Scheme.Modules.pullback c).obj L, ⊤))
    (hσ' : ∀ l, σ' l = (((Scheme.Modules.pullbackPushforwardAdjunction c).unit.app L).app ⊤) (σ l))
    {M : ℕ} (ρ : Fin (M + 1) → Γ((Scheme.Modules.pullback c).obj L, ⊤))
    (U' : Fin (M + 1) → X'.Opens) (hU' : iSup U' = ⊤)
    (hframe' : ∀ (j : Fin (M + 1)) (V' : X'.Opens), V' ≤ U' j →
      Function.Bijective fun g : Γ(X', V') =>
        g • (((Scheme.Modules.pullback c).obj L).presheaf.map (homOfLE (le_top : V' ≤ ⊤)).op (ρ j) :
          Γ((Scheme.Modules.pullback c).obj L, V')))
    (hspan : ∀ j : Fin (M + 1), ∃ a : Fin (N + 1) → Γ(X', ⊤), ρ j = ∑ l, a l • σ' l) :
    ∃ U : Fin (N + 1) → X.Opens, iSup U = ⊤ ∧
      ∀ (l : Fin (N + 1)) (V : X.Opens), V ≤ U l →
        Function.Bijective fun g : Γ(X, V) => g • (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ
          l) : Γ(L, V)) := by
  classical
  have hpt : ∀ x : X, ∃ (l : Fin (N + 1)) (U : X.Opens), x ∈ U ∧ ∀ V : X.Opens, V ≤ U →
      Function.Bijective fun g : Γ(X, V) => g • (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ l)
        : Γ(L, V)) := by
    intro x
    obtain ⟨x', hx'⟩ := c.surjective x
    have hx'top : x' ∈ (⊤ : X'.Opens) := trivial
    rw [← hU'] at hx'top
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hx'top
    obtain ⟨a, ha⟩ := hspan j
    obtain ⟨l, U'', hxU'', hfr⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_sum_smul ((Scheme.Modules.pullback
        c).obj L) a σ' x'
        ⟨U' j, hj, fun V' hV' => by
          have h := hframe' j V' hV'
          rw [ha] at h
          exact h⟩
    obtain ⟨U, hxU, hU⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_frame_of_frame_pullback c L hL (σ l) x'
        ⟨U'', hxU'', fun V' hV' => by
          have h := hfr V' hV'
          rw [hσ' l] at h
          exact h⟩
    refine ⟨l, U, ?_, hU⟩
    rw [← hx']
    exact hxU
  let good : Fin (N + 1) → Set X.Opens := fun l =>
    {W | ∀ V : X.Opens, V ≤ W →
      Function.Bijective fun g : Γ(X, V) => g • (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op (σ l)
        : Γ(L, V))}
  refine ⟨fun l => sSup (good l), ?_, ?_⟩
  · refine le_antisymm le_top fun x _ => ?_
    obtain ⟨l, U, hxU, hU⟩ := hpt x
    have hle : U ≤ sSup (good l) := le_sSup (show U ∈ good l from hU)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨l, hle hxU⟩
  · intro l V hV
    apply AlgebraicGeometry.Scheme.Modules.bijective_smul_of_forall_exists_bijective_smul L (σ l) V
    intro x hx
    obtain ⟨W, hW, hxW⟩ := TopologicalSpace.Opens.mem_sSup.mp (hV hx)
    exact ⟨W, hxW, hW⟩

end AlgebraicGeometry.Scheme.Modules.IsInvertible
