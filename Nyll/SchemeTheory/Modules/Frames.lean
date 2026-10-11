/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesSectionsTensor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! Local frames for scheme modules and their restrictions. -/

universe u

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} {M : X.Modules} {U : X.Opens}

/-- A section is a local frame on an open subset when its restrictions freely generate all smaller
  section modules. -/
def IsFrameOn (s : Γ(M, U)) (V : X.Opens) : Prop :=
  ∀ ⦃W : X.Opens⦄ (hWU : W ≤ U), W ≤ V →
    Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE hWU).op s : Γ(M, W))

namespace IsFrameOn

variable {s : Γ(M, U)} {V : X.Opens}

lemma bijective (h : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) :
    Function.Bijective fun g : Γ(X, W) => g • (M.presheaf.map (homOfLE hWU).op s : Γ(M, W)) :=
  h hWU hWV

lemma mono (h : IsFrameOn s V) {V' : X.Opens} (hV' : V' ≤ V) : IsFrameOn s V' :=
  fun _ hWU hWV' => h hWU (hWV'.trans hV')

lemma of_inf (h : IsFrameOn s (V ⊓ U)) : IsFrameOn s V :=
  fun _ hWU hWV => h hWU (le_inf hWV hWU)

lemma inf_iff : IsFrameOn s (V ⊓ U) ↔ IsFrameOn s V :=
  ⟨of_inf, fun h => h.mono inf_le_left⟩

lemma map (h : IsFrameOn s V) {U' : X.Opens} (i : U' ⟶ U) :
    IsFrameOn (M.presheaf.map i.op s) V := by
  intro W hWU' hWV
  have e : M.presheaf.map (homOfLE hWU').op (M.presheaf.map i.op s) =
      M.presheaf.map (homOfLE (hWU'.trans i.le)).op s := by
    rw [← CategoryTheory.comp_apply, ← M.presheaf.map_comp]
    rfl
  simp only [e]
  exact h (hWU'.trans i.le) hWV

lemma existsUnique (h : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) (x : Γ(M, W)) :
    ∃! g : Γ(X, W), g • M.presheaf.map (homOfLE hWU).op s = x :=
  (Function.bijective_iff_existsUnique _).1 (h hWU hWV) x

lemma smul_eq_zero_iff (h : IsFrameOn s V) {W : X.Opens} (hWU : W ≤ U) (hWV : W ≤ V) (g : Γ(X, W)) :
    g • M.presheaf.map (homOfLE hWU).op s = 0 ↔ g = 0 := by
  constructor
  · intro hg
    apply (h hWU hWV).1
    change g • M.presheaf.map (homOfLE hWU).op s = (0 : Γ(X, W)) • M.presheaf.map (homOfLE hWU).op s
    rw [hg, zero_smul]
  · rintro rfl
    exact zero_smul _ _

end IsFrameOn

lemma IsFrameOn.map_iso {N : X.Modules} {s : Γ(M, U)} {V : X.Opens} (h : IsFrameOn s V) (e : M ≅ N)
  :
    IsFrameOn (e.hom.app U s) V := by
  intro W hWU hWV
  have nat : N.presheaf.map (homOfLE hWU).op (e.hom.app U s) =
      e.hom.app W (M.presheaf.map (homOfLE hWU).op s) := by
    have := (e.hom.mapPresheaf).naturality (homOfLE hWU).op
    exact (congrFun (congrArg (fun f => (ConcreteCategory.hom f : Γ(M, U) → Γ(N, W))) this) s).symm
  simp only [nat]
  have hb : Function.Bijective (e.hom.app W : Γ(M, W) → Γ(N, W)) := by
    refine Function.bijective_iff_has_inverse.2 ⟨e.inv.app W, fun x => ?_, fun y => ?_⟩
    · change (e.hom.app W ≫ e.inv.app W) x = x
      rw [← Scheme.Modules.Hom.comp_app, e.hom_inv_id, Scheme.Modules.Hom.id_app]; rfl
    · change (e.inv.app W ≫ e.hom.app W) y = y
      rw [← Scheme.Modules.Hom.comp_app, e.inv_hom_id, Scheme.Modules.Hom.id_app]; rfl
  have : (fun g : Γ(X, W) => g • e.hom.app W (M.presheaf.map (homOfLE hWU).op s)) =
      (e.hom.app W) ∘ fun g : Γ(X, W) => g • M.presheaf.map (homOfLE hWU).op s := by
    funext g
    simp only [Function.comp_apply, Scheme.Modules.Hom.app_smul]
  rw [this]
  exact hb.comp (h hWU hWV)

end AlgebraicGeometry.Scheme.Modules
