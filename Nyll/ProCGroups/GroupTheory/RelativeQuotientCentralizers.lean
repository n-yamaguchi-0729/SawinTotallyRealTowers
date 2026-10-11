/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ProC.OpenNormalSubgroups.Separation
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Relative fixed points and quotient centralizers

Vanishing relative fixed points and detection of centralizers by open
supergroups force an element centralizing an open subgroup modulo a
quotient kernel to be trivial.
-/

open scoped commutatorElement

namespace ProCGroups
universe u v

/-- An element centralizing an open subgroup modulo a quotient kernel is trivial
when relative fixed points vanish and open supergroups detect centralizers. -/
theorem quotient_eq_one_of_relative_fixedPoints
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {Q : Type v} [Group Q]
    (q : G →* Q) (hq : Function.Surjective q)
    (D : Subgroup G) [D.Normal] (hD : IsClosed (D : Set G))
    (hfaith : ∀ N : OpenNormalSubgroup G, D ≤ (N : Subgroup G) →
      ∀ x : G, q x ∈ Subgroup.centralizer ((N : Subgroup G).map q : Set Q) →
        x ∈ (N : Subgroup G))
    (hfixed : ∀ U : OpenSubgroup G, ∀ x ∈ D,
      q x ∈ Subgroup.centralizer ((U : Subgroup G).map q : Set Q) → q x = 1)
    (U : OpenSubgroup G) (x : G)
    (hx : q x ∈ Subgroup.centralizer ((U : Subgroup G).map q : Set Q)) :
    q x = 1 := by
  let V : OpenNormalSubgroup G := ProC.OpenNormalSubgroup.normalCore U
  have hVU : (V : Subgroup G) ≤ (U : Subgroup G) :=
    ProC.OpenNormalSubgroup.normalCore_le U
  have hxV : q x ∈ Subgroup.centralizer ((V : Subgroup G).map q : Set Q) :=
    Subgroup.centralizer_le (Subgroup.map_mono hVU) hx
  have : ((V : Subgroup G).map q).Normal := Subgroup.Normal.map inferInstance q hq
  let C : Subgroup G :=
    (Subgroup.centralizer ((V : Subgroup G).map q : Set Q)).comap q
  have : C.Normal := inferInstance
  have hxC : x ∈ C := hxV
  have hxDcentral : q x ∈ Subgroup.centralizer (D.map q : Set Q) := by
    apply Subgroup.mem_centralizer_iff_commutator_eq_one'.mpr
    rintro _ ⟨d, hd, rfl⟩
    have hcD : ⁅x, d⁆ ∈ D :=
      Subgroup.commutator_le_right (⊤ : Subgroup G) D
        (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) hd)
    have hcC : ⁅x, d⁆ ∈ C :=
      Subgroup.commutator_le_left C (⊤ : Subgroup G)
        (Subgroup.commutator_mem_commutator hxC (Subgroup.mem_top d))
    have hc := hfixed V.toOpenSubgroup ⁅x, d⁆ hcD hcC
    simpa only [map_commutatorElement] using hc
  have hxD : x ∈ D := by
    by_contra hxD
    obtain ⟨W, hWV, hxW⟩ :=
      ProC.exists_openNormalSubgroup_le_not_mem_sup_closedSubgroup ⟨D, hD⟩ hxD V
    let N := ProC.openNormalSubgroup_sup_normal D W
    apply hxW
    apply hfaith N le_sup_left
    have hDle : D.map q ≤ Subgroup.centralizer ({q x} : Set Q) := by
      intro d hd
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hxDcentral d hd)
    have hWle : (W : Subgroup G).map q ≤ Subgroup.centralizer ({q x} : Set Q) := by
      intro w hw
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (hxV w (Subgroup.map_mono hWV hw))
    intro n hn
    have hn' : n ∈ (D.map q) ⊔ ((W : Subgroup G).map q) := by
      rw [← Subgroup.map_sup]
      exact hn
    exact Subgroup.mem_centralizer_singleton_iff.mp ((sup_le hDle hWle) hn')
  exact hfixed U x hxD hx

end ProCGroups
