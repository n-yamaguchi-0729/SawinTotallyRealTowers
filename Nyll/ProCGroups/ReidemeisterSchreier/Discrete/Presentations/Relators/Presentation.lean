/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.ReidemeisterSchreier.Discrete.Presentations.Relators.Operations

/-!
# Conjugated products and presentation endomorphisms

This module expands conjugated list products and promotes generatorwise
normal-closure relations to all words under a free-group endomorphism.
-/

namespace ReidemeisterSchreier.Discrete.Presentations

variable {G H : Type*} [Group G] [Group H]

section NormalClosure

variable {R S : Set G} {r a b : G}

/-- Conjugating a list product is the product of the conjugated entries. -/
theorem conjugate_list_prod {G : Type*} [Group G] (x : G) :
    ∀ l : List G, x * l.prod * x⁻¹ = (l.map fun t => x * t * x⁻¹).prod
  | [] => by
      simp only [List.prod_nil, mul_one, mul_inv_cancel, List.map_nil]
  | t :: ts => by
      rw [List.prod_cons, List.map_cons, List.prod_cons]
      calc
        x * (t * ts.prod) * x⁻¹ = (x * t * x⁻¹) * (x * ts.prod * x⁻¹) := by
          group
        _ = x * t * x⁻¹ * (List.map (fun t => x * t * x⁻¹) ts).prod := by
          rw [conjugate_list_prod x ts]

/-- A rectangular product of conjugated entries is the conjugate of the corresponding
rectangular product. -/
theorem nested_conjugate_list_prod {G : Type*} [Group G]
    (x : G) {p n : ℕ} (f : Fin p → Fin n → G) :
    (List.ofFn (fun b : Fin p =>
      (List.ofFn (fun j : Fin n => x * f b j * x⁻¹)).prod)).prod =
        x * (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin n => f b j)).prod)).prod * x⁻¹ := by
  have hinner :
      (List.ofFn (fun b : Fin p =>
        (List.ofFn (fun j : Fin n => x * f b j * x⁻¹)).prod)) =
          List.ofFn (fun b : Fin p =>
            x * (List.ofFn (fun j : Fin n => f b j)).prod * x⁻¹) := by
    apply List.ofFn_inj.2
    funext b
    simpa only [List.map_ofFn, Function.comp_def] using
      (conjugate_list_prod x (List.ofFn (fun j : Fin n => f b j))).symm
  rw [hinner]
  simpa only [List.map_ofFn, Function.comp_def] using
    (conjugate_list_prod x
      (List.ofFn (fun b : Fin p =>
        (List.ofFn (fun j : Fin n => f b j)).prod))).symm

/-- The value of a subgroup list product is the product of the underlying subgroup elements. -/
theorem subgroup_list_prod_val {G : Type*} [Group G]
    {H : Subgroup G} {n : ℕ} (f : Fin n → H) :
    (((List.ofFn f).prod : H) : G) =
      (List.ofFn (fun i : Fin n => ((f i : H) : G))).prod := by
  change H.subtype ((List.ofFn f).prod) =
    (List.ofFn (fun i : Fin n => ((f i : H) : G))).prod
  rw [map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply List.ofFn_inj.2
  funext i
  rfl

/--
The subgroup nested list product underlying value is evaluated by the displayed coordinate or
generator-level formula in the Reidemeister--Schreier rewriting system.
-/
theorem subgroup_nested_list_prod_val {G : Type*} [Group G]
    {H : Subgroup G} {p n : ℕ} (f : Fin p → Fin n → H) :
    (((List.ofFn (fun b : Fin p =>
      (List.ofFn (fun j : Fin n => f b j)).prod)).prod : H) : G) =
        (List.ofFn (fun b : Fin p =>
          (List.ofFn (fun j : Fin n => ((f b j : H) : G))).prod)).prod := by
  change H.subtype
      ((List.ofFn (fun b : Fin p =>
        (List.ofFn (fun j : Fin n => f b j)).prod)).prod) =
    (List.ofFn (fun b : Fin p =>
      (List.ofFn (fun j : Fin n => ((f b j : H) : G))).prod)).prod
  rw [map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply List.ofFn_inj.2
  funext b
  exact subgroup_list_prod_val (fun j : Fin n => f b j)



/--
If an endomorphism is congruent to the identity on generators modulo a normal closure, then it
is congruent to the identity on every free-group word.
-/
theorem freeGroup_endomorph_mul_inv_mem_normalClosure_of_generator_mul_inv
    {Y : Type*} (R : Set (FreeGroup Y)) (F : FreeGroup Y →* FreeGroup Y)
    (hgen :
      ∀ y : Y,
        F (FreeGroup.of y) * (FreeGroup.of y)⁻¹ ∈ Subgroup.normalClosure R) :
    ∀ w : FreeGroup Y, F w * w⁻¹ ∈ Subgroup.normalClosure R := by
  classical
  let N : Subgroup (FreeGroup Y) := Subgroup.normalClosure R
  let q : FreeGroup Y →* FreeGroup Y ⧸ N := QuotientGroup.mk' N
  have hq : q.comp F = q := by
    apply FreeGroup.ext_hom
    intro y
    change q (F (FreeGroup.of y)) = q (FreeGroup.of y)
    exact
      (QuotientGroup.eq_iff_div_mem
        (N := N) (x := F (FreeGroup.of y)) (y := FreeGroup.of y)).2
        (by simpa [N, div_eq_mul_inv] using hgen y)
  intro w
  have hw :
      q (F w) = q w := by
    simpa using congrArg (fun ψ : FreeGroup Y →* FreeGroup Y ⧸ N => ψ w) hq
  exact
    (QuotientGroup.eq_iff_div_mem (N := N) (x := F w) (y := w)).1
      (by
        change q (F w) = q w
        exact hw)


end NormalClosure

end ReidemeisterSchreier.Discrete.Presentations
