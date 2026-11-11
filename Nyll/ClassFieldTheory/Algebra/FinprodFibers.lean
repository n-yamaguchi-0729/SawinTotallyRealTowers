/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.BigOperators.Finprod

/-!
# Finite products grouped by arbitrary fibers
-/

@[expose] public section

open Function

namespace GlobalClassFieldTheory.Reciprocity

/-- A finitely supported product may be regrouped over the fibers of an
arbitrary indexing map. -/
theorem finprod_fibers_eq_sigma
    {α β G : Type*} [CommMonoid G]
    (g : α → β) (f : α → G)
    (hf : HasFiniteMulSupport f) :
    (∏ᶠ b : β,
        ∏ᶠ x : {x : α // g x = b}, f x.1) =
      ∏ᶠ x : α, f x := by
  classical
  let s := hf.toFinset
  have hFiber (b : β) :
      (∏ᶠ x : {x : α // g x = b}, f x.1) =
        ∏ x ∈ s with g x = b, f x := by
    rw [finprod_eq_prod_of_mulSupport_subset
      (fun x : {x : α // g x = b} => f x.1)
      (s := s.subtype fun x => g x = b)]
    · simp only [Finset.prod_subtype_eq_prod_filter]
    · intro x hx
      change x ∈ s.subtype (fun x => g x = b)
      change f x.1 ≠ 1 at hx
      exact Finset.mem_subtype.mpr (hf.mem_toFinset.2 hx)
  calc
    (∏ᶠ b : β,
        ∏ᶠ x : {x : α // g x = b}, f x.1) =
        ∏ᶠ b : β,
          ∏ x ∈ s with g x = b, f x :=
      finprod_congr hFiber
    _ = ∏ x ∈ s, f x := by
      rw [finprod_eq_prod_of_mulSupport_subset _
        (s.mulSupport_of_fiberwise_prod_subset_image f g)]
      exact
        Finset.prod_fiberwise_of_maps_to
          (t := s.image g)
          (fun x hx => Finset.mem_image_of_mem g hx) f
    _ = ∏ᶠ x : α, f x :=
      (finprod_eq_prod f hf).symm

end GlobalClassFieldTheory.Reciprocity
