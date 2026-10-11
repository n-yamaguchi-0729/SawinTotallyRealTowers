/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.End
import Mathlib.Algebra.Group.Commute.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card

/-!
# Products over finite automorphism orbits

The product of all translates is fixed by the acting finite group. If a
commuting automorphism changes the original element by a fixed factor, it
changes the orbit product by that factor raised to the group's cardinality.
-/

namespace GroupTheory

open scoped BigOperators

/-- The product of all translates, indexed by the acting finite monoid. -/
def finiteOrbitProduct {G A : Type*} [Monoid G] [Fintype G] [CommMonoid A]
    (ρ : G →* MulAut A) (C : A) : A :=
  ∏ g : G, ρ g C

/-- Reindexing by left multiplication makes the orbit product invariant. -/
theorem finiteOrbitProduct_invariant
    {G A : Type*} [Group G] [Fintype G] [CommMonoid A]
    (ρ : G →* MulAut A) (C : A) (g : G) :
    ρ g (finiteOrbitProduct ρ C) = finiteOrbitProduct ρ C := by
  change ρ g (∏ h : G, ρ h C) = ∏ h : G, ρ h C
  rw [map_prod]
  calc
    (∏ h : G, ρ g (ρ h C)) = ∏ h : G, ρ (g * h) C := by
      apply Finset.prod_congr rfl
      intro h _hh
      rw [map_mul, MulAut.mul_apply]
    _ = ∏ h : G, ρ h C := Equiv.prod_comp (Equiv.mulLeft g) (fun h : G => ρ h C)

/-- A fixed multiplicative difference accumulates once for each translate. -/
theorem finiteOrbitProduct_map_div
    {G A : Type*} [Monoid G] [Fintype G] [CommGroup A]
    (ρ : G →* MulAut A) (α : MulAut A) (C D : A)
    (hcomm : ∀ g : G, Commute α (ρ g))
    (hdiff : α C / C = D) (hD : ∀ g : G, ρ g D = D) :
    α (finiteOrbitProduct ρ C) / finiteOrbitProduct ρ C = D ^ Fintype.card G := by
  have hfactor (g : G) : α (ρ g C) / ρ g C = D := by
    have hcomm_apply : α (ρ g C) = ρ g (α C) :=
      DFunLike.congr_fun (hcomm g).eq C
    rw [hcomm_apply, ← map_div, hdiff, hD g]
  change α (∏ g : G, ρ g C) / (∏ g : G, ρ g C) = D ^ Fintype.card G
  rw [map_prod, ← Finset.prod_div_distrib]
  exact Finset.prod_eq_pow_card (fun g _hg => hfactor g)

end GroupTheory
