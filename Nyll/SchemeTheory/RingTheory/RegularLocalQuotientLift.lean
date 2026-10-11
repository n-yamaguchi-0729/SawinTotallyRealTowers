/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Regular
import Mathlib.RingTheory.LocalRing.RingHom.Basic
import Mathlib.Algebra.Module.SpanRank
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Lifting regularity through a nonzerodivisor quotient

If a Noetherian local ring modulo a nonzerodivisor is regular, then the
original ring is regular. A minimal generating set of the quotient maximal
ideal lifts, together with the nonzerodivisor, to a generating set of the
original maximal ideal. The dimension formula gives the required bound.

This proves the one-element assertion of Stacks Project, Lemma 10.106.7
(tag `00NU`), used for a regular Cartier divisor in Lemma 58.31.3 (`0EYE`).
-/

noncomputable section

open IsLocalRing

namespace SchemeTheory

universe u

private theorem maximalIdeal_spanFinrank_le_quotient_add_one
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) [IsLocalRing (R ⧸ Ideal.span {x})] :
    (maximalIdeal R).spanFinrank ≤
      (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by
  classical
  let S := R ⧸ Ideal.span {x}
  let f : R →+* S := Ideal.Quotient.mk (Ideal.span {x})
  have hf : Function.Surjective f := Ideal.Quotient.mk_surjective
  have : IsLocalHom f := IsLocalHom.of_surjective f hf
  let lift : S → R := Function.surjInv hf
  have hlift (s : S) : f (lift s) = s := Function.surjInv_eq hf s
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (maximalIdeal S).fg_of_isNoetherianRing
  let t : Finset R := insert x (s.image lift)
  let J : Ideal R := Ideal.span (t : Set R)
  have hfx : f x = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton x))
  have himage : f '' (↑(s.image lift) : Set R) = (s : Set S) := by
    ext a
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hb
      rw [hlift]
      exact hc
    · intro ha
      exact ⟨lift a, Finset.mem_image.mpr ⟨a, ha, rfl⟩, hlift a⟩
  have hmap : J.map f = maximalIdeal S := by
    dsimp only [J, t]
    rw [Ideal.map_span, Finset.coe_insert, Set.image_insert_eq, hfx, himage,
      Ideal.span_insert, Ideal.span_singleton_zero, bot_sup_eq]
    exact hspan
  have hker : RingHom.ker f ≤ J := by
    rw [show RingHom.ker f = Ideal.span {x} from Ideal.mk_ker]
    apply Ideal.span_le.mpr
    intro a ha
    have ha' : a = x := Set.mem_singleton_iff.mp ha
    subst a
    exact Ideal.subset_span (Finset.mem_insert_self x (s.image lift))
  have hJ : J = maximalIdeal R := by
    rw [← maximalIdeal_comap f, ← hmap, Ideal.comap_map_of_surjective f hf J]
    exact (sup_eq_left.mpr hker).symm
  rw [← hJ]
  calc
    J.spanFinrank ≤ (t : Set R).ncard :=
      Submodule.spanFinrank_span_le_ncard_of_finite t.finite_toSet
    _ = t.card := Set.ncard_coe_finset t
    _ ≤ (s.image lift).card + 1 := Finset.card_insert_le x (s.image lift)
    _ ≤ s.card + 1 := Nat.add_le_add_right (Finset.card_image_le) 1
    _ = (maximalIdeal S).spanFinrank + 1 := by rw [hcard]

/-- A Noetherian local ring is regular if its quotient by a nonzerodivisor
in the maximal ideal is regular. -/
theorem isRegularLocalRing_of_quotient_span_singleton
    (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hregular : IsSMulRegular R x)
    [IsRegularLocalRing (R ⧸ Ideal.span {x})] : IsRegularLocalRing R := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  rw [← ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim hregular hx,
    ← IsRegularLocalRing.spanFinrank_maximalIdeal]
  exact_mod_cast maximalIdeal_spanFinrank_le_quotient_add_one R x

end SchemeTheory
