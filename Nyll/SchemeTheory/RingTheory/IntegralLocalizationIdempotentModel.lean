/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.IntegralLocalizationFiniteModel
public import Mathlib.Algebra.Group.Idempotent
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic

/-!
# Finite localization models preserving quotient idempotents

Ideal membership uses only finitely many coefficients. Including those
coefficients in a finite subalgebra makes a quotient idempotent descend to that
subalgebra. A finite-type principal localization can also be preserved.
-/


@[expose] public section

universe u v

namespace Algebra

private theorem exists_finite_set_of_mem_map
    {R : Type u} {C : Type v} [CommRing R] [CommRing C] [Algebra R C]
    (I : Ideal R) {x : C} (hx : x ∈ I.map (algebraMap R C)) :
    ∃ T : Set C, T.Finite ∧ ∀ S : Subalgebra R C, T ⊆ S →
      ∃ y : S, (y : C) = x ∧ y ∈ I.map (algebraMap R S) := by
  change x ∈ Submodule.span C ((algebraMap R C) '' (I : Set R)) at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨r, hr, rfl⟩ := hx
    refine ⟨∅, Set.finite_empty, ?_⟩
    intro S _
    exact ⟨algebraMap R S r, rfl, Ideal.mem_map_of_mem (algebraMap R S) hr⟩
  | zero =>
    refine ⟨∅, Set.finite_empty, ?_⟩
    intro S _
    exact ⟨0, rfl, (I.map (algebraMap R S)).zero_mem⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨T, hT, hTx⟩ := ihx
    obtain ⟨U, hU, hUy⟩ := ihy
    refine ⟨T ∪ U, hT.union hU, ?_⟩
    intro S hS
    obtain ⟨xS, hxS, hxI⟩ := hTx S (fun z hz ↦ hS (Or.inl hz))
    obtain ⟨yS, hyS, hyI⟩ := hUy S (fun z hz ↦ hS (Or.inr hz))
    refine ⟨xS + yS, ?_, (I.map (algebraMap R S)).add_mem hxI hyI⟩
    change (xS : C) + (yS : C) = x + y
    rw [hxS, hyS]
  | smul c x _ ih =>
    obtain ⟨T, hT, hTx⟩ := ih
    refine ⟨insert c T, hT.insert c, ?_⟩
    intro S hS
    obtain ⟨xS, hxS, hxI⟩ := hTx S (fun z hz ↦ hS (Set.mem_insert_of_mem c hz))
    let cS : S := ⟨c, hS (Set.mem_insert c T)⟩
    refine ⟨cS * xS, ?_, (I.map (algebraMap R S)).mul_mem_left cS hxI⟩
    change c * (xS : C) = c * x
    rw [hxS]

/-- A quotient idempotent in an integral algebra descends to the quotient of
a finite subalgebra containing its representative. -/
theorem exists_finite_subalgebra_quotient_idempotent
    {R : Type u} {C : Type v} [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.IsIntegral R C] (I : Ideal R) (b : C)
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap R C)) b)) :
    ∃ S : Subalgebra R C, Module.Finite R S ∧ ∃ hbS : b ∈ S,
      IsIdempotentElem
        (Ideal.Quotient.mk (I.map (algebraMap R S)) (⟨b, hbS⟩ : S)) := by
  have hdef : b * b - b ∈ I.map (algebraMap R C) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, sub_eq_zero]
    exact hb.eq
  obtain ⟨T, hT, hcoeff⟩ := exists_finite_set_of_mem_map I hdef
  let S : Subalgebra R C := Algebra.adjoin R (insert b T)
  have hfinite : Module.Finite R S :=
    Algebra.finite_adjoin_of_finite_of_isIntegral (hT.insert b)
      (fun x _ ↦ Algebra.IsIntegral.isIntegral x)
  have hbS : b ∈ S := Algebra.subset_adjoin (Set.mem_insert b T)
  have hTS : T ⊆ S := fun x hx ↦
    Algebra.subset_adjoin (Set.mem_insert_of_mem b hx)
  obtain ⟨xS, hxS, hxI⟩ := hcoeff S hTS
  let bS : S := ⟨b, hbS⟩
  have hdefS : bS * bS - bS ∈ I.map (algebraMap R S) := by
    have heq : bS * bS - bS = xS := Subtype.ext hxS.symm
    rw [heq]
    exact hxI
  refine ⟨S, hfinite, hbS, ?_⟩
  have heq := Ideal.Quotient.eq_zero_iff_mem.mpr hdefS
  rw [map_sub, map_mul, sub_eq_zero] at heq
  exact heq

/-- A quotient idempotent in an integral algebra has a finite subalgebra model
in which it is still idempotent modulo the extended ideal. If localizing at the
element is of finite type, the model has the same principal localization. -/
theorem exists_finite_subalgebra_idempotent_awayMap_bijective
    {R : Type u} {C : Type v} [CommRing R] [CommRing C] [Algebra R C]
    [Algebra.IsIntegral R C] (I : Ideal R) (b : C)
    [Algebra.FiniteType R (Localization.Away b)]
    (hb : IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap R C)) b)) :
    ∃ S : Subalgebra R C, Module.Finite R S ∧ ∃ hbS : b ∈ S,
      IsIdempotentElem
        (Ideal.Quotient.mk (I.map (algebraMap R S)) (⟨b, hbS⟩ : S)) ∧
      Function.Bijective (Localization.awayMap S.val.toRingHom ⟨b, hbS⟩) := by
  have hdef : b * b - b ∈ I.map (algebraMap R C) := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [map_sub, map_mul, sub_eq_zero]
    exact hb.eq
  obtain ⟨T, hT, hcoeff⟩ := exists_finite_set_of_mem_map I hdef
  obtain ⟨S, hfinite, hTS, hbS, hbij⟩ :=
    exists_finite_subalgebra_awayMap_bijective_of_finiteType (R := R) b T hT
  obtain ⟨xS, hxS, hxI⟩ := hcoeff S hTS
  let bS : S := ⟨b, hbS⟩
  have hdefS : bS * bS - bS ∈ I.map (algebraMap R S) := by
    have heq : bS * bS - bS = xS := Subtype.ext hxS.symm
    rw [heq]
    exact hxI
  refine ⟨S, hfinite, hbS, ?_, hbij⟩
  have heq := Ideal.Quotient.eq_zero_iff_mem.mpr hdefS
  rw [map_sub, map_mul, sub_eq_zero] at heq
  exact heq

end Algebra
