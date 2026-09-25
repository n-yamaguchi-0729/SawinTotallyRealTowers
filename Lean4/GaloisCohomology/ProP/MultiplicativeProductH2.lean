/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Product
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

set_option autoImplicit false
/-!
# Degree-two vanishing for products of multiplicative representations

Primitives are selected coordinatewise and assembled into an actual
one-cochain. The local vanishing input is supplied by the proved local
integer-unit and archimedean block theorems at the idele application.
-/

noncomputable section

namespace ClassFieldTower.Cohomology

open groupCohomology

variable {G : Type} [Group G]

/-- Vanishing of degree-two cohomology supplies an actual multiplicative
one-cochain primitive. -/
theorem isMulCoboundary₂_of_H2_subsingleton
    {M : Type} [CommGroup M] [MulDistribMulAction G M]
    [Subsingleton (groupCohomology (Rep.ofMulDistribMulAction G M) 2)]
    (f : G × G → M) (hf : IsMulCocycle₂ f) : IsMulCoboundary₂ f := by
  let c := cocyclesOfIsMulCocycle₂ hf
  have hb := (H2π_eq_zero_iff c).1 (Subsingleton.elim _ _)
  exact isMulCoboundary₂_of_mem_coboundaries₂ _ hb

private theorem H2_subsingleton_of_isMulCoboundary₂
    {M : Type} [CommGroup M] [MulDistribMulAction G M]
    (h : ∀ f : G × G → M, IsMulCocycle₂ f → IsMulCoboundary₂ f) :
    Subsingleton (groupCohomology (Rep.ofMulDistribMulAction G M) 2) := by
  suffices hz : ∀ x : groupCohomology (Rep.ofMulDistribMulAction G M) 2, x = 0 from
    ⟨fun x y ↦ (hz x).trans (hz y).symm⟩
  intro x
  induction x using H2_induction_on with
  | h c =>
    apply (H2π_eq_zero_iff c).2
    exact (coboundariesOfIsMulCoboundary₂
      (h _ (isMulCocycle₂_of_mem_cocycles₂ _ c.2))).2

section Pi

variable {ι : Type} (M : ι → Type) [∀ i, CommGroup (M i)]
variable [∀ i, MulDistribMulAction G (M i)]

local instance : MulDistribMulAction G (∀ i, M i) :=
  CyclicCohomology.piMulDistribMulAction G M

/-- Coordinatewise primitives prove degree-two vanishing for a dependent
product, including an infinite product. -/
theorem piMultiplicativeH2_subsingleton
    [∀ i, Subsingleton (groupCohomology (Rep.ofMulDistribMulAction G (M i)) 2)] :
    Subsingleton (groupCohomology (Rep.ofMulDistribMulAction G (∀ i, M i)) 2) := by
  apply H2_subsingleton_of_isMulCoboundary₂
  intro f hf
  have hlocal (i : ι) : IsMulCoboundary₂ (fun gh ↦ f gh i) :=
    isMulCoboundary₂_of_H2_subsingleton _ (fun g h j ↦ congrFun (hf g h j) i)
  choose b hb using hlocal
  exact ⟨fun g i ↦ b i g, fun g h ↦ funext (fun i ↦ hb i g h)⟩

end Pi

/-- Degree-two vanishing is preserved by a binary product. -/
theorem prodMultiplicativeH2_subsingleton
    (M N : Type) [CommGroup M] [CommGroup N]
    [MulDistribMulAction G M] [MulDistribMulAction G N]
    [Subsingleton (groupCohomology (Rep.ofMulDistribMulAction G M) 2)]
    [Subsingleton (groupCohomology (Rep.ofMulDistribMulAction G N) 2)] :
    Subsingleton (groupCohomology (Rep.ofMulDistribMulAction G (M × N)) 2) := by
  apply H2_subsingleton_of_isMulCoboundary₂
  intro f hf
  obtain ⟨b, hb⟩ := isMulCoboundary₂_of_H2_subsingleton (fun gh ↦ (f gh).1)
    (fun g h j ↦ congrArg Prod.fst (hf g h j))
  obtain ⟨c, hc⟩ := isMulCoboundary₂_of_H2_subsingleton (fun gh ↦ (f gh).2)
    (fun g h j ↦ congrArg Prod.snd (hf g h j))
  exact ⟨fun g ↦ (b g, c g), fun g h ↦ Prod.ext (hb g h) (hc g h)⟩

end ClassFieldTower.Cohomology
