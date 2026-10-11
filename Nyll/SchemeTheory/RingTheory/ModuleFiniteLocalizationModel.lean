/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.LocalizedModule.Submodule
import Mathlib.Basic.Finite.Sigma
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Tactic.Choose


/-!
# A finite submodule agreeing on finitely many principal opens

When a submodule is finitely generated on finitely many principal opens,
choose numerator representatives for all those local generators. Their
finite span is a submodule of the original module and has exactly the same
localizations on the chosen opens. The opens need not cover the whole
spectrum, and the original submodule need not be finitely generated.

This is the affine finite-generator extraction in Stacks, Tag 01PF,
Lemma 28.23.2. That lemma supplies finite-type submodule extension for the
module approximation used by Tags 01PI, 01PJ and 0817. This file proves the
ring-local extraction, not quasicoherent-sheaf extension or gluing.
-/

noncomputable section

universe u v w

namespace Submodule

/-- A finite family of principal localizations which are finitely generated
is recovered by one actual finitely generated submodule of the original.
No covering condition on the chosen principal opens is required. -/
theorem exists_fg_le_localized_eq_finite
    {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
    {ι : Type w} [Finite ι] (r : ι → R) (N : Submodule R M)
    (h : ∀ i : ι, (N.localized (Submonoid.powers (r i))).FG) :
    ∃ K : Submodule R M, K.FG ∧ K ≤ N ∧
      ∀ i : ι, K.localized (Submonoid.powers (r i)) =
        N.localized (Submonoid.powers (r i)) := by
  classical
  choose s hs using h
  have hgen (i : ι) (a : s i) :
      (a : LocalizedModule (Submonoid.powers (r i)) M) ∈
        N.localized (Submonoid.powers (r i)) := by
    rw [← hs i]
    exact Submodule.subset_span a.property
  have hrepr (i : ι) (a : s i) :
      ∃ x : M, x ∈ N ∧ ∃ d : Submonoid.powers (r i),
        IsLocalizedModule.mk'
          (LocalizedModule.mkLinearMap (Submonoid.powers (r i)) M) x d = a := by
    exact (Submodule.mem_localized' (Localization.Away (r i))
      (Submonoid.powers (r i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (r i)) M) N a).mp (hgen i a)
  choose x hx d hd using hrepr
  let K : Submodule R M :=
    Submodule.span R (Set.range (fun a : (Σ i : ι, s i) => x a.1 a.2))
  have hKfg : K.FG := Submodule.fg_span (Set.finite_range _)
  have hKN : K ≤ N := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact hx a.1 a.2
  refine ⟨K, hKfg, hKN, ?_⟩
  intro i
  apply le_antisymm
  · intro z hz
    obtain ⟨m, hm, t, ht⟩ :=
      (Submodule.mem_localized' (Localization.Away (r i))
        (Submonoid.powers (r i))
        (LocalizedModule.mkLinearMap (Submonoid.powers (r i)) M) K z).mp hz
    exact (Submodule.mem_localized' (Localization.Away (r i))
      (Submonoid.powers (r i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (r i)) M) N z).mpr
        ⟨m, hKN hm, t, ht⟩
  · rw [← hs i]
    apply Submodule.span_le.mpr
    intro a ha
    exact (Submodule.mem_localized' (Localization.Away (r i))
      (Submonoid.powers (r i))
      (LocalizedModule.mkLinearMap (Submonoid.powers (r i)) M) K a).mpr
        ⟨x i ⟨a, ha⟩, Submodule.subset_span ⟨⟨i, ⟨a, ha⟩⟩, rfl⟩,
          d i ⟨a, ha⟩, hd i ⟨a, ha⟩⟩

end Submodule
