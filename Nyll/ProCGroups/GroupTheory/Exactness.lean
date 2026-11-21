/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Group.Equiv.Basic

/-! # Transport of multiplicative exact sequences -/

@[expose] public section

namespace Function

/-- Exactness is preserved by equivalences of the middle and target monoids. -/
theorem mulExact_transport_mulEquiv
    {A B C B' C' : Type*}
    [Monoid A] [Monoid B] [Monoid C] [Monoid B'] [Monoid C']
    (f : A →* B) (g : B →* C)
    (eB : B ≃* B') (eC : C ≃* C')
    (h : Function.MulExact f g) :
    Function.MulExact
      (eB.toMonoidHom.comp f)
      (eC.toMonoidHom.comp (g.comp eB.symm.toMonoidHom)) := by
  intro y
  change
    eC (g (eB.symm y)) = 1 ↔
      ∃ x, eB (f x) = y
  constructor
  · intro hy
    have hy' : g (eB.symm y) = 1 :=
      eC.map_eq_one_iff.mp hy
    obtain ⟨x, hx⟩ := (h (eB.symm y)).mp hy'
    refine ⟨x, ?_⟩
    simpa only [eB.apply_symm_apply] using congrArg eB hx
  · rintro ⟨x, hx⟩
    apply eC.map_eq_one_iff.mpr
    apply (h (eB.symm y)).mpr
    refine ⟨x, ?_⟩
    apply eB.injective
    simpa only [eB.apply_symm_apply] using hx

end Function
