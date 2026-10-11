/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-!
# Reidemeister Schreier / Discrete / Presentations / Automation

This module defines the small proof automation used in relator calculations:
it closes elementary `RelatorEquivalent` goals and reduces normal-closure
membership goals to the standard closure lemmas.
-/

namespace ReidemeisterSchreier.Discrete.Presentations

/-- Try the standard reusable steps in a relator calculation:

* use an existing hypothesis;
* close reflexive `RelatorEquivalent` goals;
* turn membership in the relator set or its normal closure into
  `RelatorEquivalent _ _ 1`;
* recursively split products, inverses, powers, contexts, and conjugates;
* simplify the definition of `RelatorEquivalent`;
* move to quotient equality and simplify.

This is deliberately general.  It is meant to clear routine endpoints in
longer application proofs, not to encode downstream-specific rewrite rules.
-/
macro "relator_equivalent" : tactic =>
  `(tactic|
    repeat first
    | assumption
    | exact RelatorEquivalent.refl _ _
    | apply RelatorEquivalent.of_mem; assumption
    | apply RelatorEquivalent.of_mem_normalClosure; assumption
    | apply RelatorEquivalent.mul
    | apply RelatorEquivalent.mul_eq_one
    | apply RelatorEquivalent.inv
    | apply RelatorEquivalent.inv_eq_one
    | apply RelatorEquivalent.pow
    | apply RelatorEquivalent.pow_eq_one
    | apply RelatorEquivalent.zpow
    | apply RelatorEquivalent.zpow_eq_one
    | apply RelatorEquivalent.context
    | apply RelatorEquivalent.conj
    | apply RelatorEquivalent.conj_eq_one
    | simp only [RelatorEquivalent]
    | rw [relatorEquivalent_iff_eq_in_presentedQuotient]; simp only)

/-- A more aggressive variant of `relator_equivalent`.

This tactic uses `simp_all`, so it strongly simplifies the local context as well
as the target. -/
macro "relator_equivalent!" : tactic =>
  `(tactic|
    first
    | relator_equivalent
    | simp_all only [RelatorEquivalent]
    | rw [relatorEquivalent_iff_eq_in_presentedQuotient]; simp_all only)

end ReidemeisterSchreier.Discrete.Presentations
