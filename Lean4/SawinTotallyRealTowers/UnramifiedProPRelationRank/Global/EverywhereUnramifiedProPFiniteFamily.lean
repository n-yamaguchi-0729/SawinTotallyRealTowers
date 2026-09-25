/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.EverywhereUnramifiedProPCompositum

set_option autoImplicit false
/-!
# Finite families of everywhere-unramified pro-p extensions

For an odd prime `p`, every finite family of bundled finite Galois
everywhere-unramified `p`-extensions has a bundled compositum. Its underlying
field is the finite supremum of the fields in the family.
-/

noncomputable section

universe u v

namespace ClassFieldTower.Martinet
namespace FiniteEverywhereUnramifiedProPExtension

variable {F : Type u} [Field F] [NumberField F]
variable {p : ℕ} [Fact p.Prime]

/-- A finite family of candidates has a candidate whose underlying field is
the finite supremum of the family. -/
theorem exists_finsetSup
    {I : Type v} (hpOdd : Odd p)
    (E : I → FiniteEverywhereUnramifiedProPExtension F p)
    (s : Finset I) :
    ∃ C : FiniteEverywhereUnramifiedProPExtension F p,
      C.field = ⨆ i, ⨆ (_ : i ∈ s), (E i).field := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      exact ⟨bot, by simp [bot]⟩
  | @insert a s ha ih =>
      obtain ⟨C, hC⟩ := ih
      refine ⟨sup hpOdd (E a) C, ?_⟩
      change (E a).field ⊔ C.field =
        ⨆ i, ⨆ (_ : i ∈ insert a s), (E i).field
      rw [hC]
      exact (Finset.iSup_insert a s fun i => (E i).field).symm

/-- A chosen bundled compositum for a finite family of candidates. -/
def finsetSup
    {I : Type v} (hpOdd : Odd p)
    (E : I → FiniteEverywhereUnramifiedProPExtension F p)
    (s : Finset I) :
    FiniteEverywhereUnramifiedProPExtension F p :=
  Classical.choose (exists_finsetSup hpOdd E s)

/-- The underlying field of the chosen finite-family compositum is exactly
the finite supremum. -/
@[simp]
theorem finsetSup_field
    {I : Type v} (hpOdd : Odd p)
    (E : I → FiniteEverywhereUnramifiedProPExtension F p)
    (s : Finset I) :
    (finsetSup hpOdd E s).field =
      ⨆ i, ⨆ (_ : i ∈ s), (E i).field :=
  Classical.choose_spec (exists_finsetSup hpOdd E s)

end FiniteEverywhereUnramifiedProPExtension
end ClassFieldTower.Martinet
