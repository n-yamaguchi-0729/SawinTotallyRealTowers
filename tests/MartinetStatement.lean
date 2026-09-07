import SawinTotallyRealTowers.MartinetCorollary

set_option autoImplicit false

open NumberField

/-- Exact Lean Eval `martinet_totally_real_towers` target, via the public corollary. -/
example :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧ |(NumberField.discr K : ℝ)| ≤ C ^ d :=
  ClassFieldTower.Sawin.exists_totallyReal_discr_le
