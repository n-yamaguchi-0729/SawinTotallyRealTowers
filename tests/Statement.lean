import SawinTotallyRealTowers.SawinTotallyRealTower

set_option autoImplicit false

open scoped NumberField
open NumberField IsDedekindDomain

/-- Exact Formal Conjectures target, proved through the public entry point. -/
example :
    ∃ (rdBound : ℝ) (Q : Set ℕ), Q.Infinite ∧ (∀ q ∈ Q, q.Prime ∧ q % 4 = 1) ∧
      ∀ N : ℕ, ∃ (F : Type) (_ : Field F) (_ : CharZero F) (_ : NumberField F)
        (_ : IsTotallyReal F),
        N ≤ Module.finrank ℚ F ∧
        (|(NumberField.discr F : ℝ)|) ^ ((1 : ℝ) / Module.finrank ℚ F) ≤ rdBound ∧
        ∀ q ∈ Q, ∃ (factors : Finset (Ideal (𝓞 F))),
          factors.card = Module.finrank ℚ F ∧
          ∀ p ∈ factors, p.IsMaximal ∧ (q : 𝓞 F) ∈ p :=
  ClassFieldTower.Sawin.sawin_totally_real_tower
