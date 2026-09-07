import ProCGroups.FoxDifferential.Completed.CoefficientRings.CompletedGroupAlgebraModN.CoeffMap

set_option autoImplicit false

/-!
# Fox differential: prime-power completed group algebra — basic — stage coeff map — coeff

The principal declarations in this module are:

- `primePower_pos`
  The prime-power moduli used throughout the compatibility layer are positive.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

/-- The prime-power moduli used throughout the compatibility layer are positive. -/
theorem primePower_pos (ℓ a : ℕ) [Fact (0 < ℓ)] : 0 < ℓ ^ a :=
  pow_pos (Fact.out : 0 < ℓ) a

end

end FoxDifferential
