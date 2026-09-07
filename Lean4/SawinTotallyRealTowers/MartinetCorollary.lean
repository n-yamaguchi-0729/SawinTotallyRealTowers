import SawinTotallyRealTowers.SawinTotallyRealTower
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-!
# Martinet's totally real towers as a corollary of Sawin's theorem

Forgetting the splitting conditions in Sawin's theorem gives totally real
number fields of unbounded degree with uniformly bounded root discriminant.
-/

namespace ClassFieldTower.Sawin

/-- Totally real number fields of arbitrarily large degree satisfy a
uniform exponential bound on their absolute discriminants. -/
theorem exists_totallyReal_discr_le :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∃ d : ℕ, N ≤ d ∧
      ∃ (K : Type) (_ : Field K) (_ : NumberField K)
        (_ : NumberField.IsTotallyReal K),
        Module.finrank ℚ K = d ∧
          |(NumberField.discr K : ℝ)| ≤ C ^ d := by
  obtain ⟨rdBound, Q, _hQ, _hprimes, hfields⟩ :=
    sawin_totally_real_tower
  have hC : (0 : ℝ) < max 1 rdBound :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 rdBound)
  refine ⟨max 1 rdBound, hC, ?_⟩
  intro N
  obtain ⟨K, fieldK, _charZeroK, numberFieldK, totallyRealK,
    hN, hroot, _hsplit⟩ := hfields N
  have hdegree : (0 : ℝ) < (Module.finrank ℚ K : ℝ) :=
    Nat.cast_pos.mpr
      (Module.finrank_pos : 0 < Module.finrank ℚ K)
  have hrootC :
      |(NumberField.discr K : ℝ)| ^
          (Module.finrank ℚ K : ℝ)⁻¹ ≤ max 1 rdBound := by
    simpa only [one_div] using
      hroot.trans (le_max_right (1 : ℝ) rdBound)
  have hdiscr :
      |(NumberField.discr K : ℝ)| ≤
        (max 1 rdBound) ^ (Module.finrank ℚ K : ℝ) :=
    (Real.rpow_inv_le_iff_of_pos
      (abs_nonneg (NumberField.discr K : ℝ)) hC.le hdegree).mp hrootC
  refine ⟨Module.finrank ℚ K, hN, K, fieldK,
    numberFieldK, totallyRealK, rfl, ?_⟩
  simpa only [Real.rpow_natCast] using hdiscr

end ClassFieldTower.Sawin
