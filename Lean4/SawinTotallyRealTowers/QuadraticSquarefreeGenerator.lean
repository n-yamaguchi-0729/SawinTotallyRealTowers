import SawinTotallyRealTowers.QuadraticGenerator
import SawinTotallyRealTowers.RationalSquarefree

set_option autoImplicit false

/-!
# Squarefree integer generators of rational quadratic extensions

Rescaling a rational Kummer generator by a nonzero rational number preserves
the generated field and replaces its square by a signed squarefree integer.
-/

universe u

namespace ClassFieldTower.Sawin

/-- Every quadratic extension of ℚ has a generator whose square is a
nonzero signed squarefree integer, nonsquare in ℚ. -/
theorem exists_squarefree_int_generator_of_isQuadraticExtension
    (L : Type u) [Field L] [Algebra ℚ L]
    [Algebra.IsQuadraticExtension ℚ L] :
    ∃ d : ℤ, ∃ β : L,
      Squarefree d.natAbs ∧ d ≠ 0 ∧
        β ^ 2 = algebraMap ℚ L (d : ℚ) ∧
        IntermediateField.adjoin ℚ ({β} : Set L) = ⊤ ∧
        ¬ IsSquare (d : ℚ) := by
  obtain ⟨q, α, hαSquare, hαAdjoin, hqNonsquare, hq⟩ :=
    exists_nonsquare_rat_generator_of_isQuadraticExtension L
  obtain ⟨d, r, hdSquarefree, hd, hr, hqr⟩ :=
    exists_squarefree_int_mul_sq q hq
  have hmapr : algebraMap ℚ L r ≠ 0 :=
    (_root_.map_ne_zero (algebraMap ℚ L)).mpr hr
  let β : L := α / algebraMap ℚ L r
  have hβSquare : β ^ 2 = algebraMap ℚ L (d : ℚ) := by
    dsimp only [β]
    rw [div_pow, hαSquare, hqr, map_mul, map_pow]
    exact mul_div_cancel_right₀ (algebraMap ℚ L (d : ℚ))
      (pow_ne_zero 2 hmapr)
  have hαRecover : α = β * algebraMap ℚ L r :=
    (div_mul_cancel₀ α hmapr).symm
  have hαMem : α ∈ IntermediateField.adjoin ℚ ({β} : Set L) := by
    rw [hαRecover]
    exact (IntermediateField.adjoin ℚ ({β} : Set L)).mul_mem
      (IntermediateField.mem_adjoin_simple_self ℚ β)
      ((IntermediateField.adjoin ℚ ({β} : Set L)).algebraMap_mem r)
  have hβAdjoin : IntermediateField.adjoin ℚ ({β} : Set L) = ⊤ := by
    apply top_le_iff.mp
    rw [← hαAdjoin]
    apply IntermediateField.adjoin_le_iff.mpr
    intro x hx
    have hxα : x = α := Set.mem_singleton_iff.mp hx
    rw [hxα]
    exact hαMem
  have hdNonsquare : ¬ IsSquare (d : ℚ) := by
    intro hdIsSquare
    apply hqNonsquare
    rw [hqr]
    exact hdIsSquare.mul (IsSquare.sq r)
  exact ⟨d, β, hdSquarefree, hd, hβSquare, hβAdjoin, hdNonsquare⟩

end ClassFieldTower.Sawin
