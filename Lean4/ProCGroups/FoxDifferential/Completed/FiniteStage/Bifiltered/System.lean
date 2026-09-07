import ProCGroups.FoxDifferential.Completed.FiniteStage.Bifiltered.Transition

set_option autoImplicit false

/-!
# Fox differential: completed — finite stage — bifiltered — system

The principal declarations in this module are:

- `foxAlgebraicStageTargetQuotientMap_rfl`
  The target quotient map induced by the identity subgroup refinement is the identity.
- `foxAlgebraicStageTargetGroupAlgebraMap_rfl`
  The target group-algebra map induced by the identity subgroup refinement is the identity.
- `foxAlgebraicStageBifilteredSemidirectMap_rfl`
  The bifiltered transition along identity target refinement and identity coefficient reduction is
  the identity semidirect map.
- `foxAlgebraicStageBifilteredTargetGroupAlgebraMap_comp`
  Two successive bifiltered target group-algebra maps agree with the map for the composite stage
  refinement.
-/

namespace FoxDifferential

noncomputable section

open ProCGroups.InverseSystems
open ProCGroups.ProC

universe u

variable {X : Type u} [DecidableEq X]

section Identity

variable {N : Subgroup (FreeGroup X)} [N.Normal]
variable {n : ℕ} [Fact (0 < n)]

omit [DecidableEq X] in
/-- The target quotient map induced by the identity subgroup refinement is the identity. -/
@[simp]
theorem foxAlgebraicStageTargetQuotientMap_rfl :
    foxAlgebraicStageTargetQuotientMap (X := X) (N := N) (M := N) (le_rfl : N ≤ N) =
      MonoidHom.id (foxAlgebraicStageTargetQuotient (X := X) N) := by
  apply MonoidHom.ext
  intro q
  rcases QuotientGroup.mk'_surjective N q with ⟨w, hw⟩
  rw [← hw, foxAlgebraicStageTargetQuotientMap_mk]
  rfl

omit [DecidableEq X] [Fact (0 < n)] in
/-- The target group-algebra map induced by the identity subgroup refinement is the identity. -/
@[simp]
theorem foxAlgebraicStageTargetGroupAlgebraMap_rfl :
    foxAlgebraicStageTargetGroupAlgebraMap (X := X) (N := N) (M := N) (le_rfl : N ≤ N) n =
      RingHom.id (foxAlgebraicStageTargetGroupAlgebra (X := X) N n) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      foxAlgebraicStageTargetGroupAlgebraMap (X := X) (N := N) (M := N) (le_rfl : N ≤ N) n x =
        x)
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective N q with ⟨w, hw⟩
    rw [← hw, foxAlgebraicStageTargetGroupAlgebraMap_of]
  · intro x y hx hy
    simp only [map_add, hx, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, hx]
    simp only [map_intCast]

omit [DecidableEq X] [Fact (0 < n)] in
/--
The bifiltered transition along identity target refinement and identity coefficient reduction is
the identity semidirect map.
-/
@[simp]
theorem foxAlgebraicStageBifilteredSemidirectMap_rfl :
    foxAlgebraicStageBifilteredSemidirectMap
        (X := X) (N := N) (M := N) (n := n) (m := n) (le_rfl : N ≤ N) dvd_rfl =
      MonoidHom.id (FoxAlgebraicStageSemidirect (X := X) N n) := by
  apply MonoidHom.ext
  intro y
  apply FoxAlgebraicStageSemidirect.ext
  · funext i
    change foxAlgebraicStageBifilteredTargetGroupAlgebraMap
        (X := X) (N := N) (M := N) (n := n) (m := n) (le_rfl : N ≤ N) dvd_rfl
        (y.left i) = y.left i
    rw [foxAlgebraicStageBifilteredTargetGroupAlgebraMap_apply,
      foxAlgebraicStageTargetGroupAlgebraCoeffMap_rfl]
    exact congrArg (fun f => f (y.left i)) foxAlgebraicStageTargetGroupAlgebraMap_rfl
  · change foxAlgebraicStageTargetQuotientMap (X := X) (N := N) (M := N)
        (le_rfl : N ≤ N) y.right = y.right
    exact congrArg (fun f => f y.right) foxAlgebraicStageTargetQuotientMap_rfl

end Identity

section Composition

variable {N₀ N₁ N₂ : Subgroup (FreeGroup X)}
variable [N₀.Normal] [N₁.Normal] [N₂.Normal]
variable (h₀₁ : N₀ ≤ N₁) (h₁₂ : N₁ ≤ N₂)
variable {n₀ n₁ n₂ : ℕ} [Fact (0 < n₀)] [Fact (0 < n₁)] [Fact (0 < n₂)]
variable (h₀₁n : n₀ ∣ n₁) (h₁₂n : n₁ ∣ n₂)

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < n₁)] [Fact (0 < n₂)] in
/--
Two successive bifiltered target group-algebra maps agree with the map for the composite stage
refinement.
-/
@[simp 900]
theorem foxAlgebraicStageBifilteredTargetGroupAlgebraMap_comp :
    (foxAlgebraicStageBifilteredTargetGroupAlgebraMap
        (X := X) (N := N₁) (M := N₂) h₁₂ h₀₁n).comp
      (foxAlgebraicStageBifilteredTargetGroupAlgebraMap
        (X := X) (N := N₀) (M := N₁) h₀₁ h₁₂n) =
    foxAlgebraicStageBifilteredTargetGroupAlgebraMap
      (X := X) (N := N₀) (M := N₂) (le_trans h₀₁ h₁₂) (dvd_trans h₀₁n h₁₂n) := by
  apply RingHom.ext
  intro x
  refine MonoidAlgebra.induction_on
    (motive := fun x =>
      ((foxAlgebraicStageBifilteredTargetGroupAlgebraMap
          (X := X) (N := N₁) (M := N₂) h₁₂ h₀₁n).comp
        (foxAlgebraicStageBifilteredTargetGroupAlgebraMap
          (X := X) (N := N₀) (M := N₁) h₀₁ h₁₂n)) x =
      foxAlgebraicStageBifilteredTargetGroupAlgebraMap
        (X := X) (N := N₀) (M := N₂) (le_trans h₀₁ h₁₂) (dvd_trans h₀₁n h₁₂n) x)
    x ?_ ?_ ?_
  · intro q
    rcases QuotientGroup.mk'_surjective N₀ q with ⟨w, rfl⟩
    rw [RingHom.comp_apply, foxAlgebraicStageBifilteredTargetGroupAlgebraMap_of,
      foxAlgebraicStageBifilteredTargetGroupAlgebraMap_of,
      foxAlgebraicStageBifilteredTargetGroupAlgebraMap_of]
  · intro x y hx hy
    simp only [map_add, hx, foxAlgebraicStageBifilteredTargetGroupAlgebraMap_apply, hy]
  · intro a x hx
    rcases ZMod.intCast_surjective a with ⟨t, rfl⟩
    rw [Algebra.smul_def, RingHom.map_mul, RingHom.map_mul, hx]
    simp only [foxAlgebraicStageBifilteredTargetGroupAlgebraMap, map_intCast, RingHom.coe_comp,
        Function.comp_apply]

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < n₁)] [Fact (0 < n₂)] in
/-- Bifiltered coordinate-vector transitions compose pointwise. -/
theorem foxAlgebraicStageBifilteredCoordinateVectorMap_comp
    (v : foxAlgebraicStageCoordinateVector (X := X) N₀ n₂) :
    foxAlgebraicStageBifilteredCoordinateVectorMap
        (X := X) (N := N₁) (M := N₂) h₁₂ h₀₁n
        (foxAlgebraicStageBifilteredCoordinateVectorMap
          (X := X) (N := N₀) (M := N₁) h₀₁ h₁₂n v) =
      foxAlgebraicStageBifilteredCoordinateVectorMap
        (X := X) (N := N₀) (M := N₂) (le_trans h₀₁ h₁₂) (dvd_trans h₀₁n h₁₂n) v := by
  funext i
  change
    foxAlgebraicStageBifilteredTargetGroupAlgebraMap
        (X := X) (N := N₁) (M := N₂) h₁₂ h₀₁n
      (foxAlgebraicStageBifilteredTargetGroupAlgebraMap
        (X := X) (N := N₀) (M := N₁) h₀₁ h₁₂n (v i)) =
    foxAlgebraicStageBifilteredTargetGroupAlgebraMap
      (X := X) (N := N₀) (M := N₂) (le_trans h₀₁ h₁₂) (dvd_trans h₀₁n h₁₂n) (v i)
  exact congrArg (fun f => f (v i))
    (foxAlgebraicStageBifilteredTargetGroupAlgebraMap_comp
      (X := X) h₀₁ h₁₂ h₀₁n h₁₂n)

omit [DecidableEq X] [Fact (0 < n₀)] [Fact (0 < n₁)] [Fact (0 < n₂)] in
/-- Bifiltered semidirect transitions compose. -/
@[simp 900]
theorem foxAlgebraicStageBifilteredSemidirectMap_comp :
    (foxAlgebraicStageBifilteredSemidirectMap
        (X := X) (N := N₁) (M := N₂) h₁₂ h₀₁n).comp
      (foxAlgebraicStageBifilteredSemidirectMap
        (X := X) (N := N₀) (M := N₁) h₀₁ h₁₂n) =
    foxAlgebraicStageBifilteredSemidirectMap
      (X := X) (N := N₀) (M := N₂) (le_trans h₀₁ h₁₂) (dvd_trans h₀₁n h₁₂n) := by
  apply MonoidHom.ext
  intro y
  apply FoxAlgebraicStageSemidirect.ext
  · change
      foxAlgebraicStageBifilteredCoordinateVectorMap
          (X := X) (N := N₁) (M := N₂) h₁₂ h₀₁n
          (foxAlgebraicStageBifilteredCoordinateVectorMap
            (X := X) (N := N₀) (M := N₁) h₀₁ h₁₂n y.left) =
        foxAlgebraicStageBifilteredCoordinateVectorMap
          (X := X) (N := N₀) (M := N₂) (le_trans h₀₁ h₁₂)
          (dvd_trans h₀₁n h₁₂n) y.left
    exact foxAlgebraicStageBifilteredCoordinateVectorMap_comp
      (X := X) h₀₁ h₁₂ h₀₁n h₁₂n y.left
  · change
      foxAlgebraicStageTargetQuotientMap (X := X) h₁₂
        (foxAlgebraicStageTargetQuotientMap (X := X) h₀₁ y.right) =
      foxAlgebraicStageTargetQuotientMap (X := X) (le_trans h₀₁ h₁₂) y.right
    rcases QuotientGroup.mk'_surjective N₀ y.right with ⟨w, hw⟩
    rw [← hw]
    rw [foxAlgebraicStageTargetQuotientMap_mk, foxAlgebraicStageTargetQuotientMap_mk,
      foxAlgebraicStageTargetQuotientMap_mk]

end Composition

end

end FoxDifferential
