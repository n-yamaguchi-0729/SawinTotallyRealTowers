import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Tactic.Abel

set_option autoImplicit false

/-!
# Relative representatives of degree-two cohomology classes

Restriction-zero classes have representatives which vanish pointwise on the
subgroup. Their conjugation defect is an actual degree-one cocycle, the input
for Hilbert 90 in finite Galois descent.
-/

open CategoryTheory
open Rep
open groupCohomology

namespace ClassFieldTower.Cohomology

noncomputable section

variable {k G : Type} [CommRing k] [Group G]

/-- Replace a restriction-zero class by a cohomologous cocycle that vanishes
on both subgroup arguments. No normality is needed for this first step. -/
theorem exists_relativeTwoCocycle
    (A : Rep k G) (S : Subgroup G) (z : cocycles₂ A)
    (hz : groupCohomology.map S.subtype (𝟙 (res S.subtype A)) 2 (H2π A z) = 0) :
    ∃ z' : cocycles₂ A, H2π A z' = H2π A z ∧
      ∀ n m : S, z' ((n : G), (m : G)) = 0 := by
  classical
  have hr : H2π (res S.subtype A)
      (mapCocycles₂ S.subtype (𝟙 (res S.subtype A)) z) = 0 := by
    rw [← H2π_comp_map_apply]
    exact hz
  obtain ⟨b, hb⟩ := (H2π_eq_zero_iff
    (mapCocycles₂ S.subtype (𝟙 (res S.subtype A)) z)).mp hr
  let B : G → A := fun g => if hg : g ∈ S then b ⟨g, hg⟩ else 0
  have hB (n : S) : B n = b n := by
    dsimp only [B]
    rw [dif_pos n.property]
  let dz : cocycles₂ A := ⟨d₁₂ A B, d₁₂_apply_mem_cocycles₂ B⟩
  refine ⟨z - dz, ?_, ?_⟩
  · apply (H2π_eq_iff (z - dz) z).mpr
    refine ⟨-B, ?_⟩
    change (d₁₂ A).hom (-B) = (z.val - dz.val) - z.val
    rw [map_neg]
    change -(d₁₂ A B) = (z.val - d₁₂ A B) - z.val
    abel
  · intro n m
    have hnm := congrFun hb (n, m)
    change (res S.subtype A).ρ n (b m) - b (n * m) + b n =
      z ((n : G), (m : G)) at hnm
    change z ((n : G), (m : G)) -
      (A.ρ (n : G) (B m) - B ((n : G) * (m : G)) + B n) = 0
    rw [hB m, hB n]
    change z ((n : G), (m : G)) -
      ((res S.subtype A).ρ n (b m) - B (n * m : S) + b n) = 0
    rw [hB (n * m), hnm, sub_self]

/-- The defect between the two subgroup coset decompositions is a one-cocycle.
It is the concrete input whose coboundary Hilbert 90 supplies. -/
def relativeTwoCocycleConjugation
    (A : Rep k G) (S : Subgroup G) [S.Normal]
    (z : cocycles₂ A) (hz : ∀ n m : S, z ((n : G), (m : G)) = 0)
    (g : G) : cocycles₁ (res S.subtype A) := by
  refine ⟨fun n => z ((n : G), g) - z (g, g⁻¹ * (n : G) * g), ?_⟩
  apply (mem_cocycles₁_iff _).mpr
  intro n m
  let ng : S := ⟨g⁻¹ * (n : G) * g,
    Subgroup.Normal.conj_mem' inferInstance (n : G) n.property g⟩
  let mg : S := ⟨g⁻¹ * (m : G) * g,
    Subgroup.Normal.conj_mem' inferInstance (m : G) m.property g⟩
  have h1 := (mem_cocycles₂_iff z).mp z.property (n : G) (m : G) g
  have h2 := (mem_cocycles₂_iff z).mp z.property (n : G) g (mg : G)
  have h3 := (mem_cocycles₂_iff z).mp z.property g (ng : G) (mg : G)
  have hng : g * (ng : G) = (n : G) * g := by
    dsimp only [ng]
    rw [mul_assoc, mul_inv_cancel_left]
  have hmg : g * (mg : G) = (m : G) * g := by
    dsimp only [mg]
    rw [mul_assoc, mul_inv_cancel_left]
  have hprod : (ng : G) * (mg : G) = g⁻¹ * ((n : G) * (m : G)) * g := by
    dsimp only [ng, mg]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [hz n m, add_zero] at h1
  rw [hmg] at h2
  rw [hng, hz ng mg, map_zero, zero_add, hprod] at h3
  change z ((n : G) * (m : G), g) - z (g, g⁻¹ * ((n : G) * (m : G)) * g) =
    A.ρ (n : G) (z ((m : G), g) - z (g, (mg : G))) +
      (z ((n : G), g) - z (g, (ng : G)))
  rw [map_sub]
  rw [h1, eq_sub_of_add_eq' h2.symm, ← h3]
  abel

end
end ClassFieldTower.Cohomology
