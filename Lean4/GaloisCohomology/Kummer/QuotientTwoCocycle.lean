import GaloisCohomology.Kummer.RelativeTwoCocycle
import GaloisCohomology.Kummer.MixedTwoCocycle
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.Abel

set_option autoImplicit false

/-!
# Descent of mixed-zero two-cocycles to a quotient group

The descended cocycle takes values in the actual subgroup invariants. Together
with relative normalization, this proves exactness in degree two when subgroup
H¹ vanishes.
-/

open CategoryTheory
open Rep
open groupCohomology

namespace ClassFieldTower.Cohomology

noncomputable section

variable {k G : Type} [CommRing k] [Group G]

private theorem mixedTwoCocycle_second_right
    (A : Rep k G) (S : Subgroup G) (z : cocycles₂ A)
    (hr : ∀ (g : G) (n : S), z (g, (n : G)) = 0)
    (g h : G) (n : S) : z (g, h * (n : G)) = z (g, h) := by
  have hc := (mem_cocycles₂_iff z).mp z.property g h (n : G)
  rw [hr (g * h) n, hr h n, zero_add, map_zero, zero_add] at hc
  exact hc.symm

private theorem mixedTwoCocycle_first_right
    (A : Rep k G) (S : Subgroup G) [S.Normal] (z : cocycles₂ A)
    (hl : ∀ (n : S) (g : G), z ((n : G), g) = 0)
    (hr : ∀ (g : G) (n : S), z (g, (n : G)) = 0)
    (g h : G) (n : S) : z (g * (n : G), h) = z (g, h) := by
  let nh : S := ⟨h⁻¹ * (n : G) * h,
    Subgroup.Normal.conj_mem' inferInstance (n : G) n.property h⟩
  have hnh : h * (nh : G) = (n : G) * h := by
    dsimp only [nh]
    simp only [mul_assoc, mul_inv_cancel_left]
  have hc := (mem_cocycles₂_iff z).mp z.property g (n : G) h
  rw [hr g n, hl n h, add_zero, map_zero, zero_add] at hc
  rw [hc, ← hnh]
  exact mixedTwoCocycle_second_right A S z hr g h nh

private theorem mixedTwoCocycle_invariant
    (A : Rep k G) (S : Subgroup G) [S.Normal] (z : cocycles₂ A)
    (hl : ∀ (n : S) (g : G), z ((n : G), g) = 0)
    (hr : ∀ (g : G) (n : S), z (g, (n : G)) = 0)
    (g h : G) (n : S) : A.ρ (n : G) (z (g, h)) = z (g, h) := by
  let ng : S := ⟨g⁻¹ * (n : G) * g,
    Subgroup.Normal.conj_mem' inferInstance (n : G) n.property g⟩
  have hng : g * (ng : G) = (n : G) * g := by
    dsimp only [ng]
    simp only [mul_assoc, mul_inv_cancel_left]
  have hc := (mem_cocycles₂_iff z).mp z.property (n : G) g h
  rw [hl n g, hl n (g * h), add_zero, add_zero] at hc
  rw [← hc, ← hng]
  exact mixedTwoCocycle_first_right A S z hl hr g h ng

/-- A cocycle vanishing on mixed subgroup arguments descends to quotient
cohomology, with coefficients in the subgroup invariants. -/
theorem exists_quotientTwoCocycle_of_mixed_zero
    (A : Rep k G) (S : Subgroup G) [S.Normal] (z : cocycles₂ A)
    (hl : ∀ (n : S) (g : G), z ((n : G), g) = 0)
    (hr : ∀ (g : G) (n : S), z (g, (n : G)) = 0) :
    ∃ w : cocycles₂ (A.quotientToInvariants S),
      mapCocycles₂ (QuotientGroup.mk' S)
        (ofHom (A.ρ.quotientToInvariants_lift S)) w = z := by
  classical
  let q : G →* G ⧸ S := QuotientGroup.mk' S
  let s : G ⧸ S → G := Function.surjInv (QuotientGroup.mk'_surjective S)
  have hs (x : G ⧸ S) : q (s x) = x := Function.surjInv_eq _ x
  have hcoset {g g' : G} (he : q g = q g') : ∃ n : S, g' = g * (n : G) := by
    let n : S := ⟨g⁻¹ * g', by
      apply (QuotientGroup.eq_one_iff _).mp
      change q (g⁻¹ * g') = 1
      rw [map_mul, map_inv, he, inv_mul_cancel]⟩
    exact ⟨n, (mul_inv_cancel_left g g').symm⟩
  have hfirst {g g' : G} (he : q g = q g') (h : G) : z (g', h) = z (g, h) := by
    obtain ⟨n, rfl⟩ := hcoset he
    exact mixedTwoCocycle_first_right A S z hl hr g h n
  have hsecond {h h' : G} (he : q h = q h') (g : G) : z (g, h') = z (g, h) := by
    obtain ⟨n, rfl⟩ := hcoset he
    exact mixedTwoCocycle_second_right A S z hr g h n
  let f : (G ⧸ S) × (G ⧸ S) → A.quotientToInvariants S := fun xy =>
    ⟨z (s xy.1, s xy.2), fun n => mixedTwoCocycle_invariant A S z hl hr _ _ n⟩
  have hfval (g h : G) : (f (q g, q h) : A) = z (g, h) := by
    change z (s (q g), s (q h)) = z (g, h)
    rw [hfirst (hs (q g)).symm, hsecond (hs (q h)).symm]
  have hf : f ∈ cocycles₂ (A.quotientToInvariants S) := by
    apply (mem_cocycles₂_iff f).mpr
    intro x y t
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective S x
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective S y
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective S t
    apply Subtype.ext
    change (f (q g * q h, q j) : A) + (f (q g, q h) : A) =
      A.ρ g (f (q h, q j) : A) + (f (q g, q h * q j) : A)
    rw [← map_mul q, ← map_mul q, hfval, hfval, hfval, hfval]
    exact (mem_cocycles₂_iff z).mp z.property g h j
  refine ⟨⟨f, hf⟩, ?_⟩
  apply cocycles₂_ext
  intro g h
  change (f (q g, q h) : A) = z (g, h)
  exact hfval g h

/-- The restriction kernel in degree two is the inflation image whenever the
subgroup H¹ vanishes. This constructs the quotient class from a cocycle. -/
theorem degreeTwo_restriction_ker_le_inflation_range
    (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (groupCohomology (res S.subtype A) 1)] :
    (groupCohomology.map S.subtype (𝟙 (res S.subtype A)) 2).hom.ker ≤
      (groupCohomology.map (A := A.quotientToInvariants S) (B := A) (QuotientGroup.mk' S)
        (ofHom (A.ρ.quotientToInvariants_lift S)) 2).hom.range := by
  intro x hx
  induction x using H2_induction_on with
  | h z =>
    obtain ⟨z₀, hclass, hz₀⟩ := exists_relativeTwoCocycle A S z hx
    obtain ⟨B, _, hBl, hBr⟩ := exists_mixedTwoCocycle_correction A S z₀ hz₀
    let dz : cocycles₂ A := ⟨d₁₂ A B, d₁₂_apply_mem_cocycles₂ B⟩
    let z₁ : cocycles₂ A := z₀ - dz
    have hleft (n : S) (g : G) : z₁ ((n : G), g) = 0 := by
      change z₀ ((n : G), g) - d₁₂ A B ((n : G), g) = 0
      rw [hBl, sub_self]
    have hright (g : G) (n : S) : z₁ (g, (n : G)) = 0 := by
      change z₀ (g, (n : G)) - d₁₂ A B (g, (n : G)) = 0
      rw [hBr, sub_self]
    have hz₁ : H2π A z₁ = H2π A z₀ := by
      apply (H2π_eq_iff z₁ z₀).mpr
      refine ⟨-B, ?_⟩
      change (d₁₂ A).hom (-B) = (z₀.val - dz.val) - z₀.val
      rw [map_neg]
      change -(d₁₂ A B) = (z₀.val - d₁₂ A B) - z₀.val
      abel
    obtain ⟨w, hw⟩ := exists_quotientTwoCocycle_of_mixed_zero A S z₁ hleft hright
    refine ⟨H2π (A.quotientToInvariants S) w, ?_⟩
    rw [H2π_comp_map_apply, hw, hz₁, hclass]

end
end ClassFieldTower.Cohomology
