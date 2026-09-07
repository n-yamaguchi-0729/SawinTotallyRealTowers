import GaloisCohomology.Kummer.RelativeTwoCocycle
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Tactic.Abel

set_option autoImplicit false

/-!
# Killing mixed subgroup entries of a two-cocycle

A vanishing first cohomology group supplies primitives for the conjugation
cocycles of a relative representative. A coset section then turns these
primitives into one global cochain.
-/

open CategoryTheory
open Rep
open groupCohomology

namespace ClassFieldTower.Cohomology

noncomputable section

variable {k G : Type} [CommRing k] [Group G]

private theorem exists_conjugation_primitive
    (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (groupCohomology (res S.subtype A) 1)]
    (z : cocycles₂ A) (hz : ∀ n m : S, z ((n : G), (m : G)) = 0)
    (g : G) : ∃ b : A, ∀ n : S,
      A.ρ (n : G) b - b = z ((n : G), g) - z (g, g⁻¹ * (n : G) * g) := by
  let w : cocycles₁ (res S.subtype A) := relativeTwoCocycleConjugation A S z hz g
  have hw : H1π (res S.subtype A) w = 0 := Subsingleton.elim _ _
  obtain ⟨b, hb⟩ := (H1π_eq_zero_iff w).mp hw
  refine ⟨b, fun n => ?_⟩
  exact congrFun hb n

/-- A relative cocycle admits a global cochain which kills all entries having
at least one argument in the subgroup when the subgroup H¹ vanishes. -/
theorem exists_mixedTwoCocycle_correction
    (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (groupCohomology (res S.subtype A) 1)]
    (z : cocycles₂ A) (hz : ∀ n m : S, z ((n : G), (m : G)) = 0) :
    ∃ B : G → A,
      (∀ n : S, B n = 0) ∧
      (∀ (n : S) (g : G), d₁₂ A B ((n : G), g) = z ((n : G), g)) ∧
      (∀ (g : G) (n : S), d₁₂ A B (g, (n : G)) = z (g, (n : G))) := by
  classical
  let q : G →* G ⧸ S := QuotientGroup.mk' S
  let s : G ⧸ S → G := Function.surjInv (QuotientGroup.mk'_surjective S)
  have hs (x : G ⧸ S) : q (s x) = x := Function.surjInv_eq _ x
  have hsOne : s 1 ∈ S := (QuotientGroup.eq_one_iff (s 1)).mp (hs 1)
  have h11 : z (1, 1) = 0 := hz 1 1
  have hzLeft (g : G) : z (1, g) = 0 :=
    (cocycles₂_map_one_fst z g).trans h11
  have hprim (x : G ⧸ S) : ∃ b : A,
      (x = 1 → b = 0) ∧ ∀ n : S,
      A.ρ (n : G) b - b = z ((n : G), s x) - z (s x, (s x)⁻¹ * (n : G) * s x) := by
    by_cases hx : x = 1
    · subst x
      refine ⟨0, fun _ => rfl, fun n => ?_⟩
      let sn : S := ⟨s 1, hsOne⟩
      let nt : S := ⟨(s 1)⁻¹ * (n : G) * s 1,
        Subgroup.Normal.conj_mem' inferInstance (n : G) n.property (s 1)⟩
      change A.ρ (n : G) 0 - 0 = z ((n : G), (sn : G)) - z ((sn : G), (nt : G))
      rw [map_zero, hz n sn, hz sn nt, sub_self]
    · obtain ⟨b, hb⟩ := exists_conjugation_primitive A S z hz (s x)
      exact ⟨b, fun h => False.elim (hx h), hb⟩
  choose beta hbetaOne hbeta using hprim
  let a : G → S := fun g => ⟨g * (s (q g))⁻¹, by
    apply (QuotientGroup.eq_one_iff _).mp
    change q (g * (s (q g))⁻¹) = 1
    rw [map_mul, map_inv, hs, mul_inv_cancel]⟩
  have ha (g : G) : (a g : G) * s (q g) = g := by
    dsimp only [a]
    rw [inv_mul_cancel_right]
  have hq (n : S) : q n = 1 := (QuotientGroup.eq_one_iff (n : G)).mpr n.property
  have hqLeft (n : S) (g : G) : q ((n : G) * g) = q g := by
    rw [map_mul, hq n, one_mul]
  have haLeft (n : S) (g : G) : a ((n : G) * g) = n * a g := by
    apply Subtype.ext
    change (n : G) * g * (s (q ((n : G) * g)))⁻¹ = (n : G) * (g * (s (q g))⁻¹)
    rw [hqLeft, mul_assoc]
  let B : G → A := fun g => A.ρ (a g : G) (beta (q g)) - z ((a g : G), s (q g))
  have hBzero (n : S) : B n = 0 := by
    dsimp only [B]
    rw [hq n, hbetaOne 1 rfl, map_zero]
    exact sub_eq_zero.mpr (hz (a n) ⟨s 1, hsOne⟩).symm
  have hBleft (n : S) (g : G) :
      B ((n : G) * g) = A.ρ (n : G) (B g) - z ((n : G), g) := by
    have hc := (mem_cocycles₂_iff z).mp z.property (n : G) (a g : G) (s (q g))
    rw [hz n (a g), add_zero, ha] at hc
    dsimp only [B]
    rw [hqLeft, haLeft]
    change A.ρ ((n : G) * (a g : G)) (beta (q g)) - z ((n : G) * (a g : G), s (q g)) = _
    rw [map_mul, Module.End.mul_apply, map_sub, hc]
    abel
  have hBsection (x : G ⧸ S) : B (s x) = beta x := by
    have haS : a (s x) = 1 := by
      apply Subtype.ext
      change s x * (s (q (s x)))⁻¹ = 1
      rw [hs, mul_inv_cancel]
    dsimp only [B]
    rw [hs, haS]
    change A.ρ 1 (beta x) - z (1, s x) = beta x
    rw [map_one, Module.End.one_apply, hzLeft, sub_zero]
  have hBrightSection (x : G ⧸ S) (n : S) :
      B (s x * (n : G)) = beta x - z (s x, (n : G)) := by
    let ns : S := ⟨s x * (n : G) * (s x)⁻¹,
      Subgroup.Normal.conj_mem inferInstance (n : G) n.property (s x)⟩
    have hns : (ns : G) * s x = s x * (n : G) := by
      dsimp only [ns]
      rw [inv_mul_cancel_right]
    have hconj : (s x)⁻¹ * (ns : G) * s x = (n : G) := by
      dsimp only [ns]
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
    have hp := hbeta x ns
    rw [hconj] at hp
    rw [← hns, hBleft, hBsection]
    exact (sub_eq_sub_iff_sub_eq_sub).mp hp
  have hBright (g : G) (n : S) : B (g * (n : G)) = B g - z (g, (n : G)) := by
    have hc := (mem_cocycles₂_iff z).mp z.property (a g : G) (s (q g)) (n : G)
    rw [ha] at hc
    calc
      B (g * (n : G)) = B ((a g : G) * (s (q g) * (n : G))) := by rw [← mul_assoc, ha]
      _ = A.ρ (a g : G) (B (s (q g) * (n : G))) - z ((a g : G), s (q g) * (n : G)) := hBleft (a g) _
      _ = A.ρ (a g : G) (beta (q g) - z (s (q g), (n : G))) -
          z ((a g : G), s (q g) * (n : G)) := by rw [hBrightSection]
      _ = B g - z (g, (n : G)) := by
        dsimp only [B]
        rw [map_sub]
        rw [eq_sub_of_add_eq' hc.symm]
        abel
  refine ⟨B, hBzero, ?_, ?_⟩
  · intro n g
    change A.ρ (n : G) (B g) - B ((n : G) * g) + B n = z ((n : G), g)
    rw [hBleft, hBzero]
    abel
  · intro g n
    change A.ρ g (B n) - B (g * (n : G)) + B g = z (g, (n : G))
    rw [hBzero, map_zero, hBright]
    abel

end
end ClassFieldTower.Cohomology
