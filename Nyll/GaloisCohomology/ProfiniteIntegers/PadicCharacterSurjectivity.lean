/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProfiniteIntegers.PadicInverseLimit
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-! # Surjectivity of p-adic characters detected modulo p -/

namespace PadicInt
universe u
variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [CompactSpace G]

/-- A compact-group character in the additive p-adic integers is surjective
when its reduction modulo p is nonzero. Its closed image contains the dense
integer multiples of a p-adic unit. -/
theorem surjective_character_of_nonzero_reduction
    (χ : G →ₜ* Multiplicative (PadicInt p))
    (hχ : ∃ g : G, toZModPow 1 (χ g).toAdd ≠ 0) :
    Function.Surjective χ := by
  obtain ⟨g, hg⟩ := hχ
  let f : G → PadicInt p := fun x => (χ x).toAdd
  have hf : Continuous f := χ.continuous
  have hunit : IsUnit (f g) := by
    by_contra h
    have hd : (p : PadicInt p) ∣ f g :=
      (norm_lt_one_iff_dvd (f g)).mp (not_isUnit_iff.mp h)
    apply hg
    change f g ∈ RingHom.ker (toZModPow 1)
    rw [ker_toZModPow, pow_one, Ideal.mem_span_singleton]
    exact hd
  obtain ⟨u, hu⟩ := hunit
  have hclosed : IsClosed (Set.range f) := (isCompact_range hf).isClosed
  have hmul (z : PadicInt p) : z * (u : PadicInt p) ∈ Set.range f := by
    refine DenseRange.induction_on denseRange_natCast z
      (hclosed.preimage (continuous_id.mul continuous_const)) ?_
    intro n
    rw [hu]
    refine ⟨g ^ n, ?_⟩
    change (χ (g ^ n)).toAdd = (n : PadicInt p) * f g
    rw [map_pow]
    change n • f g = (n : PadicInt p) * f g
    exact nsmul_eq_mul n (f g)
  intro y
  have hy := hmul (y.toAdd * (↑u⁻¹ : PadicInt p))
  rw [mul_assoc, Units.inv_mul, mul_one] at hy
  obtain ⟨x, hx⟩ := hy
  exact ⟨x, congrArg Multiplicative.ofAdd hx⟩

end PadicInt
