/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.GaloisCohomology.ProP.QuotientRestriction

/-!
# Trivial restriction maps in degree-one continuous cohomology

Pullback along the constant-one homomorphism vanishes on cocycles and
continuous cohomology with trivial `ZMod p` coefficients. Consequently,
inflation followed by restriction to the kernel vanishes in degree one.
The same statements are proved for universe-lifted coefficients.
-/

open CategoryTheory TopRep ContRepresentation

namespace ClassFieldTower.Cohomology

noncomputable section

universe u

variable (p : ℕ)
variable {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Pullback along the constant-one group homomorphism is zero on continuous cocycles in
degree one with trivial `ZMod p` coefficients. -/
theorem trivialZModPCocyclesMap_trivial_one_eq_zero :
    trivialZModPCocyclesMap p (trivialContinuousHom H G) 1 = 0 := by
  rw [← cancel_mono ((trivialZModPCochains p H).iCycles 1)]
  simp only [HomologicalComplex.cyclesMap_i, Limits.zero_comp]
  ext z
  change _ = (0 : (TopRep.resolutionX (trivialZModP p H) 2).ρ.invariants)
  apply Subtype.ext
  ext h₀ h₁
  change (((trivialZModPCochains p G).iCycles 1) z).1 1 1 = 0
  have hz :
      ((trivialZModPCochains p G).d 1 2).hom
          (((trivialZModPCochains p G).iCycles 1).hom z) = 0 := by
    have h := ConcreteCategory.congr_hom
      ((trivialZModPCochains p G).iCycles_d (i := 1) (j := 2)) z
    change ((trivialZModPCochains p G).d 1 2).hom
      (((trivialZModPCochains p G).iCycles 1).hom z) = 0 at h
    exact h
  have hz111 := congrArg
    (fun τ : (trivialZModPCochains p G).X 2 => τ.1 1 1 1) hz
  have hd := TopRep.homogeneousCochains.d_apply (trivialZModP p G) 1
    (((trivialZModPCochains p G).iCycles 1).hom z)
  have hd111 := congrArg (fun τ => τ 1 1 1) hd
  rw [hd111] at hz111
  simp [d_succ, d_zero, hom_sub, ContIntertwiningMap.sub_apply,
    coind₁ι_toFun, coind₁Map_toFun] at hz111
  exact hz111.trans rfl

/-- Pullback along the constant-one group homomorphism is zero on continuous `H¹` with trivial
`ZMod p` coefficients. -/
theorem continuousCohomologyZModPMap_trivial_one_eq_zero :
    continuousCohomologyZModPMap p (trivialContinuousHom H G) 1 = 0 := by
  rw [← cancel_epi (ContinuousCohomology.π (trivialZModP p G) 1)]
  rw [trivialZModP_π_naturality]
  rw [trivialZModPCocyclesMap_trivial_one_eq_zero]
  simp

/-- Inflation followed by restriction is zero on continuous `H¹` with trivial `ZMod p`
coefficients. -/
theorem inflation_comp_restriction_degree_one_eq_zero
    (N : Subgroup G) [N.Normal] :
    continuousCohomologyZModPMap p (quotientProjection N) 1 ≫
        continuousCohomologyZModPMap p (subgroupInclusion N) 1 = 0 := by
  rw [inflation_comp_restriction_eq_trivialMap]
  exact continuousCohomologyZModPMap_trivial_one_eq_zero p

section Lifted

variable {G H : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Pullback along the constant-one homomorphism is zero on degree-one cocycles with
universe-lifted trivial `ZMod p` coefficients. -/
theorem trivialZModPCocyclesMapLifted_trivial_one_eq_zero :
    trivialZModPCocyclesMapLifted p (trivialContinuousHom H G) 1 = 0 := by
  rw [← cancel_mono ((trivialZModPCochainsLifted p H).iCycles 1)]
  simp only [HomologicalComplex.cyclesMap_i, Limits.zero_comp]
  ext z
  change _ = (0 : (TopRep.resolutionX (trivialZModPLifted p H) 2).ρ.invariants)
  apply Subtype.ext
  ext h₀ h₁
  change (((trivialZModPCochainsLifted p G).iCycles 1) z).1 1 1 = 0
  have hz :
      ((trivialZModPCochainsLifted p G).d 1 2).hom
          (((trivialZModPCochainsLifted p G).iCycles 1).hom z) = 0 := by
    have h := ConcreteCategory.congr_hom
      ((trivialZModPCochainsLifted p G).iCycles_d (i := 1) (j := 2)) z
    change ((trivialZModPCochainsLifted p G).d 1 2).hom
      (((trivialZModPCochainsLifted p G).iCycles 1).hom z) = 0 at h
    exact h
  have hz111 := congrArg
    (fun τ : (trivialZModPCochainsLifted p G).X 2 => τ.1 1 1 1) hz
  have hd := TopRep.homogeneousCochains.d_apply (trivialZModPLifted p G) 1
    (((trivialZModPCochainsLifted p G).iCycles 1).hom z)
  have hd111 := congrArg (fun τ => τ 1 1 1) hd
  rw [hd111] at hz111
  simp [d_succ, d_zero, hom_sub, ContIntertwiningMap.sub_apply,
    coind₁ι_toFun, coind₁Map_toFun] at hz111
  exact hz111.trans rfl

/-- Pullback along the constant-one homomorphism is zero on lifted continuous `H¹`. -/
theorem continuousCohomologyZModPMapLifted_trivial_one_eq_zero :
    continuousCohomologyZModPMapLifted p (trivialContinuousHom H G) 1 = 0 := by
  rw [← cancel_epi (ContinuousCohomology.π (trivialZModPLifted p G) 1)]
  rw [trivialZModPLifted_π_naturality]
  rw [trivialZModPCocyclesMapLifted_trivial_one_eq_zero]
  simp

/-- Inflation followed by restriction is zero on lifted continuous `H¹` with trivial
`ZMod p` coefficients. -/
theorem inflation_comp_restriction_degree_one_eq_zero_lifted
    (N : Subgroup G) [N.Normal] :
    continuousCohomologyZModPMapLifted p (quotientProjection N) 1 ≫
        continuousCohomologyZModPMapLifted p (subgroupInclusion N) 1 = 0 := by
  rw [inflation_comp_restriction_eq_trivialMap_lifted]
  exact continuousCohomologyZModPMapLifted_trivial_one_eq_zero p

end Lifted

end


end ClassFieldTower.Cohomology
