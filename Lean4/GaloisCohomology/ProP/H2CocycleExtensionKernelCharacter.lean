/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.H2CocycleExtensionSplitting

set_option autoImplicit false
/-!
# Splitting a cocycle extension with a coefficient-kernel character

A continuous character which is the identity on the explicit coefficient kernel constructs
a continuous section by correcting the zero-coordinate lift. The prime-to-index restriction
leaf supplies this character from the actual finite-index transfer.
-/

open scoped Topology

namespace ClassFieldTower.ProP

open CategoryTheory TopRep ContRepresentation FreeProPH2Cocycle

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G]

/-- A coefficient-kernel retraction gives an explicit continuous section and kills the class. -/
theorem H2CocycleExtension.π_eq_zero_of_kernelCharacter
    (z : Cohomology.trivialZModPCocyclesLifted p G 2)
    (χ : H2CocycleExtension z →ₜ* Multiplicative (ZMod p))
    (hχ : ∀ a : A p, χ ⟨a, 1⟩ = Multiplicative.ofAdd a.down) :
    ContinuousCohomology.π (Cohomology.trivialZModPLifted p G) 2 z = 0 := by
  have hχag (a : A p) (g : G) :
      (χ ⟨a, g⟩).toAdd = a.down + (χ ⟨0, g⟩).toAdd := by
    have he : (⟨a, g⟩ : H2CocycleExtension z) = ⟨a, 1⟩ * ⟨0, g⟩ := by
      apply H2CocycleExtension.ext
      · change a = a + 0 + normalizedCocycle z 1 g
        rw [normalizedCocycle_one_left]
        simp
      · exact (one_mul g).symm
    rw [he, map_mul, hχ]
    rfl
  let b : G → A p := fun g => ULift.up (-(χ ⟨0, g⟩).toAdd)
  have hb (g h : G) : b (g * h) = b g + b h + normalizedCocycle z g h := by
    apply ULift.ext
    change -(χ ⟨0, g * h⟩).toAdd =
      -(χ ⟨0, g⟩).toAdd + -(χ ⟨0, h⟩).toAdd + (normalizedCocycle z g h).down
    have hm := congrArg Multiplicative.toAdd (χ.map_mul ⟨0, g⟩ ⟨0, h⟩)
    change (χ ⟨0 + 0 + normalizedCocycle z g h, g * h⟩).toAdd =
      (χ ⟨0, g⟩).toAdd + (χ ⟨0, h⟩).toAdd at hm
    rw [zero_add, zero_add, hχag] at hm
    calc
      _ = -((normalizedCocycle z g h).down + (χ ⟨0, g * h⟩).toAdd) +
          (normalizedCocycle z g h).down := by abel
      _ = _ := by rw [hm]; abel
  have hbcont : Continuous b := by
    have hzero : Continuous (fun g : G => (⟨0, g⟩ : H2CocycleExtension z)) :=
      (H2CocycleExtension.toProdHomeomorph z).symm.continuous.comp
        (continuous_const.prodMk continuous_id)
    have hc : Continuous (fun g : G => (χ ⟨0, g⟩).toAdd) :=
      χ.continuous_toFun.comp hzero
    exact continuous_uliftUp.comp hc.neg
  let s : G →ₜ* H2CocycleExtension z :=
    { toFun := fun g => ⟨b g, g⟩
      map_one' := by
        apply H2CocycleExtension.ext
        · apply ULift.ext
          change -(χ 1).toAdd = (0 : ZMod p)
          rw [map_one]
          simp
        · rfl
      map_mul' := fun g h => H2CocycleExtension.ext z (hb g h) rfl
      continuous_toFun := by
        rw [continuous_induced_rng]
        exact hbcont.prodMk continuous_id }
  apply H2CocycleExtension.π_eq_zero_of_section z s
  ext g
  rfl

end
end ClassFieldTower.ProP
