/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.TameRamification.ValueGroup.NonarchimedeanLocalField.Valuation
import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension

/-!
# Local-field extension invariants

This file exposes the elementary divisibility consequences of the canonical
ramification identity `e * f = [L : K]` for finite separable
nonarchimedean local-field extensions.
-/

noncomputable section

universe u

namespace TameAbhyankar

open LocalFieldTheory
open scoped ValuativeRel

namespace NAField

local notation "e[" K "," L "]" =>
  Ideal.ramificationIdx (𝓂[L] : Ideal 𝒪[L]) 𝒪[K]

local notation "f[" K "," L "]" => Module.finrank 𝓀[K] 𝓀[L]

variable {K L : Type u}
variable [Field K] [ValuativeRel K] [TopologicalSpace K]
variable [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L]
variable [IsNonarchimedeanLocalField L]
variable [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
variable [Valuation.HasExtension (ValuativeRel.valuation K)
  (ValuativeRel.valuation L)]

/-- The canonical ramification and residue degrees multiply to the field degree. -/
theorem ramificationIndex_mul_residueDegree_eq_finrank :
    e[K,L] * f[K,L] = Module.finrank K L := by
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
    localCompleteDVF_integerRing_isIntegralClosure K L
  have h :=
    maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank_of_isIntegralClosure
      K L
  have hp : (𝓂[K] : Ideal 𝒪[K]) ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField
      (IsLocalRing.maximalIdeal.isMaximal 𝒪[K])
      (IsDiscreteValuationRing.not_isField 𝒪[K])
  rw [Ideal.ramificationIdx'_eq_ramificationIdx _ _ hp] at h
  exact h

/-- The canonical ramification index divides the field degree. -/
theorem ramificationIndex_dvd_finrank :
    e[K,L] ∣ Module.finrank K L :=
  ⟨f[K,L], (ramificationIndex_mul_residueDegree_eq_finrank
    (K := K) (L := L)).symm⟩

/-- The canonical residue degree divides the field degree. -/
theorem residueDegree_dvd_finrank :
    f[K,L] ∣ Module.finrank K L := by
  refine ⟨e[K,L], ?_⟩
  calc
    Module.finrank K L = e[K,L] * f[K,L] :=
      (ramificationIndex_mul_residueDegree_eq_finrank
        (K := K) (L := L)).symm
    _ = f[K,L] * e[K,L] := by rw [mul_comm]

/-- The ramification index of a finite local-field extension is positive. -/
theorem ramificationIndex_pos :
    0 < e[K,L] := by
  have hfin : 0 < Module.finrank K L := Module.finrank_pos
  exact Nat.pos_of_ne_zero (fun he => by
    have hzero : e[K,L] * f[K,L] = 0 := by rw [he, zero_mul]
    rw [ramificationIndex_mul_residueDegree_eq_finrank
      (K := K) (L := L)] at hzero
    exact (Nat.ne_of_gt hfin) hzero)

/-- The residue degree of a finite local-field extension is positive. -/
theorem residueDegree_pos :
    0 < f[K,L] := by
  have hfin : 0 < Module.finrank K L := Module.finrank_pos
  exact Nat.pos_of_ne_zero (fun hf => by
    have hzero : e[K,L] * f[K,L] = 0 := by rw [hf, mul_zero]
    rw [ramificationIndex_mul_residueDegree_eq_finrank
      (K := K) (L := L)] at hzero
    exact (Nat.ne_of_gt hfin) hzero)

/-- Any divisor of the residue degree can be paired with the ramification
index to divide the field degree. -/
theorem ramificationIndex_mul_dvd_finrank_of_dvd_residueDegree {d : ℕ}
    (hd : d ∣ f[K,L]) :
    e[K,L] * d ∣ Module.finrank K L := by
  rcases hd with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  calc
    Module.finrank K L = e[K,L] * f[K,L] :=
      (ramificationIndex_mul_residueDegree_eq_finrank
        (K := K) (L := L)).symm
    _ = e[K,L] * (d * q) := by rw [hq]
    _ = (e[K,L] * d) * q := by rw [mul_assoc]

/-- If the residue degree is one, the ramification index is the whole field degree. -/
theorem ramificationIndex_eq_finrank_of_residueDegree_eq_one
    (hf : f[K,L] = 1) :
    e[K,L] = Module.finrank K L := by
  rw [← ramificationIndex_mul_residueDegree_eq_finrank (K := K) (L := L),
    hf, mul_one]

/-- If the ramification index is one, the residue degree is the whole field degree. -/
theorem residueDegree_eq_finrank_of_ramificationIndex_eq_one
    (he : e[K,L] = 1) :
    f[K,L] = Module.finrank K L := by
  rw [← ramificationIndex_mul_residueDegree_eq_finrank (K := K) (L := L),
    he, one_mul]

end NAField

end TameAbhyankar

end
