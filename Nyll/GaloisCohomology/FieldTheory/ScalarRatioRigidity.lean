/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


import Mathlib.Algebra.Field.Subfield.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Rigidity from scalar ratios

If every nonzero element of a field is carried to a scalar multiple of itself
by scalars in a fixed proper subfield, a unital ring endomorphism is the identity.
The proof compares an element outside the subfield with its translate by one.
-/

namespace FieldTheory
variable {K : Type*} [Field K]

/-- A field endomorphism which scales every element by an element of a fixed
proper subfield is the identity. -/
theorem ringHom_eq_id_of_div_mem_subfield
    (C : Subfield K) (hC : C ≠ ⊤) (τ : K →+* K)
    (hratio : ∀ x : K, x ≠ 0 → τ x / x ∈ C) : τ = RingHom.id K := by
  classical
  have hfix (x : K) (hx : x ∉ C) : τ x = x := by
    have hx0 : x ≠ 0 := fun h => hx (h ▸ C.zero_mem)
    have hx1 : x + 1 ≠ 0 := by
      intro h
      have he : x = -1 := eq_neg_of_add_eq_zero_left h
      exact hx (he ▸ C.neg_mem C.one_mem)
    let c : K := τ x / x
    let d : K := τ (x + 1) / (x + 1)
    have hc : c ∈ C := hratio x hx0
    have hd : d ∈ C := hratio (x + 1) hx1
    have hcx : c * x = τ x := div_mul_cancel₀ _ hx0
    have hdx : d * (x + 1) = τ x + 1 :=
      (div_mul_cancel₀ _ hx1).trans (by rw [map_add, map_one])
    have hrel : (c - d) * x = d - 1 := by linear_combination hcx - hdx
    have hcd : c = d := by
      by_contra hne
      have he : x = (d - 1) / (c - d) := (eq_div_iff (sub_ne_zero.mpr hne)).mpr
        ((mul_comm x (c - d)).trans hrel)
      exact hx (he ▸ C.div_mem (C.sub_mem hd C.one_mem) (C.sub_mem hc hd))
    have hd1 : d = 1 := by
      rw [hcd, sub_self, zero_mul] at hrel
      exact sub_eq_zero.mp hrel.symm
    exact hcx.symm.trans (by rw [hcd, hd1, one_mul])
  obtain ⟨y, hy⟩ : ∃ y : K, y ∉ C := by
    by_contra hno
    apply hC
    apply top_unique
    intro x _
    exact not_not.mp (fun hx => hno ⟨x, hx⟩)
  apply RingHom.ext
  intro x
  by_cases hx : x ∈ C
  · have hyx : y + x ∉ C := by
      intro h
      apply hy
      exact (add_sub_cancel_right y x) ▸ C.sub_mem h hx
    have h := hfix (y + x) hyx
    rw [map_add, hfix y hy] at h
    exact add_left_cancel h
  · exact hfix x hx
end FieldTheory
