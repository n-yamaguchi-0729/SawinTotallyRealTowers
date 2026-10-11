/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ProCGroups.WreathProducts
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pi.Lemmas

/-!
# Quotients of regular wreath modules

Restriction to a finite subgroup followed by multiplication along the fibers
of a quotient is equivariant and surjective. This produces regular wreath
quotients after restricting the right factor to the subgroup.
-/

namespace ProCGroups

universe u v w

variable {A : Type u} [CommGroup A] {Q : Type v} [Group Q] [Finite Q]
  {B : Type w} [Group B]

/-- Multiply the coordinates in each fiber of a homomorphism from a subgroup. -/
noncomputable def regularWreathFiberNorm (J : Subgroup Q) (ρ : J →* B) :
    (Q → A) →* (B → A) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  refine {
    toFun := fun f b => ∏ j : J, if ρ j = b then f (j : Q) else 1
    map_one' := ?_
    map_mul' := ?_ }
  · funext b
    simp only [Pi.one_apply, ite_self, Finset.prod_const_one]
  · intro f g
    funext b
    simp only [Pi.mul_apply, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : ρ j = b
    · rw [ite_eq_left hj, ite_eq_left hj, ite_eq_left hj]
    · rw [ite_eq_right hj, ite_eq_right hj, ite_eq_right hj, one_mul]

/-- Fiber multiplication intertwines the two regular translation actions. -/
theorem regularWreathFiberNorm_equivariant (J : Subgroup Q) (ρ : J →* B)
    (j : J) (f : Q → A) :
    regularWreathFiberNorm J ρ
        (mulAutArrow (G := Q) (A := Q) (M := A) (j : Q) f) =
      mulAutArrow (G := B) (A := B) (M := A) (ρ j)
        (regularWreathFiberNorm J ρ f) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  funext b
  change (∏ k : J, if ρ k = b then f ((j : Q)⁻¹ * k) else 1) =
    ∏ k : J, if ρ k = (ρ j)⁻¹ * b then f (k : Q) else 1
  apply Fintype.prod_equiv (Equiv.mulLeft j⁻¹)
  intro k
  change (if ρ k = b then f ((j : Q)⁻¹ * k) else 1) =
    if ρ (j⁻¹ * k) = (ρ j)⁻¹ * b then f ((j⁻¹ * k : J) : Q) else 1
  have h : ρ k = b ↔ ρ (j⁻¹ * k) = (ρ j)⁻¹ * b := by
    rw [map_mul, map_inv]
    exact (mul_left_cancel_iff).symm
  simp only [h]
  rfl

/-- A coordinate supported in the subgroup maps to its image coordinate. -/
theorem regularWreathFiberNorm_mulSingle [DecidableEq Q] [DecidableEq B]
    (J : Subgroup Q) (ρ : J →* B)
    (j : J) (a : A) :
    regularWreathFiberNorm J ρ (Pi.mulSingle (j : Q) a) =
      (Pi.mulSingle (ρ j) a : B → A) := by
  classical
  let : Fintype J := Fintype.ofFinite J
  funext b
  simp only [regularWreathFiberNorm, MonoidHom.coe_mk, OneHom.coe_mk]
  rw [Finset.prod_eq_single j]
  · simp only [Pi.mulSingle_eq_same, Pi.mulSingle_apply]
    by_cases h : ρ j = b
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  · intro k _ hkj
    have hval : (k : Q) ≠ (j : Q) := fun h => hkj (Subtype.ext h)
    rw [Pi.mulSingle_eq_of_ne hval, ite_self]
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

/-- A surjective homomorphism gives a surjective map on regular modules. -/
theorem regularWreathFiberNorm_surjective (J : Subgroup Q) (ρ : J →* B)
    (hρ : Function.Surjective ρ) :
    Function.Surjective (regularWreathFiberNorm (A := A) J ρ) := by
  classical
  have : Finite B := Finite.of_surjective ρ hρ
  let : Fintype B := Fintype.ofFinite B
  intro f
  let s : B → J := Function.surjInv hρ
  have hs (b : B) : ρ (s b) = b := Function.rightInverse_surjInv hρ b
  refine ⟨∏ b : B, Pi.mulSingle ((s b : J) : Q) (f b), ?_⟩
  rw [map_prod]
  simp only [regularWreathFiberNorm_mulSingle, hs]
  funext b
  rw [Finset.prod_apply, Finset.prod_eq_single b]
  · rw [Pi.mulSingle_eq_same]
  · intro c _ hcb
    rw [Pi.mulSingle_eq_of_ne (Ne.symm hcb)]
  · intro hb
    exact False.elim (hb (Finset.mem_univ b))

end ProCGroups
