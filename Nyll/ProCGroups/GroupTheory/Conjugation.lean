/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Conjugation on characteristic quotients

This module constructs the automorphism induced on a characteristic quotient and uses it to
descend conjugation by a normal subgroup to an action of the ambient quotient.
-/

namespace ProCGroups

namespace Subgroup
namespace Characteristic

universe u

variable {G : Type u} [Group G] {H : Subgroup G}

/-- An automorphism descends to the quotient by a characteristic subgroup. -/
noncomputable def quotientMulEquiv
    (hH : H.Characteristic) (e : G ≃* G) :
    G ⧸ H ≃* G ⧸ H := by
  letI : H.Normal := by infer_instance
  exact QuotientGroup.congr H H e (Subgroup.characteristic_iff_map_eq.mp hH e)

/--
The quotient equivalence induced by a characteristic subgroup sends representatives to
representatives.
-/
@[simp] theorem quotientMulEquiv_mk
    (hH : H.Characteristic) (e : G ≃* G) (g : G) :
    quotientMulEquiv hH e (QuotientGroup.mk' H g) = QuotientGroup.mk' H (e g) :=
  rfl

end Characteristic
end Subgroup

end ProCGroups

namespace ProCGroups.GroupTheory

universe u

/--
If \(K\) is characteristic in a normal subgroup \(N\) and inner conjugation by elements of \(N\)
is trivial on \(N/K\), then \(G/N\) acts on \(N/K\) by conjugation.
-/
noncomputable def quotientConjugationOnCharacteristicQuotient
    {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal] (K : Subgroup N) [K.Characteristic]
    (hNactsTrivially :
      ∀ n x : N, (((MulAut.conjNormal (n : G)) x) * x⁻¹ : N) ∈ K) :
    (G ⧸ N) →* MulAut (N ⧸ K) := by
  let hKchar : K.Characteristic := inferInstance
  letI : K.Normal := by infer_instance
  let prequotientAction : G →* MulAut (N ⧸ K) :=
    { toFun := fun g => ProCGroups.Subgroup.Characteristic.quotientMulEquiv hKchar
        (MulAut.conjNormal g)
      map_one' := by
        ext a
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K a
        rw [Subgroup.Characteristic.quotientMulEquiv_mk]
        simp only [map_one, MulAut.one_apply, QuotientGroup.mk'_apply]
      map_mul' := by
        intro g h
        ext a
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K a
        change
          QuotientGroup.mk' K ((MulAut.conjNormal (g * h)) x) =
            ProCGroups.Subgroup.Characteristic.quotientMulEquiv hKchar (MulAut.conjNormal g)
              (ProCGroups.Subgroup.Characteristic.quotientMulEquiv hKchar (MulAut.conjNormal h)
                  (QuotientGroup.mk' K x))
        rw [Subgroup.Characteristic.quotientMulEquiv_mk,
          Subgroup.Characteristic.quotientMulEquiv_mk]
        congr 1
        ext
        simp only [map_mul, MulAut.mul_apply, MulAut.conjNormal_apply, mul_assoc]}
  have hNker : N ≤ prequotientAction.ker := by
    intro g hg
    ext a
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K a
    change
      QuotientGroup.mk' K ((MulAut.conjNormal g) x) =
        QuotientGroup.mk' K x
    exact
      (QuotientGroup.eq_iff_div_mem (N := K)
        (x := (MulAut.conjNormal g) x) (y := x)).2
        (by simpa [div_eq_mul_inv] using hNactsTrivially ⟨g, hg⟩ x)
  exact QuotientGroup.lift N prequotientAction hNker

/-- The algebraic conjugation action sends representatives to conjugates. -/
@[simp] theorem quotientConjugationOnCharacteristicQuotient_mk_apply_mk
    {G : Type u} [Group G]
    (N : Subgroup G) [N.Normal] (K : Subgroup N) [K.Characteristic]
    (hNactsTrivially :
      ∀ n x : N, (((MulAut.conjNormal (n : G)) x) * x⁻¹ : N) ∈ K)
    (g : G) (n : N) :
    quotientConjugationOnCharacteristicQuotient
      (G := G) N K hNactsTrivially
      (QuotientGroup.mk' N g) (QuotientGroup.mk' K n) =
        QuotientGroup.mk' K ((MulAut.conjNormal g) n) := by
  dsimp [quotientConjugationOnCharacteristicQuotient]
  rfl

end ProCGroups.GroupTheory
