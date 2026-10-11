/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.Algebra.Algebra.Hom
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.Localization.Integral

/-!
# Inertia-fixed integral numerators

For an element of the ambient Galois field fixed by normalization inertia,
the native integral-multiple theorem supplies a nonzero base denominator.
Scalar preservation and the existing literal coefficient square prove that
the resulting actual integral-closure numerator is fixed by the same original
inertia. No finite extension, fixed-field comparison, or stalk-image premise
is introduced. The base denominator need not avoid the prime.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v w

attribute [local instance] normalizationInertiaImageAction

/-- An original inertia-fixed field element has an inertia-fixed integral
numerator after multiplication by a nonzero element of the original base.
The statement holds for any ideal; in particular for the original prime. -/
theorem integralClosure_exists_inertia_fixed_integral_multiple
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsDomain A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (integralClosure A L)) (x : L)
    (hx : ∀ σ ∈ Q.inertia Gal(L/K), σ x = x) :
    ∃ a : A, a ≠ 0 ∧ ∃ b : integralClosure A L,
      (b : L) = a • x ∧ ∀ σ ∈ Q.inertia Gal(L/K), σ • b = b := by
  have : Algebra.IsAlgebraic A L :=
    (IsFractionRing.comap_isAlgebraic_iff (A := A) (K := K) (C := L)).mpr inferInstance
  have hxalg : IsAlgebraic A x := Algebra.IsAlgebraic.isAlgebraic x
  obtain ⟨a, ha, hint⟩ := hxalg.exists_integral_multiple
  let b : integralClosure A L := ⟨a • x, hint⟩
  refine ⟨a, ha, b, rfl, ?_⟩
  intro σ hσ
  apply Subtype.ext
  have hfield : σ (a • x) = a • x :=
    (AlgHom.map_smul_of_tower σ.toAlgHom a x).trans
      (congrArg (fun y : L => a • y) (hx σ hσ))
  have hcoeff := RingHom.congr_fun (normalizationInertiaImageAction_comp_inclusion A K L σ) b
  exact hcoeff.symm.trans hfield

end EtaleFundamentalGroups.Inertia
