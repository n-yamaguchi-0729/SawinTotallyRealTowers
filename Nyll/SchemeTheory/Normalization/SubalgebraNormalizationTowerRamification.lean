/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.SubalgebraNormalizationTower
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RamificationInertia.Ramification

/-!
# Ramification indices in normalization towers

Proves compatibility of the normalization tower map with base coefficients and multiplicativity
of ramification indices for the resulting tower.
-/

noncomputable section

namespace SchemeTheory

universe u v

variable {A : Type u} {L : Type v}
  [CommRing A] [CommRing L] [Algebra A L]

/-- The existing literal normalization tower map preserves the original
coefficient maps, as follows from its ambient inclusion triangle. -/
theorem subalgebraNormalizationTowerRingMap_comp_base
    (S T : Subalgebra A L) (h : S ≤ T) :
    (subalgebraNormalizationTowerRingMap S T h).comp
        (algebraMap A (subalgebraNormalizationCommAlgCat S)) =
      algebraMap A (subalgebraNormalizationCommAlgCat T) := by
  apply (RingHom.cancel_left (g := subalgebraNormalizationRingMap T)
    (subalgebraNormalizationRingMap_injective T)).mp
  rw [← RingHom.comp_assoc, subalgebraNormalizationTowerRingMap_comp,
    subalgebraNormalizationRingMap_comp_base,
    subalgebraNormalizationRingMap_comp_base]

/-- Ramification indices multiply for the literal normalization inclusion.
Its algebra structure is installed from that ring map; its scalar tower,
torsion-freeness, and flatness are constructed here from the coefficient
triangle and the native injection. -/
theorem subalgebraNormalization_ramificationIdx_tower
    (S T : Subalgebra A L) (h : S ≤ T)
    [IsDedekindDomain (subalgebraNormalizationCommAlgCat S)]
    [IsDomain (subalgebraNormalizationCommAlgCat T)]
    (P : Ideal (subalgebraNormalizationCommAlgCat S))
    (Q : Ideal (subalgebraNormalizationCommAlgCat T))
    (hPQ : P = Q.comap (subalgebraNormalizationTowerRingMap S T h)) :
    letI : Algebra (subalgebraNormalizationCommAlgCat S)
        (subalgebraNormalizationCommAlgCat T) :=
      (subalgebraNormalizationTowerRingMap S T h).toAlgebra
    Q.ramificationIdx A = P.ramificationIdx A *
      Q.ramificationIdx (subalgebraNormalizationCommAlgCat S) := by
  let : Algebra (subalgebraNormalizationCommAlgCat S)
      (subalgebraNormalizationCommAlgCat T) :=
    (subalgebraNormalizationTowerRingMap S T h).toAlgebra
  have : IsScalarTower A (subalgebraNormalizationCommAlgCat S)
      (subalgebraNormalizationCommAlgCat T) :=
    IsScalarTower.of_algebraMap_eq'
      (subalgebraNormalizationTowerRingMap_comp_base S T h).symm
  have : Module.IsTorsionFree (subalgebraNormalizationCommAlgCat S)
      (subalgebraNormalizationCommAlgCat T) :=
    (Module.isTorsionFree_iff_algebraMap_injective).mpr
      (subalgebraNormalizationTowerRingMap_injective S T h)
  have : Q.LiesOver P := ⟨hPQ⟩
  exact Ideal.ramificationIdx_tower (R := A) P Q

end SchemeTheory

end
