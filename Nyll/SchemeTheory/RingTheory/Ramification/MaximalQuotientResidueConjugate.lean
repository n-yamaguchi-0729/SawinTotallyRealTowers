/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.MaximalQuotientResidueNaturality
import Nyll.SchemeTheory.RingTheory.Ramification.NativeMaximalResidue
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Conjugacy of quotient and localization residue maps

Identifies the residue automorphism of a localization as the conjugate of the quotient
automorphism through the canonical maximal-quotient residue equivalence.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The actual localization residue map is conjugate to its quotient map
through the fixed canonical maximal-quotient equivalence. -/
theorem maximalQuotientResidueEquiv_localization_conjugate
    {B : Type u} [CommRing B] (Q : Ideal B) [Q.IsMaximal]
    (e : B ≃+* B) (hQ : Q = Q.comap e.toRingHom) :
    (IsLocalRing.ResidueField.mapEquiv
        (Localization.localRingEquiv Q Q e hQ)).toRingHom =
      ((maximalQuotientResidueEquiv Q).toRingHom.comp
        (Ideal.quotientEquiv Q Q e
          ((congrArg (Ideal.map e.toRingHom) hQ).trans
            (Ideal.map_comap_eq_self_of_equiv e Q)).symm).toRingHom).comp
        (maximalQuotientResidueEquiv Q).symm.toRingHom := by
  apply RingHom.ext
  intro x
  have hx : (maximalQuotientResidueEquiv Q).toRingHom.toFun
      ((maximalQuotientResidueEquiv Q).symm.toRingHom.toFun x) = x :=
    (maximalQuotientResidueEquiv Q).right_inv x
  have hlocal := maximalQuotientResidueEquiv_naturality Q e hQ
    ((maximalQuotientResidueEquiv Q).symm.toRingHom.toFun x)
  exact Eq.trans (α := Q.ResidueField)
    (congrArg (IsLocalRing.ResidueField.mapEquiv
      (Localization.localRingEquiv Q Q e hQ)).toRingHom.toFun hx.symm) hlocal

end EtaleFundamentalGroups.Inertia

end
