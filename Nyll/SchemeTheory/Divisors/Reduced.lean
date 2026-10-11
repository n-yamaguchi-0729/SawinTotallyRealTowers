/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Nyll.SchemeTheory.Divisors.Basic

/-!
# Reduced ideal sheaves and their closed subschemes

An ideal sheaf is radical exactly when its associated closed subscheme is
reduced.  This is checked on the canonical affine cover by the quotients
`Spec (Γ(X, U) / I(U))`.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

namespace Scheme.IdealSheafData

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- A radical ideal sheaf defines a reduced closed subscheme. -/
theorem IsReduced.subscheme (hI : I.IsReduced) :
    AlgebraicGeometry.IsReduced I.subscheme := by
  let : ∀ U, AlgebraicGeometry.IsReduced
      (I.subschemeCover.openCover.X U) := fun U ↦ by
    change X.affineOpens at U
    have hradical : (I.ideal U).IsRadical := by
      rw [← Ideal.radical_eq_iff]
      have h := congrArg (fun J : X.IdealSheafData ↦ J.ideal U) hI
      simpa only [radical_ideal] using h
    let : _root_.IsReduced (Γ(X, U) ⧸ I.ideal U) :=
      (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mp hradical
    change AlgebraicGeometry.IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U)))
    infer_instance
  exact AlgebraicGeometry.IsReduced.of_openCover I.subscheme
    I.subschemeCover.openCover

/-- If the closed subscheme of an ideal sheaf is reduced, the ideal sheaf is
radical. -/
theorem isReduced_of_subscheme
    [AlgebraicGeometry.IsReduced I.subscheme] : I.IsReduced := by
  rw [IdealSheafData.IsReduced]
  ext U : 2
  apply Ideal.IsRadical.radical
  rw [Ideal.isRadical_iff_quotient_reduced]
  let e := (I.subschemeObjIso U).commRingCatIsoToRingEquiv
  exact isReduced_of_injective e.symm e.symm.injective

/-- Radicality of an ideal sheaf is equivalent to reducedness of its closed
subscheme. -/
theorem isReduced_iff_subscheme_isReduced :
    I.IsReduced ↔ AlgebraicGeometry.IsReduced I.subscheme :=
  ⟨IsReduced.subscheme I, fun h ↦ @isReduced_of_subscheme _ I h⟩

end Scheme.IdealSheafData

end AlgebraicGeometry

end
