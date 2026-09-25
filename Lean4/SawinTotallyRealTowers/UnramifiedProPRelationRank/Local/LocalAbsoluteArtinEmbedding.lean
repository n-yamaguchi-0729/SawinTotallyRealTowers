/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import ClassFieldTheory.LocalClassFieldTheory.Infinite.AbsoluteArtinRestriction
import ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.GeneralTowerNaturality

set_option autoImplicit false
/-!
# Absolute Artin action on an embedded finite extension

An actual representative of the absolute Artin value acts on every embedded
finite abelian extension by its finite Artin automorphism.  The representative
condition is supplied by the quotient map, not by an Artin-comparison assumption.
-/

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open LocalClassFieldTheory

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
variable (L : Type) [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsAbelianGalois K L]

/-- Actual Artin action in the separable-closure model. -/
theorem separableAbsoluteLocalArtinMap_lift_action
    (i : L →ₐ[K] SeparableClosure K) (a : Kˣ)
    (sigma : Gal(SeparableClosure K / K))
    (hsigma : (QuotientGroup.mk sigma : localAbsoluteAbelianProfinite K) =
      separableAbsoluteLocalArtinMap K a)
    (z : L) :
    sigma (i z) = i (abelianLocalArtinMonoidHom K L a z) := by
  let E := i.fieldRange
  let e : L ≃ₐ[K] E := i.equivFieldRange
  let _ : FiniteDimensional K E := e.toLinearEquiv.finiteDimensional
  let _ : IsAbelianGalois K E := IsAbelianGalois.of_algHom e.symm.toAlgHom
  have hr : AlgEquiv.restrictNormalHom E sigma = abelianLocalArtinMonoidHom K E a := by
    calc
      AlgEquiv.restrictNormalHom E sigma =
          absoluteAbelianRestriction K E (QuotientGroup.mk sigma) := rfl
      _ = abelianLocalArtinMap K E a := by
        rw [hsigma, separableAbsoluteLocalArtinMap_restriction]
      _ = abelianLocalArtinMonoidHom K E a := by
        change (abelianLocalArtinMap K E).toMonoidHom a = _
        rw [abelianLocalArtinMap_toMonoidHom]
  have he := DFunLike.congr_fun
    (abelianLocalArtinMonoidHom_autCongr K L E e) a
  change AlgEquiv.autCongr e (abelianLocalArtinMonoidHom K L a) =
    abelianLocalArtinMonoidHom K E a at he
  calc
    sigma (i z) = ((AlgEquiv.restrictNormalHom E sigma) (e z) : SeparableClosure K) :=
      (AlgEquiv.restrictNormal_commutes sigma E (e z)).symm
    _ = ((AlgEquiv.autCongr e (abelianLocalArtinMonoidHom K L a)) (e z) :
        SeparableClosure K) := by rw [hr, ← he]
    _ = i (abelianLocalArtinMonoidHom K L a z) := by
      change (e (abelianLocalArtinMonoidHom K L a (e.symm (e z))) :
        SeparableClosure K) = _
      rw [e.symm_apply_apply]
      rfl

/-- Actual Artin action in the algebraic-closure model. -/
theorem absoluteLocalArtinMap_lift_action
    (i : L →ₐ[K] AlgebraicClosure K) (a : Kˣ)
    (sigma : Gal(AlgebraicClosure K / K))
    (hsigma : (QuotientGroup.mk (show Field.absoluteGaloisGroup K from sigma) :
      Field.absoluteGaloisGroupAbelianization K) =
      absoluteLocalArtinMap K a)
    (z : L) :
    sigma (i z) = i (abelianLocalArtinMonoidHom K L a z) := by
  let j : L →ₐ[K] SeparableClosure K :=
    i.codRestrict (separableClosure K (AlgebraicClosure K)).toSubalgebra fun x ↦
      (Algebra.IsSeparable.isSeparable K x).map i i.injective
  let tau := standardToSeparableAbsoluteGaloisEquiv K sigma
  have htau : (QuotientGroup.mk tau : localAbsoluteAbelianProfinite K) =
      separableAbsoluteLocalArtinMap K a := by
    have h := congrArg (separableToStandardAbsoluteAbelianizationEquiv K).symm hsigma
    rw [separableToStandardAbsoluteAbelianizationEquiv_symm_artinMap] at h
    exact h
  exact congrArg (fun x : SeparableClosure K ↦ (x : AlgebraicClosure K))
    (separableAbsoluteLocalArtinMap_lift_action K L j a tau htau z)

end ClassFieldTower.Martinet.Shafarevich
