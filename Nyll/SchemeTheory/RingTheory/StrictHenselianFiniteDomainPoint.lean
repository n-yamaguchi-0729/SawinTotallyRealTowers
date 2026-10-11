/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.HenselianFiniteDomainLocal
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Closed geometric points of finite domains over strictly Henselian rings

A finite domain over a Henselian local ring is local. When the base residue
field is separably closed, its finite residue extension is purely inseparable.
Thus every automorphism of the finite algebra fixes every closed geometric
point. The locality and the residue action are both proved here.
-/

noncomputable section

namespace SchemeTheory

universe u v w

/-- Every algebra automorphism of a finite domain over a strictly Henselian
local ring fixes a specified closed geometric point. -/
theorem strictHenselian_finiteDomain_aut_fixes_closedPoint
    (R : Type u) (B : Type v) [CommRing R] [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    [CommRing B] [IsDomain B] [Algebra R B] [Module.Finite R B]
    {Ω : Type w} [Field Ω] (φ : B →+* Ω) [IsLocalHom φ]
    (σ : B ≃ₐ[R] B) : φ.comp σ.toRingEquiv.toRingHom = φ := by
  let : IsLocalRing B := isLocalRing_of_finite_domain_henselian R B
  have hcontract : (IsLocalRing.maximalIdeal B).under R = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := R)
        (IsLocalRing.maximalIdeal B))
  let : IsLocalHom (algebraMap R B) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R B)).out 1 5).mpr hcontract
  let k := IsLocalRing.ResidueField R
  let l := IsLocalRing.ResidueField B
  have hσ : (IsLocalRing.ResidueField.mapAlgEquiv' σ).toAlgHom = AlgHom.id k l :=
    Subsingleton.elim _ _
  ext b
  change φ (σ b) = φ b
  have heq : IsLocalRing.residue B (σ b) = IsLocalRing.residue B b :=
    congrArg (fun f : l →ₐ[k] l => f (IsLocalRing.residue B b)) hσ
  have hpoint := congrArg (IsLocalRing.ResidueField.lift φ) heq
  simpa only [IsLocalRing.ResidueField.lift_residue_apply] using hpoint

end SchemeTheory
