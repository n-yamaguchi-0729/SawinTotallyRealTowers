/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.NativeMaximalResidue
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Naturality of the maximal-quotient residue equivalence

Proves that the canonical equivalence from a maximal-ideal quotient to the localization residue
field intertwines the maps induced by a prime-preserving ring automorphism.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u

/-- The fixed canonical maximal-quotient residue equivalence intertwines
the quotient and localization residue maps induced by the same automorphism.
No residue action or comparison equation is supplied as an assumption. -/
theorem maximalQuotientResidueEquiv_naturality
    {B : Type u} [CommRing B] (Q : Ideal B) [Q.IsMaximal]
    (e : B ≃+* B) (hQ : Q = Q.comap e.toRingHom) (x : B ⧸ Q) :
    (IsLocalRing.ResidueField.mapEquiv
        (Localization.localRingEquiv Q Q e hQ)).toRingHom.toFun
        ((maximalQuotientResidueEquiv Q).toRingHom.toFun x) =
      (maximalQuotientResidueEquiv Q).toRingHom.toFun
        ((Ideal.quotientEquiv Q Q e
          ((congrArg (Ideal.map e.toRingHom) hQ).trans
            (Ideal.map_comap_eq_self_of_equiv e Q)).symm).toRingHom.toFun x) := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hmap : Q = Q.map e.toRingHom :=
    ((congrArg (Ideal.map e.toRingHom) hQ).trans
      (Ideal.map_comap_eq_self_of_equiv e Q)).symm
  have hquot : (Ideal.quotientEquiv Q Q e hmap).toRingHom.toFun
        ((Ideal.Quotient.mk Q).toFun b) =
      (Ideal.Quotient.mk Q).toFun (e.toRingHom.toFun b) :=
    Ideal.quotientEquiv_mk Q Q e hmap b
  have hcoeff (c : B) : (maximalQuotientResidueEquiv Q).toRingHom.toFun
        ((Ideal.Quotient.mk Q).toFun c) =
      (algebraMap B Q.ResidueField).toFun c :=
    congrArg (fun f : B →+* Q.ResidueField => f.toFun c)
      (maximalQuotientResidueEquiv_comp_quotient Q)
  have hres : (IsLocalRing.ResidueField.mapEquiv
        (Localization.localRingEquiv Q Q e hQ)).toRingHom.toFun
        ((algebraMap B Q.ResidueField).toFun b) =
      (algebraMap B Q.ResidueField).toFun (e.toRingHom.toFun b) :=
    Ideal.ResidueField.map_algebraMap Q Q e.toRingHom hQ b
  exact (congrArg
    (IsLocalRing.ResidueField.mapEquiv
      (Localization.localRingEquiv Q Q e hQ)).toRingHom.toFun (hcoeff b)).trans
      (hres.trans ((hcoeff (e.toRingHom.toFun b)).symm.trans
        (congrArg (maximalQuotientResidueEquiv Q).toRingHom.toFun hquot.symm)))

end EtaleFundamentalGroups.Inertia

end
