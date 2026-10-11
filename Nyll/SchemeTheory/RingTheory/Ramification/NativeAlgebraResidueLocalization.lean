/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.NativeAlgebraResidueCoefficient
import Nyll.SchemeTheory.RingTheory.Ramification.MaximalQuotientResidueConjugate
import Nyll.SchemeTheory.RingTheory.Ramification.NativeAlgebraResidueEpi
import Nyll.SchemeTheory.RingTheory.Ramification.NativeResidueAction
import Nyll.SchemeTheory.RingTheory.Ramification.MaximalQuotientResidueNaturality
import Nyll.SchemeTheory.RingTheory.Ramification.StabilizerLocalizationAction
import Nyll.SchemeTheory.CategoryTheory.CommAlgRingMap
import Mathlib.RingTheory.Ideal.Quotient.Operations

import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Algebra residue morphisms and localization

Identifies the algebra residue morphism with the quotient automorphism of its coefficient
action. The canonical maximal-quotient equivalence then relates it to the localization residue
map.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

open scoped Pointwise

universe u v

/-- The same native algebra residue morphism induces the quotient of its
actual coefficient automorphism. Its defining coefficient equation is retained. -/
theorem nativeAlgebraResidueMorphism_eq_quotientEquiv
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A)
    (G : Type v) [Group G] [MulSemiringAction G R]
    (Q : Ideal R)
    (hbase : ∀ g : G, (MulSemiringAction.toRingHom G R g).comp
      (commAlgCoefficientMap R) = commAlgCoefficientMap R)
    (d : nativeResidueStabilizer R G Q) :
    nativeAlgebraResidueAutomorphismRingEquiv R Q
        ((nativeAlgebraResidueMorphism R G Q hbase).hom'.toFun d) =
      Ideal.quotientEquiv Q Q (stabilizerCoefficientRingEquiv R G Q d)
        ((congrArg (Ideal.map (stabilizerCoefficientRingEquiv R G Q d).toRingHom)
          (stabilizerCoefficientRingEquiv_comap_eq R G Q d)).trans
          (Ideal.map_comap_eq_self_of_equiv (stabilizerCoefficientRingEquiv R G Q d) Q)).symm := by
  let e : R ≃+* R := stabilizerCoefficientRingEquiv R G Q d
  have he : Q = Q.comap e.toRingHom := stabilizerCoefficientRingEquiv_comap_eq R G Q d
  have hmap : Q = Q.map e.toRingHom :=
    ((congrArg (Ideal.map e.toRingHom) he).trans
      (Ideal.map_comap_eq_self_of_equiv e Q)).symm
  apply RingEquiv.ext
  intro x
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hnative :
      (nativeAlgebraResidueAutomorphismRingEquiv R Q
        ((nativeAlgebraResidueMorphism R G Q hbase).hom'.toFun d)).toRingHom.toFun
        ((Ideal.Quotient.mk Q).toFun b) =
      (Ideal.Quotient.mk Q).toFun (e.toRingHom.toFun b) := rfl
  have hquot : (Ideal.quotientEquiv Q Q e hmap).toRingHom.toFun
        ((Ideal.Quotient.mk Q).toFun b) =
      (Ideal.Quotient.mk Q).toFun (e.toRingHom.toFun b) :=
    Ideal.quotientEquiv_mk Q Q e hmap b
  exact Eq.trans (α := R ⧸ Q) hnative hquot.symm

/-- The same native algebra residue morphism agrees with the actual
localization residue map through the fixed maximal-quotient equivalence. -/
theorem nativeAlgebraResidueMorphism_localization_square
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A)
    (G : Type v) [Group G] [MulSemiringAction G R]
    (Q : Ideal R) [Q.IsMaximal]
    (hbase : ∀ g : G, (MulSemiringAction.toRingHom G R g).comp
      (commAlgCoefficientMap R) = commAlgCoefficientMap R)
    (d : nativeResidueStabilizer R G Q) (x : R ⧸ Q) :
    (IsLocalRing.ResidueField.mapEquiv
        (stabilizerLocalizationRingEquiv R G Q d)).toRingHom.toFun
        ((maximalQuotientResidueEquiv Q).toRingHom.toFun x) =
      (maximalQuotientResidueEquiv Q).toRingHom.toFun
        ((nativeAlgebraResidueAutomorphismRingEquiv R Q
          ((nativeAlgebraResidueMorphism R G Q hbase).hom'.toFun d)).toRingHom.toFun x) := by
  have hnative := nativeAlgebraResidueMorphism_eq_quotientEquiv R G Q hbase d
  have hlocal := maximalQuotientResidueEquiv_naturality Q
    (stabilizerCoefficientRingEquiv R G Q d)
    (stabilizerCoefficientRingEquiv_comap_eq R G Q d) x
  exact hlocal.trans
    (congrArg
      (fun f : (R ⧸ Q) ≃+* (R ⧸ Q) =>
        (maximalQuotientResidueEquiv Q).toRingHom.toFun (f.toRingHom.toFun x)) hnative.symm)

/-- The standard local residue action is the fixed canonical conjugate of
the SAME native algebra residue morphism. -/
theorem nativeAlgebraResidueMorphism_localization_ringHom
    {A : Type u} [CommRing A] (R : CommAlgCat.{v} A)
    (G : Type v) [Group G] [MulSemiringAction G R]
    (Q : Ideal R) [Q.IsMaximal]
    (hbase : ∀ g : G, (MulSemiringAction.toRingHom G R g).comp
      (commAlgCoefficientMap R) = commAlgCoefficientMap R)
    (d : nativeResidueStabilizer R G Q) :
    MulSemiringAction.toRingHom (MulAction.stabilizer G Q) Q.ResidueField d =
      ((maximalQuotientResidueEquiv Q).toRingHom.comp
        (nativeAlgebraResidueAutomorphismRingEquiv R Q
          ((nativeAlgebraResidueMorphism R G Q hbase).hom'.toFun d)).toRingHom).comp
        (maximalQuotientResidueEquiv Q).symm.toRingHom := by
  have hnative := nativeAlgebraResidueMorphism_eq_quotientEquiv R G Q hbase d
  have hlocal := maximalQuotientResidueEquiv_localization_conjugate Q
    (stabilizerCoefficientRingEquiv R G Q d)
    (stabilizerCoefficientRingEquiv_comap_eq R G Q d)
  exact Eq.trans (α := Q.ResidueField →+* Q.ResidueField) hlocal
    (congrArg (fun e : (R ⧸ Q) ≃+* (R ⧸ Q) =>
      ((maximalQuotientResidueEquiv Q).toRingHom.comp e.toRingHom).comp
        (maximalQuotientResidueEquiv Q).symm.toRingHom) hnative.symm)

end EtaleFundamentalGroups.Inertia

end
