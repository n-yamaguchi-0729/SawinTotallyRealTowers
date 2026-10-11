/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.Functoriality
import Mathlib.AlgebraicGeometry.Stalk

/-!
# Function fields of morphisms factoring through a stalk spectrum

An injective map out of an integral scheme's stalk gives a dominant
morphism from the spectrum of its target back to the scheme.  The induced
function-field map restricts to the original ring map on that stalk.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

private theorem eqToHom_stalk_eq_stalkCongr
    (Z : Scheme.{u}) {z z' : Z} (h : z = z') :
    eqToHom (congrArg (fun w ↦ Z.presheaf.stalk w) h) =
      (Z.presheaf.stalkCongr (.of_eq h)).hom := by
  subst z'
  simp

private theorem SpecMap_genericPoint_of_injective
    {R S : CommRingCat.{u}} [IsDomain R] [IsDomain S]
    (phi : R ⟶ S) (hphi : Function.Injective phi) :
    Spec.map phi (genericPoint (Spec S)) = genericPoint (Spec R) := by
  rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
  apply PrimeSpectrum.ext
  change Ideal.comap phi.hom (⊥ : Ideal S) = (⊥ : Ideal R)
  exact Ideal.comap_bot_of_injective phi.hom hphi

private theorem fromSpecStalk_genericPoint_eq
    {X : Scheme.{u}} [IsIntegral X] (x : X) :
    X.fromSpecStalk x (genericPoint (Spec (X.presheaf.stalk x))) =
      genericPoint X := by
  let h := genericPoint_specializes x
  let K := X.functionField
  have hK : genericPoint (Spec K) = IsLocalRing.closedPoint K := by
    apply PrimeSpectrum.ext
    rw [genericPoint_eq_bot_of_affine]
    exact IsLocalRing.maximalIdeal_eq_bot.symm
  have hmap : Spec.map (X.presheaf.stalkSpecializes h)
      (genericPoint (Spec K)) =
      genericPoint (Spec (X.presheaf.stalk x)) := by
    apply SpecMap_genericPoint_of_injective
    change Function.Injective
      (algebraMap (X.presheaf.stalk x) X.functionField)
    exact IsFractionRing.injective (X.presheaf.stalk x) X.functionField
  have hcomp := X.SpecMap_stalkSpecializes_fromSpecStalk h
  have happ := congrArg (fun g ↦ g (genericPoint (Spec K))) hcomp
  change X.fromSpecStalk x
      (Spec.map (X.presheaf.stalkSpecializes h) (genericPoint (Spec K))) =
    X.fromSpecStalk (genericPoint X) (genericPoint (Spec K)) at happ
  rw [hmap, hK, X.fromSpecStalk_closedPoint] at happ
  exact happ

/-- An injective map from a stalk of an integral scheme defines a dominant
morphism from the target spectrum back to the scheme. -/
theorem denseRange_specMap_comp_fromSpecStalk_of_injective
    {X : Scheme.{u}} [IsIntegral X] (x : X)
    {S : Type u} [CommRing S] [IsDomain S]
    (phi : X.presheaf.stalk x →+* S) (hphi : Function.Injective phi) :
    DenseRange
      (Spec.map (CommRingCat.ofHom phi) ≫ X.fromSpecStalk x) := by
  have hgeneric :
      (Spec.map (CommRingCat.ofHom phi) ≫ X.fromSpecStalk x)
          (genericPoint (Spec (.of S))) = genericPoint X := by
    change X.fromSpecStalk x
      (Spec.map (CommRingCat.ofHom phi)
        (genericPoint (Spec (.of S)))) = genericPoint X
    rw [SpecMap_genericPoint_of_injective _ hphi]
    exact fromSpecStalk_genericPoint_eq x
  rw [DenseRange, dense_iff_closure_eq]
  apply Set.Subset.antisymm
  · exact Set.subset_univ _
  · rw [← (genericPoint_spec X).def]
    apply closure_mono
    rintro _ rfl
    exact ⟨genericPoint (Spec (.of S)), hgeneric⟩

/-- The function-field map of a morphism presented by an injective map out
of a stalk restricts to that ring map, followed by the canonical map to the
target fraction field. -/
theorem functionFieldMap_comp_stalkFunctionField_of_injective
    {X : Scheme.{u}} [IsIntegral X] (x : X)
    {S : Type u} [CommRing S] [IsDomain S]
    (phi : X.presheaf.stalk x →+* S) (hphi : Function.Injective phi) :
    let g := Spec.map (CommRingCat.ofHom phi) ≫ X.fromSpecStalk x
    let hg : DenseRange g :=
      denseRange_specMap_comp_fromSpecStalk_of_injective x phi hphi
    letI : Algebra S (Spec (.of S)).functionField :=
      AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of S)
    (g.functionFieldMap hg).comp
        (algebraMap (X.presheaf.stalk x) X.functionField) =
      (algebraMap S (Spec (.of S)).functionField).comp phi := by
  dsimp only
  let : Algebra S (Spec (.of S)).functionField :=
    AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (.of S)
  let g : Spec (.of S) ⟶ X :=
    Spec.map (CommRingCat.ofHom phi) ≫ X.fromSpecStalk x
  let hg : DenseRange g :=
    denseRange_specMap_comp_fromSpecStalk_of_injective x phi hphi
  have hgeneric : g (genericPoint (Spec (.of S))) = genericPoint X :=
    g.map_genericPoint_of_denseRange hg
  let lhs : X.presheaf.stalk x →+* (Spec (.of S)).functionField :=
    (g.functionFieldMap hg).comp
      (algebraMap (X.presheaf.stalk x) X.functionField)
  let rhs : X.presheaf.stalk x →+* (Spec (.of S)).functionField :=
    (algebraMap S (Spec (.of S)).functionField).comp phi
  change lhs = rhs
  have hspec : Spec.map (CommRingCat.ofHom lhs) =
      Spec.map (CommRingCat.ofHom rhs) := by
    apply (cancel_mono (X.fromSpecStalk x)).mp
    dsimp only [lhs, rhs]
    rw [show
      CommRingCat.ofHom
          ((g.functionFieldMap hg).comp
              (algebraMap (X.presheaf.stalk x) X.functionField)) =
        CommRingCat.ofHom
            (algebraMap (X.presheaf.stalk x) X.functionField) ≫
          CommRingCat.ofHom (g.functionFieldMap hg) by rfl]
    rw [show
      CommRingCat.ofHom
          ((algebraMap S (Spec (.of S)).functionField).comp phi) =
        CommRingCat.ofHom phi ≫
          CommRingCat.ofHom
            (algebraMap S (Spec (.of S)).functionField) by rfl]
    rw [Spec.map_comp, Spec.map_comp]
    simp only [Category.assoc]
    rw [show
      CommRingCat.ofHom
          (algebraMap (X.presheaf.stalk x) X.functionField) =
        X.presheaf.stalkSpecializes (genericPoint_specializes x) by rfl]
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rw [show
      Spec.map (CommRingCat.ofHom
          (algebraMap S (Spec (.of S)).functionField)) =
        (Spec (.of S)).fromSpecStalk (genericPoint (Spec (.of S))) from
      (Spec.fromSpecStalk_eq' (.of S) (genericPoint (Spec (.of S)))).symm]
    unfold functionFieldMap
    rw [show
      CommRingCat.ofHom
          (CommRingCat.Hom.hom
            (eqToHom _ ≫
              g.stalkMap (genericPoint (Spec (.of S))))) =
        eqToHom _ ≫
          g.stalkMap (genericPoint (Spec (.of S))) by rfl]
    rw [Spec.map_comp]
    simp only [Category.assoc]
    rw [eqToHom_stalk_eq_stalkCongr]
    all_goals try exact hgeneric.symm
    dsimp only [TopCat.Presheaf.stalkCongr]
    change Spec.map (g.stalkMap (genericPoint (Spec (.of S)))) ≫
      Spec.map (X.presheaf.stalkSpecializes (specializes_of_eq hgeneric)) ≫
        X.fromSpecStalk (genericPoint X) = _
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
  have hhom :
      CommRingCat.Hom.hom (CommRingCat.ofHom lhs) =
        CommRingCat.Hom.hom (CommRingCat.ofHom rhs) :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective hspec)
  exact hhom

end AlgebraicGeometry.Scheme.Hom

end
