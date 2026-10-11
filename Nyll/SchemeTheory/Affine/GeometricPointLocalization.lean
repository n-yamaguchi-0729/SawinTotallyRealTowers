/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.StalkLocalization
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Geometric points of localized étale charts

A prescribed point of a localized stalk in an étale chart admits a geometric
point over any chosen algebraically closed residue-field extension downstairs.
The construction uses the actual residue map of the chart and the isomorphisms
on stalks of localization morphisms, so the resulting triangle commutes as
scheme morphisms.
-/


noncomputable section

open CategoryTheory IsLocalRing

namespace AlgebraicGeometry

universe u

private theorem exists_geometricPoint_of_isIso_stalkMap
    {X U V : Scheme.{u}} (f : U ⟶ X) [Etale f] (h : V ⟶ U) (v : V)
    [IsIso (h.stalkMap v)] (η : X) (hv : f (h v) = η)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (a : X.residueField η ⟶ CommRingCat.of Ω) :
    ∃ t : Spec (CommRingCat.of Ω) ⟶ V,
      t (closedPoint Ω) = v ∧
      t ≫ h ≫ f = Spec.map a ≫ X.fromSpecResidueField η := by
  subst η
  let : Algebra (X.residueField (f (h v))) (U.residueField (h v)) :=
    (f.residueFieldMap (h v)).hom.toAlgebra
  let : Algebra (X.residueField (f (h v))) Ω := a.hom.toAlgebra
  let b : U.residueField (h v) →ₐ[X.residueField (f (h v))] Ω := IsAlgClosed.lift
  have hb : f.residueFieldMap (h v) ≫ CommRingCat.ofHom b.toRingHom = a := by
    apply CommRingCat.hom_ext
    exact b.comp_algebraMap
  let : IsIso (h.residueFieldMap v) :=
    (IsLocalRing.ResidueField.mapEquiv
      (asIso (h.stalkMap v)).commRingCatIsoToRingEquiv).toCommRingCatIso.isIso_hom
  let c : V.residueField v ⟶ CommRingCat.of Ω :=
    inv (h.residueFieldMap v) ≫ CommRingCat.ofHom b.toRingHom
  have hc : h.residueFieldMap v ≫ c = CommRingCat.ofHom b.toRingHom := by
    exact IsIso.hom_inv_id_assoc _ _
  refine ⟨Spec.map c ≫ V.fromSpecResidueField v, ?_, ?_⟩
  · exact V.fromSpecResidueField_apply v _
  · calc
      (Spec.map c ≫ V.fromSpecResidueField v) ≫ h ≫ f =
          Spec.map c ≫ Spec.map (h.residueFieldMap v) ≫
            U.fromSpecResidueField (h v) ≫ f := by
        rw [Category.assoc, ← h.SpecMap_residueFieldMap_fromSpecResidueField_assoc]
      _ = Spec.map (CommRingCat.ofHom b.toRingHom) ≫
          U.fromSpecResidueField (h v) ≫ f := by
        rw [← Spec.map_comp_assoc, hc]
      _ = Spec.map (CommRingCat.ofHom b.toRingHom) ≫
          Spec.map (f.residueFieldMap (h v)) ≫
            X.fromSpecResidueField (f (h v)) := by
        rw [← f.SpecMap_residueFieldMap_fromSpecResidueField]
      _ = Spec.map a ≫ X.fromSpecResidueField (f (h v)) := by
        rw [← Spec.map_comp_assoc]
        exact congrArg (fun k : X.residueField (f (h v)) ⟶ CommRingCat.of Ω =>
          Spec.map k ≫ X.fromSpecResidueField (f (h v))) hb

/-- A point of any localization of a chart stalk lifts the prescribed
geometric point downstairs, with its underlying point unchanged. -/
theorem exists_geometricPoint_localized_stalk
    {X U : Scheme.{u}} (f : U ⟶ X) [Etale f] (u : U)
    (M : Submonoid (U.presheaf.stalk u)) (S : Type u) [CommRing S]
    [Algebra (U.presheaf.stalk u) S] [IsLocalization M S]
    (q : Spec (CommRingCat.of S)) (η : X)
    (hq : f (U.fromSpecStalk u
      ((Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk u) S))) q)) = η)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (a : X.residueField η ⟶ CommRingCat.of Ω) :
    ∃ t : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of S),
      t (closedPoint Ω) = q ∧
      t ≫ Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk u) S)) ≫
        U.fromSpecStalk u ≫ f = Spec.map a ≫ X.fromSpecResidueField η := by
  let l : Spec (CommRingCat.of S) ⟶ Spec (U.presheaf.stalk u) :=
    Spec.map (CommRingCat.ofHom (algebraMap (U.presheaf.stalk u) S))
  let : IsIso (l.stalkMap q) := isIso_stalkMap_SpecMap_of_isLocalization M q
  let : IsIso ((U.fromSpecStalk u).stalkMap (l q)) :=
    U.isIso_fromSpecStalk_stalkMap u (l q)
  let : IsIso ((l ≫ U.fromSpecStalk u).stalkMap q) := by
    rw [Scheme.Hom.stalkMap_comp]
    exact ((asIso ((U.fromSpecStalk u).stalkMap (l q))) ≪≫
      asIso (l.stalkMap q)).isIso_hom
  obtain ⟨t, ht, hcomm⟩ := exists_geometricPoint_of_isIso_stalkMap
    f (l ≫ U.fromSpecStalk u) q η hq Ω a
  refine ⟨t, ht, ?_⟩
  exact (congrArg (fun k : Spec (CommRingCat.of S) ⟶ X => t ≫ k)
    (Category.assoc l (U.fromSpecStalk u) f)).symm.trans hcomm

/-- The extension of a chosen chart branch to a prime localization carries a
geometric point over the fixed geometric point downstairs. The prime itself
and its inverse image are supplied by localization of the given inclusion. -/
theorem exists_geometricPoint_localized_chart_branch
    {X U : Scheme.{u}} (f : U ⟶ X) [Etale f] (u : U)
    (q : Spec (U.presheaf.stalk u)) (P : Ideal (U.presheaf.stalk u)) [P.IsPrime]
    (hqP : q.asIdeal ≤ P) (η : X) (hqη : f (U.fromSpecStalk u q) = η)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (a : X.residueField η ⟶ CommRingCat.of Ω) :
    ∃ t : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of (Localization.AtPrime P)),
      (t (closedPoint Ω)).asIdeal =
        q.asIdeal.map (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P)) ∧
      t ≫ Spec.map (CommRingCat.ofHom
          (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P))) ≫
        U.fromSpecStalk u ≫ f = Spec.map a ≫ X.fromSpecResidueField η := by
  let : q.asIdeal.IsPrime := q.isPrime
  let Q : Spec (CommRingCat.of (Localization.AtPrime P)) :=
    ⟨q.asIdeal.map (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P)),
      Ideal.isPrime_map_of_isLocalizationAtPrime P hqP⟩
  have hQ : (Spec.map (CommRingCat.ofHom
      (algebraMap (U.presheaf.stalk u) (Localization.AtPrime P)))) Q = q := by
    apply PrimeSpectrum.ext
    exact Ideal.under_map_of_isLocalizationAtPrime P hqP
  obtain ⟨t, ht, hcomm⟩ := exists_geometricPoint_localized_stalk
    f u P.primeCompl (Localization.AtPrime P) Q η (by rw [hQ]; exact hqη) Ω a
  exact ⟨t, congrArg PrimeSpectrum.asIdeal ht, hcomm⟩

end AlgebraicGeometry
