/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Stalks of localization morphisms

The canonical map from the spectrum of an arbitrary model of a localization
has isomorphic stalk maps.  Mathlib contains this for the quotient-type
`Localization M`; the statement below removes that representation choice.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- The stalk map of `Spec S ⟶ Spec R` is an isomorphism when `S` is a
localization of `R`, independently of the chosen localization model. -/
theorem isIso_stalkMap_SpecMap_of_isLocalization
    {R S : CommRingCat.{u}} (M : Submonoid R)
    [Algebra R S] [IsLocalization M S]
    (x : PrimeSpectrum S) :
    IsIso ((Spec.map (CommRingCat.ofHom (algebraMap R S))).stalkMap x) := by
  erw [← Scheme.localRingHom_comp_stalkIso,
    ConcreteCategory.isIso_iff_bijective]
  dsimp
  let T := Localization.AtPrime x.asIdeal
  let p := x.asIdeal.comap (algebraMap R S)
  let : IsLocalization.AtPrime T p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      M T x.asIdeal
  let e : Localization.AtPrime p ≃ₐ[R] T :=
    IsLocalization.algEquiv p.primeCompl _ _
  have heq :
      Localization.localRingHom p x.asIdeal (algebraMap R S) rfl =
        e.toRingEquiv.toRingHom := by
    apply IsLocalization.ringHom_ext p.primeCompl
    ext r
    simp only [RingHom.comp_apply, Localization.localRingHom_to_map]
    change (algebraMap S T) ((algebraMap R S) r) =
      e ((algebraMap R (Localization.AtPrime p)) r)
    rw [e.commutes r]
    exact (IsScalarTower.algebraMap_apply R S T r).symm
  rw [heq]
  exact
    (ConcreteCategory.bijective_of_isIso (Spec.stalkIso S x).inv).comp
      (e.bijective.comp
        (ConcreteCategory.bijective_of_isIso
          (Spec.stalkIso R (x.comap (algebraMap R S))).hom))

/-- Every stalk map of the canonical morphism from the spectrum of a stalk,
computed inside a chosen affine neighbourhood, is an isomorphism. -/
theorem IsAffineOpen.isIso_fromSpecStalk_stalkMap
    {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    IsIso ((hU.fromSpecStalk hx).stalkMap p) := by
  erw [IsAffineOpen.fromSpecStalk, Scheme.Hom.stalkMap_comp]
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hx).hom.toAlgebra
  let := hU.isLocalization_stalk ⟨x, hx⟩
  have hlocal : IsIso
      ((Spec.map (X.presheaf.germ U x hx)).stalkMap p) :=
    isIso_stalkMap_SpecMap_of_isLocalization
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl p
  have hopen : IsIso
      (hU.fromSpec.stalkMap ((Spec.map (X.presheaf.germ U x hx)) p)) :=
    inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _
    (hU.fromSpec.stalkMap ((Spec.map (X.presheaf.germ U x hx)) p))
    ((Spec.map (X.presheaf.germ U x hx)).stalkMap p) hopen hlocal

/-- Every stalk map of the canonical morphism `Spec 𝒪_{X,x} ⟶ X` is an
isomorphism.  Equivalently, the local ring at a generalization of `x` is the
corresponding prime localization of `𝒪_{X,x}`. -/
theorem Scheme.isIso_fromSpecStalk_stalkMap
    (X : Scheme.{u}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    IsIso ((X.fromSpecStalk x).stalkMap p) := by
  let f := X.affineCover.f (X.affineCover.idx x)
  let U := f.opensRange
  let hU : IsAffineOpen U := isAffineOpen_opensRange f
  let hx : x ∈ U := X.affineCover.covers x
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
  exact hU.isIso_fromSpecStalk_stalkMap x hx p

/-- The local ring at the image of a prime of `𝒪_{X,x}` is canonically
isomorphic to the localization of `𝒪_{X,x}` at that prime. -/
noncomputable def Scheme.stalkFromSpecStalkEquivLocalization
    (X : Scheme.{u}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.presheaf.stalk (X.fromSpecStalk x p) ≃+*
      Localization.AtPrime p.asIdeal := by
  letI := X.isIso_fromSpecStalk_stalkMap x p
  exact ((asIso ((X.fromSpecStalk x).stalkMap p)) ≪≫
    Spec.stalkIso (X.presheaf.stalk x) p).commRingCatIsoToRingEquiv

/-- The dimension of the local ring at the point represented by `p` in
`Spec 𝒪_{X,x}` is the height of `p`. -/
theorem Scheme.ringKrullDim_stalk_fromSpecStalk_eq_height
    (X : Scheme.{u}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    ringKrullDim (X.presheaf.stalk (X.fromSpecStalk x p)) =
      p.asIdeal.height := by
  rw [ringKrullDim_eq_of_ringEquiv
    (X.stalkFromSpecStalkEquivLocalization x p)]
  exact IsLocalization.AtPrime.ringKrullDim_eq_height
    p.asIdeal (Localization.AtPrime p.asIdeal)

/-- The residue field at a point represented in the spectrum of a stalk is
canonically the residue field of the corresponding prime of that stalk. -/
noncomputable def Scheme.residueFieldFromSpecStalkEquiv
    (X : Scheme.{u}) (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    X.residueField (X.fromSpecStalk x p) ≃+* p.asIdeal.ResidueField := by
  exact IsLocalRing.ResidueField.mapEquiv
    (X.stalkFromSpecStalkEquivLocalization x p)

end AlgebraicGeometry

end
