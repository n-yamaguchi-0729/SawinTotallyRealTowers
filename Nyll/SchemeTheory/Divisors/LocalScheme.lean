/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.CategoryTheory.ConcreteCategory.Basic
import Mathlib.CategoryTheory.Iso
import Nyll.SchemeTheory.Affine.StalkLocalization
import Nyll.SchemeTheory.Divisors.ArithmeticBoundaryEtale

/-!
# Divisors on spectra of local rings

This file relates the support of an ideal sheaf near a scheme point to prime
ideals of its local ring.  It contains the point-level bridge used when a
codimension-two localization is selected inside a local ramification
argument.
-/

noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}}

/-- A prime of `𝒪_{X,x}` containing the stalk ideal represents a point of the
support under the canonical morphism `Spec 𝒪_{X,x} ⟶ X`. -/
theorem mem_support_fromSpecStalk_of_stalkIdeal_le
    (I : X.IdealSheafData) (x : X)
    (p : Spec (X.presheaf.stalk x))
    (hp : I.stalkIdeal x ≤ p.asIdeal) :
    X.fromSpecStalk x p ∈ I.support := by
  let f := X.affineCover.f (X.affineCover.idx x)
  let U := f.opensRange
  let hU : IsAffineOpen U := isAffineOpen_opensRange f
  let hx : x ∈ U := X.affineCover.covers x
  let q : PrimeSpectrum Γ(X, U) :=
    Spec.map (X.presheaf.germ U x hx) p
  have hq : q ∈ PrimeSpectrum.zeroLocus
      (I.ideal ⟨U, hU⟩ : Set Γ(X, U)) := by
    rw [PrimeSpectrum.mem_zeroLocus]
    intro a ha
    apply hp
    apply I.map_ideal_le_stalkIdeal x ⟨U, hU⟩ hx
    exact Ideal.mem_map_of_mem _ ha
  have hq' : hU.fromSpec q ∈
      X.zeroLocus (I.ideal ⟨U, hU⟩ : Set Γ(X, U)) := by
    exact (Set.ext_iff.mp
      (hU.fromSpec_preimage_zeroLocus
        (I.ideal ⟨U, hU⟩ : Set Γ(X, U))) q).mpr hq
  have hqU : hU.fromSpec q ∈ U := by
    change (hU.isoSpec.inv q).1 ∈ U
    exact (hU.isoSpec.inv q).2
  have hsupport : hU.fromSpec q ∈ I.support :=
    (I.mem_support_iff_of_mem hqU).mpr hq'
  have heq : X.fromSpecStalk x p = hU.fromSpec q := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
    rfl
  rwa [heq]

/-- Under the canonical identification of the stalk at a point of
`Spec 𝒪_{X,x}` with a prime localization, the divisor stalk ideal is exactly
the extension of the stalk ideal at `x`. -/
theorem map_stalkIdeal_stalkFromSpecStalkEquivLocalization
    (I : X.IdealSheafData) (x : X)
    (p : Spec (X.presheaf.stalk x)) :
    (I.stalkIdeal (X.fromSpecStalk x p)).map
        (X.stalkFromSpecStalkEquivLocalization x p).toRingHom =
      (I.stalkIdeal x).map
        (algebraMap (X.presheaf.stalk x)
          (@Localization.AtPrime (X.presheaf.stalk x) _
             (p : PrimeSpectrum (X.presheaf.stalk x)).asIdeal
             (PrimeSpectrum.isPrime (p : PrimeSpectrum (X.presheaf.stalk x))))) := by
  let f := X.affineCover.f (X.affineCover.idx x)
  let U := f.opensRange
  let hU : IsAffineOpen U := isAffineOpen_opensRange f
  let hx : x ∈ U := X.affineCover.covers x
  let q : PrimeSpectrum Γ(X, U) :=
    Spec.map (X.presheaf.germ U x hx) p
  have hy : X.fromSpecStalk x p ∈ U := by
    rw [← hU.fromSpecStalk_eq_fromSpecStalk hx]
    change (hU.isoSpec.inv q).1 ∈ U
    exact (hU.isoSpec.inv q).2
  rw [stalkIdeal_eq_map_ideal I (X.fromSpecStalk x p) ⟨U, hU⟩ hy,
    stalkIdeal_eq_map_ideal I x ⟨U, hU⟩ hx,
    Ideal.map_map, Ideal.map_map]
  congr 1
  ext a
  change (Spec.stalkIso (X.presheaf.stalk x) p).hom
      ((X.fromSpecStalk x).stalkMap p
        (X.presheaf.germ U (X.fromSpecStalk x p) hy a)) = _
  rw [Scheme.Hom.germ_stalkMap_apply]
  simp only [Scheme.fromSpecStalk_app hx, Scheme.ΓSpecIso_inv_naturality_assoc,
    CommRingCat.comp_apply]
  erw [TopCat.Presheaf.germ_res_apply]
  erw [← CommRingCat.comp_apply, Spec.germ_stalkMapIso_hom,
    CommRingCat.comp_apply]
  have hnat := ConcreteCategory.congr_hom
    (Scheme.ΓSpecIso_naturality (X.presheaf.germ U x hx))
    ((Scheme.ΓSpecIso Γ(X, U)).inv a)
  have hunit := ConcreteCategory.congr_hom (Scheme.ΓSpecIso Γ(X, U)).inv_hom_id a
  simp only [CommRingCat.comp_apply, CommRingCat.id_apply] at hnat hunit
  exact congrArg
    (algebraMap (X.presheaf.stalk x)
      (@Localization.AtPrime (X.presheaf.stalk x) _
        (p : PrimeSpectrum (X.presheaf.stalk x)).asIdeal
        (PrimeSpectrum.isPrime (p : PrimeSpectrum (X.presheaf.stalk x)))))
    (hnat.trans (congrArg (fun b : Γ(X, U) => X.presheaf.germ U x hx b) hunit))

end AlgebraicGeometry.Scheme.IdealSheafData

end
