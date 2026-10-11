/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Affine.FlatBaseChangeAffinization
import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Flat base change on sections with the original affine coefficient rings

The scalar maps here are the actual maps from the rings defining the two
affine bases. This comparison is used for residue-field coefficients in
proper-family cohomology, where the original field actions must agree.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Flat R A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable [QuasiCompact f] [QuasiSeparated f]

/-- Flat base change on global sections as a pushout with the given base
rings, and with the actual scalar and pullback maps. -/
theorem isPushout_specPullbackSections :
    IsPushout (CommRingCat.ofHom (algebraMap R A))
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop)
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop := by
  let g : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R A))
  have : Flat g := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  refine (isPushout_appTop_of_flat f g).flip.of_iso
    (Scheme.ΓSpecIso (CommRingCat.of R))
    (Scheme.ΓSpecIso (CommRingCat.of A)) (Iso.refl _) (Iso.refl _)
    ?_ ?_ ?_ ?_
  · exact Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R A))
  · rw [Iso.refl_hom, Iso.hom_inv_id_assoc, Category.comp_id]
  · rw [Iso.refl_hom, Iso.hom_inv_id_assoc, Category.comp_id]
  · exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The global-section tensor comparison retains the original affine base
ring as scalar owner. -/
def specPullbackSectionsTensorEquiv :
    let : Algebra R Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
    let : Algebra A Γ(pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap R A))), ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop).hom.toAlgebra
    A ⊗[R] Γ(X, ⊤) ≃ₐ[A]
      Γ(pullback f (Spec.map (CommRingCat.ofHom (algebraMap R A))), ⊤) := by
  intro hRX hAP
  let e := (CommRingCat.isPushout_tensorProduct R A Γ(X, ⊤)).isoPushout ≪≫
    (isPushout_specPullbackSections (A := A) f).isoPushout.symm
  refine { toRingEquiv := e.commRingCatIsoToRingEquiv, commutes' := ?_ }
  intro a
  change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e.hom) a =
    ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop) a
  congr 2
  simp only [e, Iso.trans_hom, Iso.symm_hom,
    IsPushout.inl_isoPushout_hom_assoc, IsPushout.inl_isoPushout_inv]

/-- The tensor comparison sends the right factor to the actual restriction
from the source scheme. -/
theorem specPullbackSectionsTensorEquiv_one_tmul :
    let : Algebra R Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ f.appTop).hom.toAlgebra
    let : Algebra A Γ(pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap R A))), ⊤) :=
      ((Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop).hom.toAlgebra
    ∀ x : Γ(X, ⊤), specPullbackSectionsTensorEquiv (A := A) f (1 ⊗ₜ[R] x) =
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap R A)))).appTop x := by
  intro hRX hAP x
  change (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫
    ((CommRingCat.isPushout_tensorProduct R A Γ(X, ⊤)).isoPushout ≪≫
      (isPushout_specPullbackSections (A := A) f).isoPushout.symm).hom) x = _
  congr 2
  simp only [Iso.trans_hom, Iso.symm_hom,
    IsPushout.inr_isoPushout_hom_assoc, IsPushout.inr_isoPushout_inv]

end AlgebraicGeometry
