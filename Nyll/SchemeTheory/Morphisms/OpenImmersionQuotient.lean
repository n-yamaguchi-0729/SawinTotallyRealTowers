/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.RingTheory.QuotientBaseChange
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Open immersions after quotient base change

The literal map `R / I → S / I S` is the base change of a ring map `R → S`.
Its pushout square is obtained from the tensor-product pushout and the
canonical quotient/tensor-product equivalence. Consequently its spectrum
is an open immersion whenever the original spectrum map is.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

universe u v

namespace CommRingCat

/-- Extension of an ideal gives the canonical pushout square of quotient
ring maps. -/
theorem isPushout_quotientMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) :
    IsPushout (ofHom f) (ofHom (Ideal.Quotient.mk I))
      (ofHom (Ideal.Quotient.mk (I.map f)))
      (ofHom (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)) := by
  let : Algebra R S := f.toAlgebra
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).toRingEquiv
  refine (isPushout_tensorProduct R S (R ⧸ I)).of_iso'
    (Iso.refl _) (Iso.refl _) (Iso.refl _) e.toCommRingCatIso ?_ ?_ ?_ ?_
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]
  · ext s
    rfl
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change (1 : S) ⊗ₜ[R] (Ideal.Quotient.mk I r) =
      f r ⊗ₜ[R] (1 : R ⧸ I)
    exact (Algebra.TensorProduct.includeRight : (R ⧸ I) →ₐ[R]
      S ⊗[R] (R ⧸ I)).commutes r

end CommRingCat

namespace AlgebraicGeometry

/-- The canonical quotient square becomes a pullback square on spectra. -/
theorem isPullback_SpecMap_quotientMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) :
    IsPullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.map f))))
      (Spec.map (CommRingCat.ofHom
        (Ideal.quotientMap (I.map f) f Ideal.le_comap_map)))
      (Spec.map (CommRingCat.ofHom f))
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_quotientMap f I)

/-- Open immersions remain open immersions under the literal quotient map. -/
theorem isOpenImmersion_SpecMap_quotientMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap (I.map f) f Ideal.le_comap_map))) :=
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (isPullback_SpecMap_quotientMap f I) inferInstance

/-- The same result with the extended ideal written using a chosen equal ideal. -/
theorem isOpenImmersion_SpecMap_quotientMap_of_map_eq
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (J : Ideal S) (hJ : I.map f = J)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (Ideal.quotientMap J f (hJ ▸ Ideal.le_comap_map)))) := by
  subst J
  exact isOpenImmersion_SpecMap_quotientMap f I

/-- Reduction by an ideal in a common scalar ring preserves an open immersion
for the canonical quotient-base algebra map. -/
theorem isOpenImmersion_SpecMap_quotientBaseChange
    {R : Type v} {A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (I : Ideal R)
    [IsOpenImmersion (Spec.map (CommRingCat.ofHom f.toRingHom))] :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (f.quotientBaseChange I).toRingHom)) :=
  isOpenImmersion_SpecMap_quotientMap_of_map_eq f.toRingHom
    (I.map (algebraMap R A)) (I.map (algebraMap R B)) (f.map_extendedIdeal I)

end AlgebraicGeometry
