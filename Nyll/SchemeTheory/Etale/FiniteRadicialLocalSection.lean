/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.AffineResidueField
public import Nyll.SchemeTheory.Etale.FiniteNeighborhoodSection
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.RingHom.Etale

/-!
# Affine local sections over a finite radicial base

The chosen-residue-extension construction supplies pure inseparability over
the bottom ring, rather than over the intervening finite radicial algebra.
The residue-field tower transfers this property to the étale morphism. A
singleton fiber then gives a section over the inverse image of an actual
open neighborhood on the bottom affine scheme.

This is internal support for Stacks Tag `0BQN`. The singleton-fiber input is
the local finite factor to be supplied by
`exists_etale_finite_factor_of_quasiFiniteAt`; this result does not assert
the existence of the entire étale covering family or effective object descent.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

private theorem residueFieldMap_isPurelyInseparable_of_comp
    {U X Y : Scheme.{u}} (p : U ⟶ X) (f : X ⟶ Y) (u : U)
    (hκ : ((p ≫ f).residueFieldMap u).hom.IsPurelyInseparable) :
    (p.residueFieldMap u).hom.IsPurelyInseparable := by
  let : Algebra (Y.residueField (f (p u))) (X.residueField (p u)) :=
    (f.residueFieldMap (p u)).hom.toAlgebra
  let : Algebra (X.residueField (p u)) (U.residueField u) :=
    (p.residueFieldMap u).hom.toAlgebra
  let : Algebra (Y.residueField (f (p u))) (U.residueField u) :=
    ((p ≫ f).residueFieldMap u).hom.toAlgebra
  let : IsScalarTower (Y.residueField (f (p u)))
      (X.residueField (p u)) (U.residueField u) :=
    IsScalarTower.of_algebraMap_eq'
      (congrArg CommRingCat.Hom.hom (Scheme.residueFieldMap_comp p f u))
  let : IsPurelyInseparable (Y.residueField (f (p u))) (U.residueField u) := hκ
  exact IsPurelyInseparable.tower_top (Y.residueField (f (p u)))
    (X.residueField (p u)) (U.residueField u)

/-- The ring-theoretic residue extension at a finite local factor supplies
an actual scheme section over a neighborhood on the finite radicial base.
Only the composite residue extension from the bottom ring is needed. -/
theorem Etale.exists_affine_section_over_finite_radicial_neighborhood
    {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]
    [Algebra R S] [Algebra S A] [Module.Finite R S] [Module.Finite S A]
    [Algebra.Etale S A]
    [UniversallyInjective (Spec.map (CommRingCat.ofHom (algebraMap R S)))]
    (q : PrimeSpectrum A)
    (hq : ∀ q' : PrimeSpectrum A,
      PrimeSpectrum.comap (algebraMap S A) q' =
        PrimeSpectrum.comap (algebraMap S A) q → q' = q)
    (hκ : letI : q.asIdeal.IsPrime := q.isPrime
      letI : (PrimeSpectrum.comap
        ((algebraMap S A).comp (algebraMap R S)) q).asIdeal.IsPrime :=
          (PrimeSpectrum.comap ((algebraMap S A).comp (algebraMap R S)) q).isPrime
      (Ideal.ResidueField.map
      (PrimeSpectrum.comap ((algebraMap S A).comp (algebraMap R S)) q).asIdeal
      q.asIdeal ((algebraMap S A).comp (algebraMap R S)) rfl).IsPurelyInseparable) :
    ∃ (V : (Spec (CommRingCat.of R)).Opens)
      (hV : PrimeSpectrum.comap (algebraMap R S)
        (PrimeSpectrum.comap (algebraMap S A) q) ∈ V)
      (s : ((Spec.map (CommRingCat.ofHom (algebraMap R S))) ⁻¹ᵁ V).toScheme ⟶
        Spec (CommRingCat.of A)),
      s ≫ Spec.map (CommRingCat.ofHom (algebraMap S A)) =
        ((Spec.map (CommRingCat.ofHom (algebraMap R S))) ⁻¹ᵁ V).ι ∧
      s ⟨PrimeSpectrum.comap (algebraMap S A) q, hV⟩ = q := by
  let p : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of S) :=
    Spec.map (CommRingCat.ofHom (algebraMap S A))
  let f : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R) :=
    Spec.map (CommRingCat.ofHom (algebraMap R S))
  let : IsFinite p :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  let : Etale p :=
    (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
      (RingHom.etale_algebraMap.mpr inferInstance)
  let : IsFinite f :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  have hκcomp : ((p ≫ f).residueFieldMap q).hom.IsPurelyInseparable := by
    change ((Spec.map (CommRingCat.ofHom (algebraMap S A)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R S))).residueFieldMap q).hom.IsPurelyInseparable
    rw [← Spec.map_comp]
    exact (Scheme.Spec.residueFieldMap_isPurelyInseparable_iff
      (CommRingCat.ofHom ((algebraMap S A).comp (algebraMap R S))) q).mpr hκ
  exact Etale.exists_section_over_finite_base_neighborhood p f q hq
    (residueFieldMap_isPurelyInseparable_of_comp p f q hκcomp)

end AlgebraicGeometry
