/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.SchemeTheory.Etale.IsomorphismNeighborhood
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Sections over neighborhoods of a finite base

A neighborhood containing a fiber of a closed morphism contains the inverse
image of a neighborhood on the base. Applied to the isomorphism neighborhood
of a finite étale morphism, this constructs a section over a neighborhood on
the base of a finite universally injective morphism.
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- The idempotent supplied by the étale local structure theorem gives an
actual finite open factor with a singleton fiber. The point of this factor
maps to the prescribed prime of the original algebra, and the residue field
of the chosen point on the étale base is unchanged. -/
theorem exists_etale_finite_factor_of_quasiFiniteAt
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal S) [q.IsPrime] [q.LiesOver p] [Algebra.QuasiFiniteAt R q] :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (P : Ideal R') (_ : P.IsPrime) (_ : P.LiesOver p)
      (e : R' ⊗[R] S) (_ : IsIdempotentElem e),
      Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)) ∧
      Module.Finite R' (Localization.Away e) ∧
      IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away e)))) ∧
      IsOpenImmersion (Spec.map (CommRingCat.ofHom
        (algebraMap (R' ⊗[R] S) (Localization.Away e)))) ∧
      ∃ z : Spec (CommRingCat.of (Localization.Away e)),
        Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away e))) z =
          ⟨P, inferInstance⟩ ∧
        (Spec.map (CommRingCat.ofHom (algebraMap (R' ⊗[R] S) (Localization.Away e))) ≫
          Spec.map (CommRingCat.ofHom
            (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom)) z =
          (⟨q, inferInstance⟩ : Spec (CommRingCat.of S)) ∧
        ∀ z' : Spec (CommRingCat.of (Localization.Away e)),
          Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away e))) z' =
            ⟨P, inferInstance⟩ → z' = z := by
  obtain ⟨R', _, _, _, P, hP, _, e, he, P', hP', _, hP'q, heP', hκ, hfinite, huniq⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
  let : P.IsPrime := hP
  let : P'.IsPrime := hP'
  let : Module.Finite R' (Localization.Away e) := hfinite
  have hfiniteSpec : IsFinite
      (Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away e)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr hfinite)
  have hmem : (⟨P', hP'⟩ : PrimeSpectrum (R' ⊗[R] S)) ∈
      Set.range (PrimeSpectrum.comap (algebraMap (R' ⊗[R] S) (Localization.Away e))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away e) e]
    exact heP'
  obtain ⟨z, hz⟩ := hmem
  have hzP : Spec.map (CommRingCat.ofHom (algebraMap R' (Localization.Away e))) z =
      (⟨P, hP⟩ : Spec (CommRingCat.of R')) := by
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap R' (Localization.Away e)) z.asIdeal = P
    have hzIdeal : z.asIdeal.comap
        (algebraMap (R' ⊗[R] S) (Localization.Away e)) = P' :=
      congrArg PrimeSpectrum.asIdeal hz
    rw [IsScalarTower.algebraMap_eq R' (R' ⊗[R] S) (Localization.Away e),
      ← Ideal.comap_comap, hzIdeal]
    exact (P'.over_def P).symm
  refine ⟨R', inferInstance, inferInstance, inferInstance, P, hP, inferInstance,
    e, he, hκ, hfinite, hfiniteSpec, inferInstance, z, hzP, ?_, ?_⟩
  · change PrimeSpectrum.comap
        (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S).toRingHom
        (PrimeSpectrum.comap (algebraMap (R' ⊗[R] S) (Localization.Away e)) z) = _
    rw [hz]
    exact PrimeSpectrum.ext hP'q
  · intro z' hz'P
    let Q : Ideal (R' ⊗[R] S) :=
      z'.asIdeal.comap (algebraMap (R' ⊗[R] S) (Localization.Away e))
    let : z'.asIdeal.IsPrime := z'.isPrime
    let : Q.IsPrime := Ideal.comap_isPrime _ _
    let : Q.LiesOver P := ⟨by
      change P = Ideal.comap (algebraMap R' (R' ⊗[R] S))
        (Ideal.comap (algebraMap (R' ⊗[R] S) (Localization.Away e)) z'.asIdeal)
      rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq]
      exact (congrArg PrimeSpectrum.asIdeal hz'P).symm⟩
    have heQ : e ∉ Q := by
      have hr : PrimeSpectrum.comap (algebraMap (R' ⊗[R] S) (Localization.Away e)) z' ∈
          Set.range (PrimeSpectrum.comap (algebraMap (R' ⊗[R] S) (Localization.Away e))) :=
        ⟨z', rfl⟩
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away e) e] at hr
      exact hr
    apply PrimeSpectrum.localization_comap_injective (Localization.Away e) (Submonoid.powers e)
    rw [hz]
    exact PrimeSpectrum.ext (huniq Q inferInstance inferInstance heQ)

/-- A neighborhood containing a whole fiber of a universally closed morphism
contains the inverse image of an open neighborhood of the base point. -/
theorem Scheme.Hom.exists_preimage_le_of_fiber_subset
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversallyClosed f]
    (y : Y) (U : X.Opens) (hU : ∀ x : X, f x = y → x ∈ U) :
    ∃ V : Y.Opens, y ∈ V ∧ f ⁻¹ᵁ V ≤ U := by
  let V : Y.Opens :=
    ⟨(f '' (U : Set X)ᶜ)ᶜ, (f.isClosedMap _ U.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  · rintro ⟨x, hx, hxy⟩
    exact hx (hU x hxy)
  · intro x hx
    by_contra hxU
    exact hx ⟨x, hxU, rfl⟩

/-- A finite étale morphism with a singleton fiber and purely inseparable
residue extension has a section over the inverse image of a neighborhood on a finite
universally injective base. The section passes through the specified point. -/
theorem Etale.exists_section_over_finite_base_neighborhood
    {U X Y : Scheme.{u}} (p : U ⟶ X) (f : X ⟶ Y)
    [IsFinite p] [Etale p] [IsFinite f] [UniversallyInjective f]
    (u : U) (hu : ∀ u' : U, p u' = p u → u' = u)
    (hκ : (p.residueFieldMap u).hom.IsPurelyInseparable) :
    ∃ (V : Y.Opens) (hV : f (p u) ∈ V)
      (s : (f ⁻¹ᵁ V).toScheme ⟶ U),
      s ≫ p = (f ⁻¹ᵁ V).ι ∧ s ⟨p u, hV⟩ = u := by
  obtain ⟨T, huT, hT⟩ :=
    Etale.exists_isIso_restrict_of_unique_preimage_of_isPurelyInseparable p u hu hκ
  let : IsIso (p ∣_ T) := hT
  obtain ⟨V, hV, hVT⟩ := f.exists_preimage_le_of_fiber_subset (f (p u)) T
    (fun x hx ↦ (f.injective hx).symm ▸ huT)
  let s : (f ⁻¹ᵁ V).toScheme ⟶ U :=
    X.homOfLE hVT ≫ inv (p ∣_ T) ≫ (p ⁻¹ᵁ T).ι
  have hs : s ≫ p = (f ⁻¹ᵁ V).ι := by
    dsimp only [s]
    rw [Category.assoc, Category.assoc, ← morphismRestrict_ι,
      IsIso.inv_hom_id_assoc, Scheme.homOfLE_ι]
  refine ⟨V, hV, s, hs, hu _ ?_⟩
  exact congrArg (fun k : (f ⁻¹ᵁ V).toScheme ⟶ X ↦ k ⟨p u, hV⟩) hs

end AlgebraicGeometry
