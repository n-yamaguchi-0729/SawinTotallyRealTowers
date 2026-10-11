/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Unramified.LocalStructure

/-!
# Pointed etale neighborhoods of Henselian local rings

An etale neighborhood of a Henselian local ring is trivial at a chosen point
when that point has the same residue field as the base.  The algebra need not
be module-finite: standard-etale structure near the point supplies one simple
root, and Hensel's lemma identifies that root with a base element.

The file also compares the residue-field map attached to a prime ideal with
the local residue-field map after localization.  This is the form needed for
the residue-field bijection produced by Tag 00UJ.
-/

noncomputable section

namespace EtaleFundamentalGroups

open Polynomial

universe u v

/-- If a prime lies over the maximal ideal of a local base, the canonical map
from the base to the localization at that prime is local. -/
theorem isLocalHom_algebraMap_localizationAtPrime_of_liesOver_maximalIdeal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] (P : Ideal S) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)] :
    IsLocalHom (algebraMap R (Localization.AtPrime P)) := by
  apply ((IsLocalRing.local_hom_TFAE
    (algebraMap R (Localization.AtPrime P))).out 1 5 rfl rfl).mpr
  change (IsLocalRing.maximalIdeal (Localization.AtPrime P)).under R =
    IsLocalRing.maximalIdeal R
  rw [← Ideal.under_under (B := S), Localization.AtPrime.under_maximalIdeal]
  exact (P.over_def (IsLocalRing.maximalIdeal R)).symm

/-- A local ring is canonically isomorphic to its localization at its maximal
ideal. -/
noncomputable def localizationAtMaximalIdealAlgEquiv
    (R : Type u) [CommRing R] [IsLocalRing R] :
    R ≃ₐ[R] Localization.AtPrime (IsLocalRing.maximalIdeal R) :=
  IsLocalization.atUnits R (IsLocalRing.maximalIdeal R).primeCompl
    (fun x ↦ by simpa using! fun a ↦ a)

/-- A bijection between the ideal-theoretic residue fields at `m_R` and `P`
induces a bijection on the residue fields of the local map `R → S_P`.

The source comparison is the canonical equivalence
`R ≃ R_{m_R}`. -/
theorem localResidueFieldMap_bijective_of_residueFieldMap_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [IsLocalRing R] (P : Ideal S) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P
        (Algebra.ofId R S) (P.over_def (IsLocalRing.maximalIdeal R)))) :
    letI :=
      isLocalHom_algebraMap_localizationAtPrime_of_liesOver_maximalIdeal
        (R := R) (S := S) P
    Function.Bijective
      (IsLocalRing.ResidueField.map
        (algebraMap R (Localization.AtPrime P))) := by
  let m := IsLocalRing.maximalIdeal R
  let T := Localization.AtPrime P
  let : IsLocalHom (algebraMap R T) :=
    isLocalHom_algebraMap_localizationAtPrime_of_liesOver_maximalIdeal
      (R := R) (S := S) P
  let e : R ≃ₐ[R] Localization.AtPrime m :=
    localizationAtMaximalIdealAlgEquiv R
  let f : Localization.AtPrime m →+* T :=
    Localization.localRingHom m P (algebraMap R S) (P.over_def m)
  have hcomp : f.comp e.toRingHom = algebraMap R T := by
    ext x
    change f (e x) = algebraMap R T x
    have hex : e x = algebraMap R (Localization.AtPrime m) x := by
      simpa using e.commutes x
    rw [hex, Localization.localRingHom_to_map]
    exact IsScalarTower.algebraMap_apply R S T x
  let : IsLocalHom e.toRingEquiv.toRingHom := by
    have h : IsLocalHom e.toRingEquiv := inferInstance
    exact ⟨h.map_nonunit⟩
  have he : Function.Bijective
      (IsLocalRing.ResidueField.map e.toRingHom) :=
    (IsLocalRing.ResidueField.mapEquiv e.toRingEquiv).bijective
  have hf : Function.Bijective (IsLocalRing.ResidueField.map f) := by
    change Function.Bijective
      (Ideal.ResidueField.map m P (algebraMap R S) (P.over_def m)) at hres
    exact hres
  have hmap :
      IsLocalRing.ResidueField.map (algebraMap R T) =
        (IsLocalRing.ResidueField.map f).comp
          (IsLocalRing.ResidueField.map e.toRingHom) := by
    ext z
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    rw [IsLocalRing.ResidueField.map_residue,
      RingHom.comp_apply, IsLocalRing.ResidueField.map_residue,
      IsLocalRing.ResidueField.map_residue]
    exact congrArg (IsLocalRing.residue T)
      (DFunLike.congr_fun hcomp x).symm
  rw [hmap]
  exact hf.comp he

/-- A pointed etale neighborhood of a Henselian local ring, with unchanged
residue field at the chosen prime, has trivial local ring.

No module-finiteness assumption on `S` is used.  Tag 00UE supplies a
standard-etale neighborhood of `P`; Hensel's lemma moves its distinguished
simple root into `R`, and localization clears the remaining denominators. -/
theorem algebraMap_localizationAtPrime_bijective_of_henselian_of_etale_of_residueFieldMap_bijective
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [Algebra.Etale R S]
    (P : Ideal S) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P
        (Algebra.ofId R S) (P.over_def (IsLocalRing.maximalIdeal R)))) :
    Function.Bijective (algebraMap R (Localization.AtPrime P)) := by
  let T := Localization.AtPrime P
  let : IsLocalHom (algebraMap R T) :=
    isLocalHom_algebraMap_localizationAtPrime_of_liesOver_maximalIdeal
      (R := R) (S := S) P
  have hresLocal : Function.Bijective
      (IsLocalRing.ResidueField.map (algebraMap R T)) :=
    localResidueFieldMap_bijective_of_residueFieldMap_bijective
      (R := R) (S := S) P hres
  obtain ⟨s, hsP, hstd⟩ :=
    Algebra.IsEtaleAt.exists_isStandardEtale (R := R) P
  let C := Localization.Away s
  let : Algebra.IsStandardEtale R C := hstd
  let hsUnit : IsUnit ((IsScalarTower.toAlgHom R S T) s) :=
    IsLocalization.map_units (M := P.primeCompl) T
      ⟨s, show s ∈ P.primeCompl from hsP⟩
  let j : C →ₐ[R] T :=
    IsLocalization.Away.liftAlgHom s
      (f := IsScalarTower.toAlgHom R S T)
      hsUnit
  have j_algebraMap (z : S) :
      j (algebraMap S C z) = algebraMap S T z := by
    change IsLocalization.Away.lift s hsUnit (algebraMap S C z) = _
    calc
      _ = (IsScalarTower.toAlgHom R S T).toRingHom z :=
        IsLocalization.Away.lift_eq (S := C) s hsUnit z
      _ = _ := IsScalarTower.toAlgHom_apply R S T z
  let E : StandardEtalePresentation R C :=
    Algebra.IsStandardEtale.nonempty_standardEtalePresentation.some
  let beta : T := j E.x
  have hbeta : E.P.HasMap beta := E.hasMap.map j
  obtain ⟨a₀, ha₀⟩ :=
    hresLocal.surjective (IsLocalRing.residue T beta)
  have hf_root_residue : aeval a₀ E.f = 0 := by
    apply hresLocal.injective
    rw [map_zero]
    calc
      IsLocalRing.ResidueField.map (algebraMap R T) (aeval a₀ E.f) =
          aeval (IsLocalRing.ResidueField.map (algebraMap R T) a₀)
            (E.f.map (IsLocalRing.residue R)) := by
        rw [Polynomial.map_aeval_eq_aeval_map
          (R := R) (S := IsLocalRing.ResidueField R)
          (T := IsLocalRing.ResidueField R)
          (U := IsLocalRing.ResidueField T)
          (φ := IsLocalRing.residue R)
          (ψ := IsLocalRing.ResidueField.map (algebraMap R T)) rfl]
      _ = aeval (IsLocalRing.residue T beta)
          (E.f.map (IsLocalRing.residue R)) := by rw [ha₀]
      _ = IsLocalRing.residue T (aeval beta E.f) := by
        exact (Polynomial.map_aeval_eq_aeval_map
          (R := R) (S := T)
          (T := IsLocalRing.ResidueField R)
          (U := IsLocalRing.ResidueField T)
          (φ := IsLocalRing.residue R)
          (ψ := IsLocalRing.residue T) rfl E.f beta).symm
      _ = 0 := by rw [hbeta.1, map_zero]
  have hf_derivative_residue : aeval a₀ E.f.derivative ≠ 0 := by
    intro hzero
    have hmap := congrArg
      (IsLocalRing.ResidueField.map (algebraMap R T)) hzero
    rw [map_zero,
      Polynomial.map_aeval_eq_aeval_map
        (R := R) (S := IsLocalRing.ResidueField R)
        (T := IsLocalRing.ResidueField R)
        (U := IsLocalRing.ResidueField T)
        (φ := IsLocalRing.residue R)
        (ψ := IsLocalRing.ResidueField.map (algebraMap R T)) rfl,
      ha₀] at hmap
    have hmap' :
        aeval (IsLocalRing.residue T beta)
            (E.f.derivative.map (IsLocalRing.residue R)) =
          IsLocalRing.residue T (aeval beta E.f.derivative) :=
      (Polynomial.map_aeval_eq_aeval_map
        (R := R) (S := T)
        (T := IsLocalRing.ResidueField R)
        (U := IsLocalRing.ResidueField T)
        (φ := IsLocalRing.residue R)
        (ψ := IsLocalRing.residue T) rfl E.f.derivative beta).symm
    rw [hmap'] at hmap
    exact ((IsLocalRing.residue_ne_zero_iff_isUnit
      (aeval beta E.f.derivative)).mpr hbeta.isUnit_derivative_f) hmap
  have hHensel := ((HenselianLocalRing.TFAE R).out 1 2).mp
    (inferInstance : HenselianLocalRing R)
  obtain ⟨a, ha_root, ha_residue⟩ :=
    hHensel E.f E.monic_f a₀ hf_root_residue hf_derivative_residue
  have hresidue :
      IsLocalRing.residue T (algebraMap R T a) =
        IsLocalRing.residue T beta := by
    rw [← IsLocalRing.ResidueField.map_residue, ha_residue, ha₀]
  have hnot_unit : ¬ IsUnit (beta - algebraMap R T a) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
    simp [hresidue]
  have hbeta_image : beta = algebraMap R T a := by
    let g : T[X] := E.f.map (algebraMap R T)
    apply IsLocalRing.eq_of_eval_eq_zero_of_not_isUnit_sub
      (f := g) (a := beta) (b := algebraMap R T a)
    · simpa [g, aeval_def] using hbeta.1
    · simpa [g, eval_map] using congrArg (algebraMap R T) ha_root
    · exact hnot_unit
    · simpa [g, derivative_map, aeval_def] using
        hbeta.isUnit_derivative_f
  have hg_unit : IsUnit (aeval a E.g) := by
    refine IsUnit.of_map (algebraMap R T) (aeval a E.g) ?_
    change IsUnit ((Algebra.ofId R T) (aeval a E.g))
    rw [← aeval_algHom_apply (Algebra.ofId R T) a E.g]
    change IsUnit (aeval (algebraMap R T a) E.g)
    rw [← hbeta_image]
    exact hbeta.2
  have haHasMap : E.P.HasMap a := ⟨ha_root, hg_unit⟩
  let sec : C →ₐ[R] R :=
    (E.P.lift a haHasMap).comp E.equivRing.toAlgHom
  have hj : j = (Algebra.ofId R T).comp sec := by
    apply E.hom_ext
    simp [sec, beta, hbeta_image]
  have hj_range (c : C) : ∃ r : R, algebraMap R T r = j c := by
    exact ⟨sec c, (DFunLike.congr_fun hj c).symm⟩
  have hsurjective : Function.Surjective (algebraMap R T) := by
    intro z
    obtain ⟨x, y, rfl⟩ :=
      IsLocalization.exists_mk'_eq P.primeCompl z
    obtain ⟨rx, hx⟩ := hj_range (algebraMap S C x)
    obtain ⟨ry, hy⟩ := hj_range (algebraMap S C y.1)
    have hx' : algebraMap R T rx = algebraMap S T x := by
      rw [j_algebraMap] at hx
      exact hx
    have hy' : algebraMap R T ry = algebraMap S T y.1 := by
      rw [j_algebraMap] at hy
      exact hy
    have hry : IsUnit ry := by
      apply IsUnit.of_map (algebraMap R T)
      rw [hy']
      exact IsLocalization.map_units T y
    let unitY : Rˣ := hry.unit
    have hunitY : (unitY : R) = ry := hry.unit_spec
    refine ⟨rx * (↑unitY⁻¹ : R), ?_⟩
    apply IsLocalization.eq_mk'_iff_mul_eq.mpr
    calc
      algebraMap R T (rx * (↑unitY⁻¹ : R)) *
          algebraMap S T y.1 =
          (algebraMap R T rx * algebraMap R T (↑unitY⁻¹ : R)) *
            algebraMap R T ry := by rw [map_mul, hy']
      _ = algebraMap R T rx := by
        rw [mul_assoc, ← map_mul, ← hunitY]
        simp
      _ = algebraMap S T x := hx'
  let : Module.Flat R T := Module.Flat.trans R S T
  let : Module.FaithfullyFlat R T :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact ⟨FaithfulSMul.algebraMap_injective R T, hsurjective⟩

/-- The explicit base-algebra equivalence associated to a pointed etale
neighborhood with unchanged residue field. -/
noncomputable def henselianPointedEtaleLocalizationAlgEquiv
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [Algebra.Etale R S]
    (P : Ideal S) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (hres : Function.Bijective
      (Ideal.ResidueField.mapₐ (IsLocalRing.maximalIdeal R) P
        (Algebra.ofId R S) (P.over_def (IsLocalRing.maximalIdeal R)))) :
    R ≃ₐ[R] Localization.AtPrime P :=
  AlgEquiv.ofBijective (Algebra.ofId R (Localization.AtPrime P))
    (algebraMap_localizationAtPrime_bijective_of_henselian_of_etale_of_residueFieldMap_bijective
      P hres)

end EtaleFundamentalGroups

end
