/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.QuasiFinite
import Nyll.SchemeTheory.FiniteEtale.Henselian.PointedEtale

/-!
# Chosen local factors over Henselian local rings

A prime-local factor of an etale algebra over a Henselian local ring is finite over the base.
The proof uses the finite idempotent factor furnished by Tag 00UJ and trivializes its pointed
etale neighbourhood by Hensel's lemma.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u v

/-- A chosen prime-local factor of an etale algebra over a Henselian local ring is finite
over the base ring. -/
theorem moduleFinite_localizationAtPrime_of_henselian_of_etale
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [Algebra.Etale R S]
    (q : Ideal S) [q.IsPrime] [q.LiesOver (IsLocalRing.maximalIdeal R)] :
    Module.Finite R (Localization.AtPrime q) := by
  let p := IsLocalRing.maximalIdeal R
  obtain ⟨C, _, _, _, P, _, _, e, he, P', _, _, hP'q, heP', hres, hfinite, hunique⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq p q
  let B := TensorProduct R C S
  let D := Localization.Away e
  let Q : Ideal D := P'.map (algebraMap B D)
  have hdisj : Disjoint ((Submonoid.powers e : Submonoid B) : Set B) (P' : Set B) := by
    rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    exact heP'
  let : Q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (.powers e) D P' inferInstance hdisj
  have hQoverP' : Q.LiesOver P' :=
    IsLocalization.liesOver_map_of_isPrime_disjoint (.powers e) D hdisj
  have hQunder : Q.comap (algebraMap B D) = P' := hQoverP'.over.symm
  let : Q.LiesOver P := .trans Q P' P
  have hQunique : P.primesOver D = {Q} := by
    ext J
    constructor
    · rintro ⟨hJprime, hJover⟩
      let : J.IsPrime := hJprime
      let : J.LiesOver P := hJover
      let J₀ : Ideal B := J.comap (algebraMap B D)
      let : J₀.IsPrime := Ideal.IsPrime.under B J
      let : J.LiesOver J₀ := ⟨rfl⟩
      let : J₀.LiesOver P := .tower_bot J J₀ P
      have heJ₀ : e ∉ J₀ := by
        intro heJ
        have heJD : algebraMap B D e ∈ J := heJ
        exact hJprime.ne_top
          (J.eq_top_of_isUnit_mem heJD
            (IsLocalization.map_units D ⟨e, Submonoid.mem_powers e⟩))
      have hJ₀ : J₀ = P' := hunique J₀ inferInstance inferInstance heJ₀
      rw [Set.mem_singleton_iff]
      calc
        J = J₀.map (algebraMap B D) := (IsLocalization.map_under (.powers e) D J).symm
        _ = P'.map (algebraMap B D) := congrArg (Ideal.map (algebraMap B D)) hJ₀
        _ = Q := rfl
    · intro hJ
      rw [Set.mem_singleton_iff] at hJ
      subst J
      exact ⟨inferInstance, inferInstance⟩
  let Cₚ := Localization.AtPrime P
  let Dₚ := Localization.AtPrime Q
  let : Algebra Cₚ Dₚ := Localization.AtPrime.algebraOfLiesOver P Q
  let : IsScalarTower C Cₚ Dₚ := inferInstance
  let : Module.Finite Cₚ Dₚ :=
    Localization.finite_of_primesOver_eq_singleton hQunique
  let pointed : R ≃ₐ[R] Cₚ := henselianPointedEtaleLocalizationAlgEquiv P hres
  let : Module.Finite R Cₚ :=
    Module.Finite.of_surjective pointed.toLinearMap pointed.surjective
  let : Module.Finite R Dₚ := Module.Finite.trans Cₚ Dₚ
  let BS := TensorProduct R Cₚ S
  let φ : B →ₐ[C] BS :=
    Algebra.TensorProduct.map (Algebra.ofId C Cₚ) (AlgHom.id R S)
  let : Algebra B BS := φ.toAlgebra
  let : IsScalarTower C B BS := IsScalarTower.of_algebraMap_eq' φ.comp_algebraMap.symm
  let : IsScalarTower R B BS := IsScalarTower.of_algebraMap_eq' (by
    ext r
    simp [RingHom.algebraMap_toAlgebra, φ])
  let hBS : IsLocalization (Algebra.algebraMapSubmonoid B P.primeCompl) BS := by
    exact IsLocalization.tensorProduct_tensorProduct R S P.primeCompl Cₚ (by
      ext
      change φ (1 ⊗ₜ[R] _) = 1 ⊗ₜ[R] _
      rw [Algebra.TensorProduct.map_tmul]
      simp)
  let cancel : BS ≃ₐ[R] S :=
    (Algebra.TensorProduct.congr pointed.symm (AlgEquiv.refl)).trans
      (Algebra.TensorProduct.lid R S)
  let PBS : Ideal BS := P'.map (algebraMap B BS)
  have hPdisj :
      Disjoint ((Algebra.algebraMapSubmonoid B P.primeCompl : Submonoid B) : Set B)
        (P' : Set B) :=
    Ideal.disjoint_primeCompl_of_liesOver P' P
  let : PBS.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid B P.primeCompl) BS P' inferInstance hPdisj
  have hPBSoverP' : PBS.LiesOver P' :=
    IsLocalization.liesOver_map_of_isPrime_disjoint
      (Algebra.algebraMapSubmonoid B P.primeCompl) BS hPdisj
  have hPBSunder : PBS.comap (algebraMap B BS) = P' := hPBSoverP'.over.symm
  have hcancel_right (s : S) :
      cancel (algebraMap B BS (Algebra.TensorProduct.includeRight s)) = s := by
    change (Algebra.TensorProduct.lid R S)
      ((Algebra.TensorProduct.congr pointed.symm (AlgEquiv.refl))
        ((Algebra.TensorProduct.map (Algebra.ofId C Cₚ) (AlgHom.id R S))
          (1 ⊗ₜ[R] s))) = s
    rw [Algebra.TensorProduct.map_tmul]
    simp
  have hcancel_symm_right (s : S) :
      cancel.symm s = algebraMap B BS (Algebra.TensorProduct.includeRight s) :=
    (cancel.eq_symm_apply.mpr (hcancel_right s)).symm
  have hPBScancel : PBS.map (cancel.toRingEquiv : BS →+* S) = q := by
    ext s
    rw [Ideal.map_comap_of_equiv cancel.toRingEquiv]
    change cancel.symm s ∈ PBS ↔ s ∈ q
    rw [hcancel_symm_right]
    change Algebra.TensorProduct.includeRight s ∈
      PBS.comap (algebraMap B BS) ↔ s ∈ q
    rw [hPBSunder]
    change s ∈ P'.comap Algebra.TensorProduct.includeRight.toRingHom ↔ s ∈ q
    rw [hP'q]
  have hPBScomap : PBS = q.comap cancel.toRingHom := by
    symm
    rw [← hPBScancel, Ideal.map_comap_of_equiv cancel.toRingEquiv]
    exact Ideal.comap_of_equiv cancel.toRingEquiv
  let BSₚ := Localization.AtPrime PBS
  let Sₚ := Localization.AtPrime q
  let cancelLocal : BSₚ ≃ₐ[R] Sₚ :=
    Localization.localAlgEquiv PBS q cancel hPBScomap
  let hDₚB : IsLocalization P'.primeCompl Dₚ := by
    have hloc := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (.powers e) Dₚ Q
    have hsub : (Q.comap (algebraMap B D)).primeCompl = P'.primeCompl := by
      ext x
      change (x ∉ Q.comap (algebraMap B D)) ↔ x ∉ P'
      rw [hQunder]
    exact hsub ▸ hloc
  let hBSₚB : IsLocalization P'.primeCompl BSₚ := by
    have hloc := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Algebra.algebraMapSubmonoid B P.primeCompl) BSₚ PBS
    have hsub : (PBS.comap (algebraMap B BS)).primeCompl = P'.primeCompl := by
      ext x
      change (x ∉ PBS.comap (algebraMap B BS)) ↔ x ∉ P'
      rw [hPBSunder]
    exact hsub ▸ hloc
  let localFactorEquiv : Dₚ ≃ₐ[B] BSₚ :=
    IsLocalization.algEquiv P'.primeCompl Dₚ BSₚ
  let localFactorEquivR : Dₚ ≃ₐ[R] BSₚ := localFactorEquiv.restrictScalars R
  exact Module.Finite.of_surjective
    (localFactorEquivR.trans cancelLocal).toLinearMap
    (localFactorEquivR.trans cancelLocal).surjective

end EtaleFundamentalGroups
