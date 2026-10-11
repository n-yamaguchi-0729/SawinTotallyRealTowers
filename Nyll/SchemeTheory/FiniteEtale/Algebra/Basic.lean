/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
The cited pi1 file has no copyright notice; its holder requires review.

Based on pi1 source (comparison revision; exact copied commit unverified):
https://github.com/chrisflav/pi1/blob/5c5c0171efc863ce9990171bdf46d7cb5fd582fb/Pi1/RingTheory/FiniteEtale/Basic.lean
-/

module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.RingTheory.RingHom.Etale
public import Mathlib.RingTheory.RingHom.Finite
public import Mathlib.RingTheory.TotallySplit
public import Nyll.SchemeTheory.RingTheory.Finite

/-!
# Finite etale algebras

The finite etale property combines etaleness with module finiteness. The accompanying
lemmas transport this property across algebra equivalences and localizations.
-/

@[expose] public section

open TensorProduct

universe u

/-- An `R`-algebra is finite étale when it is étale and finite as an `R`-module. -/
@[mk_iff]
class Algebra.FiniteEtale (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] : Prop
  extends Algebra.Etale R S, Module.Finite R S

lemma Algebra.FiniteEtale.of_equiv {R S S' : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteEtale R S] [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S') :
    Algebra.FiniteEtale R S' := by
  have := Algebra.Etale.of_equiv e
  have := Module.Finite.equiv e.toLinearEquiv
  constructor

instance (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsFiniteSplit R S] : Algebra.FiniteEtale R S where

section

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

lemma RingHom.OfLocalizationSpan.of_exists_of_isPrime
    (hP : RingHom.OfLocalizationSpan P)
    {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S)
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p, P (Localization.awayMap f r)) :
    P f := by
  have := H
  choose u hu₁ hu₂ using this
  apply hP f (Set.range (fun p : PrimeSpectrum R ↦ u p.asIdeal))
  · rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff]
    rw [_root_.eq_top_iff]
    rintro p -
    simp only [TopologicalSpace.Opens.iSup_mk, TopologicalSpace.Opens.carrier_eq_coe,
      PrimeSpectrum.basicOpen_eq_zeroLocus_compl]
    simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iUnion, Set.mem_compl_iff,
      PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff, SetLike.mem_coe]
    use p
    apply hu₁
  · rintro ⟨p, ⟨p, rfl⟩⟩
    apply hu₂

lemma IsUnit.tmul {R S T : Type*} [CommRing R] [CommRing S]
    [CommRing T] [Algebra R T] [Algebra R S] {s : S} {t : T} (hs : IsUnit s) (ht : IsUnit t) :
    IsUnit (s ⊗ₜ[R] t) := by
  obtain ⟨s, rfl⟩ := hs
  obtain ⟨t, rfl⟩ := ht
  rw [isUnit_iff_exists_inv]
  use s⁻¹.val ⊗ₜ t⁻¹.val
  simp [Algebra.TensorProduct.one_def]

lemma RingHom.OfLocalizationSpan.of_exists_of_isPrime'
    {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}
    (hP : RingHom.OfLocalizationSpan P)
    (hPi : RingHom.RespectsIso P)
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      P (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] S))) :
    P (algebraMap R S) := by
  apply hP.of_exists_of_isPrime
  intro p hp
  obtain ⟨r, hr, hf⟩ := H p
  refine ⟨r, hr, ?_⟩
  have : IsLocalization.Away ((Algebra.ofId R S) r) (Localization.Away ((algebraMap R S) r)) :=
    inferInstanceAs <| IsLocalization.Away (algebraMap R S r) _
  let u : Localization.Away r →ₐ[R] Localization.Away ((algebraMap R S) r) :=
    Localization.awayMapₐ (Algebra.ofId R S) r
  let v : S →ₐ[R] Localization.Away ((algebraMap R S) r) :=
    IsScalarTower.toAlgHom R S (Localization.Away ((algebraMap R S) r))
  let e₀ : S ⊗[R] Localization.Away r ≃ₐ[R] Localization.Away (algebraMap R S r) :=
    (IsLocalization.Away.tensorEquiv _ r (Localization.Away r)).restrictScalars R
  let e : Localization.Away r ⊗[R] S ≃+* Localization.Away (algebraMap R S r) :=
    (Algebra.TensorProduct.comm R _ _).trans e₀
  have : Localization.awayMap (algebraMap R S) r =
      e.toRingHom.comp (algebraMap (Localization.Away r) (Localization.Away r ⊗[R] S)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext x
    simp [e, Localization.awayMap, IsLocalization.Away.map, ← IsScalarTower.algebraMap_apply,
      Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [this]
  exact hPi.left _ _ hf

lemma Algebra.Etale.of_exists_of_isPrime {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Algebra.Etale (Localization.Away r) (Localization.Away r ⊗[R] S)) : Algebra.Etale R S := by
  simp_rw [← RingHom.etale_algebraMap] at H ⊢
  apply RingHom.Etale.ofLocalizationSpan.of_exists_of_isPrime'
  · exact RingHom.Etale.respectsIso
  · intro p hp
    obtain ⟨r, hr, hf⟩ := H p
    use r, hr

lemma Module.Finite.of_exists_of_isPrime {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Module.Finite (Localization.Away r) (Localization.Away r ⊗[R] S)) : Module.Finite R S := by
  simp_rw [← RingHom.finite_algebraMap_iff] at H ⊢
  apply RingHom.OfLocalizationSpan.of_exists_of_isPrime'
    RingHom.finite_ofLocalizationSpan
  · exact RingHom.finite_respectsIso
  · intro p hp
    obtain ⟨r, hr, h⟩ := H p
    use r, hr

lemma Algebra.FiniteEtale.of_exists_of_isPrime {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (H : ∀ (p : Ideal R) [p.IsPrime], ∃ r ∉ p,
      Algebra.FiniteEtale (Localization.Away r) (Localization.Away r ⊗[R] S)) :
    Algebra.FiniteEtale R S := by
  simp_rw [Algebra.finiteEtale_iff] at H ⊢
  refine ⟨.of_exists_of_isPrime fun p hp ↦ ?_, .of_exists_of_isPrime fun p hp ↦ ?_⟩
  · obtain ⟨r, hr, hf⟩ := H p
    exact ⟨r, hr, hf.1⟩
  · obtain ⟨r, hr, hf⟩ := H p
    exact ⟨r, hr, hf.2⟩
