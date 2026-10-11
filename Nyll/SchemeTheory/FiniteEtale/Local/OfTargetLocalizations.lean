/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Etale.Locus
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.RingHom.Etale

/-!
# Recovering global etaleness from target localizations

For an algebra of finite presentation, formal etaleness at every prime of the
target is equivalent to global etaleness.  This file records that implication
in forms convenient for literal ring maps: it is enough to check all prime
ideals, or only all maximal ideals, and the local input may be stated after
localizing both the source and target at a prime and its contraction.

The latter formulation is useful when the map under consideration is a
literal `Localization.awayMap`: no replacement of that map by an isomorphic
algebra is needed.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uR uS

/-- A finite-presentation algebra that is formally etale at every target
prime is etale. -/
theorem etale_of_isEtaleAt_all_primeIdeals
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (hlocal : ∀ (Q : Ideal S), [Q.IsPrime] → Algebra.IsEtaleAt R Q) :
    Algebra.Etale R S := by
  rw [← Algebra.etaleLocus_eq_univ_iff_etale]
  apply Set.eq_univ_iff_forall.mpr
  intro Q
  change Algebra.IsEtaleAt R Q.asIdeal
  exact hlocal Q.asIdeal

/-- For a finite-presentation algebra, it is enough to be formally etale at
every maximal ideal of the target.  Openness of the etale locus propagates
the property from a maximal ideal to every prime below it. -/
theorem etale_of_isEtaleAt_all_maximalIdeals
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (hlocal : ∀ (Q : Ideal S), [Q.IsMaximal] → Algebra.IsEtaleAt R Q) :
    Algebra.Etale R S := by
  rw [← Algebra.etaleLocus_eq_univ_iff_etale]
  apply Set.eq_univ_iff_forall.mpr
  intro q
  obtain ⟨Q, hQ, hqQ⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  let : Q.IsPrime := hQ.isPrime
  let Q' : PrimeSpectrum S := ⟨Q, inferInstance⟩
  have hQ' : Q' ∈ Algebra.etaleLocus R S := by
    change Algebra.IsEtaleAt R Q
    exact hlocal Q
  exact Algebra.isOpen_etaleLocus.stableUnderGeneralization
    ((PrimeSpectrum.le_iff_specializes q Q').mp hqQ) hQ'

/-- A local-local criterion for global etaleness.  At each target prime `Q`,
the source is localized at the contracted prime `Q.under R`, and the target
at `Q`.  Formal etaleness of these local maps implies etaleness of the
original finite-presentation algebra. -/
theorem etale_of_formallyEtale_localizationsAtPrime_all_primeIdeals
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (hlocal : ∀ (Q : Ideal S), [Q.IsPrime] →
      let p := Q.under R
      letI : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
        Localization.AtPrime.algebraOfLiesOver p Q
      Algebra.FormallyEtale (Localization.AtPrime p)
        (Localization.AtPrime Q)) :
    Algebra.Etale R S := by
  apply etale_of_isEtaleAt_all_primeIdeals
  intro Q _
  let p := Q.under R
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver p Q
  let : Algebra.FormallyEtale (Localization.AtPrime p)
      (Localization.AtPrime Q) := hlocal Q
  let : Algebra.FormallyEtale R (Localization.AtPrime p) :=
    Algebra.FormallyEtale.of_isLocalization p.primeCompl
  exact Algebra.FormallyEtale.comp R (Localization.AtPrime p)
    (Localization.AtPrime Q)

/-- The maximal-ideal version of
`etale_of_formallyEtale_localizationsAtPrime_all_primeIdeals`.  This is often
the most convenient form for a finite normalization, whose local factors are
naturally selected at maximal ideals. -/
theorem etale_of_formallyEtale_localizationsAtPrime_all_maximalIdeals
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FinitePresentation R S]
    (hlocal : ∀ (Q : Ideal S), [Q.IsMaximal] →
      let p := Q.under R
      letI : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
        Localization.AtPrime.algebraOfLiesOver p Q
      Algebra.FormallyEtale (Localization.AtPrime p)
        (Localization.AtPrime Q)) :
    Algebra.Etale R S := by
  apply etale_of_isEtaleAt_all_maximalIdeals
  intro Q _
  let p := Q.under R
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
    Localization.AtPrime.algebraOfLiesOver p Q
  let : Algebra.FormallyEtale (Localization.AtPrime p)
      (Localization.AtPrime Q) := hlocal Q
  let : Algebra.FormallyEtale R (Localization.AtPrime p) :=
    Algebra.FormallyEtale.of_isLocalization p.primeCompl
  exact Algebra.FormallyEtale.comp R (Localization.AtPrime p)
    (Localization.AtPrime Q)

/-- Ring-map form of
`etale_of_formallyEtale_localizationsAtPrime_all_primeIdeals`.  Supplying a
literal map here keeps that same map in the conclusion; in particular this
can be applied directly to `Localization.awayMap` for a primitive composite
map. -/
theorem ringHom_etale_of_formallyEtale_localizationsAtPrime_all_primeIdeals
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S]
    (mapRS : R →+* S) (hfp : mapRS.FinitePresentation)
    (hlocal :
      letI : Algebra R S := mapRS.toAlgebra
      ∀ (Q : Ideal S), [Q.IsPrime] →
        let p := Q.under R
        letI : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
          Localization.AtPrime.algebraOfLiesOver p Q
        Algebra.FormallyEtale (Localization.AtPrime p)
          (Localization.AtPrime Q)) :
    mapRS.Etale := by
  let : Algebra R S := mapRS.toAlgebra
  let : Algebra.FinitePresentation R S := hfp
  exact etale_of_formallyEtale_localizationsAtPrime_all_primeIdeals hlocal

/-- Maximal-ideal ring-map form of the target-local criterion.  For a literal
away map, the only global input left is finite presentation of that away map;
the remaining hypotheses concern its local maps at maximal ideals. -/
theorem ringHom_etale_of_formallyEtale_localizationsAtPrime_all_maximalIdeals
    {R : Type uR} {S : Type uS}
    [CommRing R] [CommRing S]
    (mapRS : R →+* S) (hfp : mapRS.FinitePresentation)
    (hlocal :
      letI : Algebra R S := mapRS.toAlgebra
      ∀ (Q : Ideal S), [Q.IsMaximal] →
        let p := Q.under R
        letI : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
          Localization.AtPrime.algebraOfLiesOver p Q
        Algebra.FormallyEtale (Localization.AtPrime p)
          (Localization.AtPrime Q)) :
    mapRS.Etale := by
  let : Algebra R S := mapRS.toAlgebra
  let : Algebra.FinitePresentation R S := hfp
  exact etale_of_formallyEtale_localizationsAtPrime_all_maximalIdeals hlocal

/-- A finite algebra over a Noetherian ring gives a particularly direct
literal-away-map criterion.  The finite-presentation input for the map of
away localizations is constructed internally; it remains only to prove
formal etaleness after localizing at every target maximal ideal and its
contraction. -/
theorem localization_awayMap_etale_of_formallyEtale_localizationsAtPrime_all_maximalIdeals
    {A : Type uR} {B : Type uS}
    [CommRing A] [CommRing B] [IsNoetherianRing A]
    [Algebra A B] [Module.Finite A B]
    (f : A)
    (hlocal :
      let S := Localization.Away f
      let fB := algebraMap A B f
      let T := Localization.Away fB
      let mapST : S →+* T := Localization.awayMap (algebraMap A B) f
      letI : Algebra S T := mapST.toAlgebra
      ∀ (Q : Ideal T), [Q.IsMaximal] →
        let p := Q.under S
        letI : Algebra (Localization.AtPrime p) (Localization.AtPrime Q) :=
          Localization.AtPrime.algebraOfLiesOver p Q
        Algebra.FormallyEtale (Localization.AtPrime p)
          (Localization.AtPrime Q)) :
    (Localization.awayMap (algebraMap A B) f).Etale := by
  let S := Localization.Away f
  let fB : B := algebraMap A B f
  let T := Localization.Away fB
  let mapST : S →+* T := Localization.awayMap (algebraMap A B) f
  let : Algebra S T := mapST.toAlgebra
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A S T := by
    apply IsScalarTower.of_algebraMap_eq
    intro a
    change algebraMap A T a = mapST (algebraMap A S a)
    rw [IsScalarTower.algebraMap_apply A B T]
    simp [mapST, S, T, fB, IsLocalization.Away.map]
  let : Module.Finite S T :=
    Module.Finite.of_isLocalization A B (Submonoid.powers f)
  let : Module.FinitePresentation S T :=
    Module.finitePresentation_of_finite S T
  let : Algebra.FinitePresentation S T :=
    Algebra.FinitePresentation.of_finitePresentation S T
  exact ringHom_etale_of_formallyEtale_localizationsAtPrime_all_maximalIdeals
    mapST (by
      change Algebra.FinitePresentation S T
      infer_instance) hlocal

end EtaleFundamentalGroups

end
