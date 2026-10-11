/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.Ideal
import Nyll.SchemeTheory.FiniteEtale.Henselian.Strict

/-!
# A uniquely chosen finite étale factor over a strictly Henselian local ring

Tag 00UJ isolates a finite idempotent factor with a unique prime over the
chosen closed point.  Once local purity has made that factor étale, the
uniqueness makes the factor local.  Faithful flatness is then produced from
flatness and the local algebra map, so the connected strict-Henselian
splitting theorem applies without a separate faithfulness hypothesis.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe u

/-- A finite étale algebra with a unique prime over the closed point of a
strictly Henselian local base is the base ring itself.

The unique-prime input is exactly the output supplied for the chosen finite
idempotent factor by Tag 00UJ.  Localness, local-hom status, and faithful
flatness are conclusions internal to the proof. -/
theorem algebraMap_bijective_of_unique_prime_over_maximal_of_strictHenselian
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [Module.Finite R S] [Algebra.Etale R S]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal R)]
    (hunique : ∀ Q : Ideal S, Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal R) → Q = q) :
    Function.Bijective (algebraMap R S) := by
  have hq_maximal : q.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (algebraMap R S)
      (fun x ↦ Algebra.IsIntegral.isIntegral x) q <| by
      rw [← Ideal.under_def, ← q.over_def (IsLocalRing.maximalIdeal R)]
      exact IsLocalRing.maximalIdeal.isMaximal R
  let : IsLocalRing S := IsLocalRing.of_unique_max_ideal ⟨q, hq_maximal, by
    intro Q hQ_maximal
    let : Q.IsPrime := hQ_maximal.isPrime
    have hQ_under_maximal : (Q.under R).IsMaximal :=
      Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (algebraMap R S)
        (fun x ↦ Algebra.IsIntegral.isIntegral x) Q
    have hQ_over : Q.LiesOver (IsLocalRing.maximalIdeal R) :=
      { over := (IsLocalRing.eq_maximalIdeal hQ_under_maximal).symm }
    exact hunique Q inferInstance hQ_over⟩
  have hq_eq : q = IsLocalRing.maximalIdeal S :=
    IsLocalRing.eq_maximalIdeal hq_maximal
  have hcomap :
      (IsLocalRing.maximalIdeal S).comap (algebraMap R S) =
        IsLocalRing.maximalIdeal R := by
    rw [← hq_eq]
    change q.under R = IsLocalRing.maximalIdeal R
    exact (q.over_def (IsLocalRing.maximalIdeal R)).symm
  let : IsLocalHom (algebraMap R S) :=
    ((IsLocalRing.local_hom_TFAE (algebraMap R S)).out 5 1).mp hcomap
  let : Module.FaithfullyFlat R S :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact
    algebraMap_bijective_of_henselian_of_isSepClosed_residue_of_finiteEtale_local
      (R := R) (S := S)

/-- The explicit base-algebra equivalence for the uniquely chosen finite
étale factor over a strictly Henselian local base. -/
noncomputable def strictHenselianChosenFactorAlgEquiv
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [HenselianLocalRing R] [Module.Finite R S] [Algebra.Etale R S]
    [IsSepClosed (IsLocalRing.ResidueField R)]
    (q : Ideal S) [q.IsPrime]
    [q.LiesOver (IsLocalRing.maximalIdeal R)]
    (hunique : ∀ Q : Ideal S, Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal R) → Q = q) :
    R ≃ₐ[R] S :=
  AlgEquiv.ofBijective (Algebra.ofId R S)
    (algebraMap_bijective_of_unique_prime_over_maximal_of_strictHenselian
      q hunique)

/-- The finite Away-factor isolated by Tag 00UJ is the strict-Henselian base
once it is étale and the Tag 00UJ prime is the unique prime over the closed
point that avoids the inverted element.

This statement performs the localization-prime transport: no separate
localness, local-hom, faithful-flatness, or unique-prime assertion on the
localized factor is assumed. -/
theorem algebraMap_bijective_away_of_unique_prime_over_maximal_of_strictHenselian
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (e : A)
    [Module.Finite R (Localization.Away e)]
    [Algebra.Etale R (Localization.Away e)]
    (P : Ideal A) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (heP : e ∉ P)
    (hunique : ∀ Q : Ideal A, Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal R) → e ∉ Q → Q = P) :
    Function.Bijective (algebraMap R (Localization.Away e)) := by
  let T := Localization.Away e
  have hdisjoint :
      Disjoint (Submonoid.powers e : Set A) (P : Set A) := by
    rw [Ideal.disjoint_powers_iff_notMem_of_isPrime]
    exact heP
  let q : Ideal T := P.map (algebraMap A T)
  have hq_prime : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers e) T P inferInstance hdisjoint
  let : q.IsPrime := hq_prime
  have hq_over_P : q.LiesOver P :=
    IsLocalization.liesOver_map_of_isPrime_disjoint
      (Submonoid.powers e) T hdisjoint
  let : q.LiesOver P := hq_over_P
  have hq_over_closed : q.LiesOver (IsLocalRing.maximalIdeal R) :=
    Ideal.LiesOver.trans q P (IsLocalRing.maximalIdeal R)
  let : q.LiesOver (IsLocalRing.maximalIdeal R) := hq_over_closed
  apply
    algebraMap_bijective_of_unique_prime_over_maximal_of_strictHenselian
      q
  intro Q hQ_prime hQ_over
  let : Q.IsPrime := hQ_prime
  let : Q.LiesOver (IsLocalRing.maximalIdeal R) := hQ_over
  have hQ_under_prime : (Q.under A).IsPrime := inferInstance
  have hQ_under_over :
      (Q.under A).LiesOver (IsLocalRing.maximalIdeal R) := inferInstance
  have heQ : e ∉ Q.under A := by
    intro he
    exact
      (Ideal.notMem_of_isUnit Q
        (IsLocalization.Away.algebraMap_isUnit (S := T) e)) he
  have h_under : Q.under A = P :=
    hunique (Q.under A) hQ_under_prime hQ_under_over heQ
  change Q = P.map (algebraMap A T)
  rw [← h_under]
  exact (IsLocalization.map_under (Submonoid.powers e) T Q).symm

/-- The explicit algebra equivalence for the Away-factor version of the Tag
00UJ strict-Henselian splitting consumer. -/
noncomputable def strictHenselianAwayChosenFactorAlgEquiv
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [HenselianLocalRing R] [IsSepClosed (IsLocalRing.ResidueField R)]
    (e : A)
    [Module.Finite R (Localization.Away e)]
    [Algebra.Etale R (Localization.Away e)]
    (P : Ideal A) [P.IsPrime]
    [P.LiesOver (IsLocalRing.maximalIdeal R)]
    (heP : e ∉ P)
    (hunique : ∀ Q : Ideal A, Q.IsPrime →
      Q.LiesOver (IsLocalRing.maximalIdeal R) → e ∉ Q → Q = P) :
    R ≃ₐ[R] Localization.Away e :=
  AlgEquiv.ofBijective (Algebra.ofId R (Localization.Away e))
    (algebraMap_bijective_away_of_unique_prime_over_maximal_of_strictHenselian
      e P heP hunique)

end EtaleFundamentalGroups
