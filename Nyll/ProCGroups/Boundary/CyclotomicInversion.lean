/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.GroupTheory.OrderOfElement

/-!
# The abelian consequence of cyclotomic inversion

If an element is conjugate to its inverse, then its image in an abelian
quotient has order dividing two.  Consequently an odd-order image is
trivial.  This is the group-theoretic step used in the residue-
characteristic-two boundary argument.
-/

namespace ProCGroups.Boundary

universe u v

/-- An element conjugate to its inverse has trivial image in an abelian
quotient whenever that image has order prime to two. -/
theorem map_eq_one_of_isConj_inv_of_coprime_two
    {G : Type u} {A : Type v} [Group G] [CommGroup A]
    (f : G →* A) {gamma : G} (hConj : IsConj gamma gamma⁻¹)
    (hCoprime : Nat.Coprime (orderOf (f gamma)) 2) :
    f gamma = 1 := by
  have hInv : f gamma = (f gamma)⁻¹ := by
    rw [← map_inv]
    exact isConj_iff_eq.mp (f.map_isConj hConj)
  have hSquare : (f gamma) ^ 2 = 1 := by
    calc
      (f gamma) ^ 2 = f gamma * f gamma := pow_two _
      _ = f gamma * (f gamma)⁻¹ := congrArg (fun x => f gamma * x) hInv
      _ = 1 := mul_inv_cancel _
  have hOrder : orderOf (f gamma) = 1 :=
    Nat.eq_one_of_dvd_coprimes hCoprime dvd_rfl
      (orderOf_dvd_of_pow_eq_one hSquare)
  exact orderOf_eq_one_iff.mp hOrder

/-- Odd order is a convenient form of the preceding coprimality
criterion. -/
theorem map_eq_one_of_isConj_inv_of_odd_order
    {G : Type u} {A : Type v} [Group G] [CommGroup A]
    (f : G →* A) {gamma : G} (hConj : IsConj gamma gamma⁻¹)
    (hOdd : Odd (orderOf (f gamma))) :
    f gamma = 1 :=
  map_eq_one_of_isConj_inv_of_coprime_two f hConj hOdd.coprime_two_right

/-- A finite subgroup whose elements are all conjugate to their inverses has
trivial image in every abelian quotient when its cardinality is prime to two. -/
theorem map_eq_bot_of_forall_isConj_inv_of_card_coprime_two
    {G : Type u} {A : Type v} [Group G] [CommGroup A]
    (f : G →* A) (I : Subgroup G) [Finite I]
    (hConj : ∀ gamma : G, gamma ∈ I → IsConj gamma gamma⁻¹)
    (hCoprime : Nat.Coprime (Nat.card I) 2) :
    I.map f = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨gamma, hgamma, rfl⟩
  have hOrderCoprime : Nat.Coprime (orderOf (f gamma)) 2 :=
    hCoprime.coprime_dvd_left <|
      (orderOf_map_dvd f gamma).trans (I.orderOf_dvd_natCard hgamma)
  exact
    map_eq_one_of_isConj_inv_of_coprime_two f (hConj gamma hgamma)
      hOrderCoprime

/-- A finite cyclic subgroup of odd order vanishes when one of its generators
is conjugate in the ambient abelian group to its inverse.  This packages the
two inputs in the boundary proof: cyclotomic inversion and odd divisorial
inertia. -/
theorem subgroup_eq_bot_of_generator_isConj_inv_of_card_coprime_two
    {A : Type u} [CommGroup A] (I : Subgroup A) [Finite I]
    {gamma : A} (hGenerates : Subgroup.zpowers gamma = I)
    (hConj : IsConj gamma gamma⁻¹)
    (hCoprime : Nat.Coprime (Nat.card I) 2) :
    I = ⊥ := by
  have hGamma : gamma ∈ I := by
    rw [← hGenerates]
    exact Subgroup.mem_zpowers gamma
  have hOrderCoprime : Nat.Coprime (orderOf gamma) 2 :=
    hCoprime.coprime_dvd_left (I.orderOf_dvd_natCard hGamma)
  have hGammaOne : gamma = 1 := by
    simpa using
      map_eq_one_of_isConj_inv_of_coprime_two (MonoidHom.id A) hConj hOrderCoprime
  rw [← hGenerates, hGammaOne]
  simp

/-- A finite subgroup is trivial if its cardinality is coprime to every
prime.  This is the arithmetic boundary step obtained by testing the same
finite inertia image in every positive residue characteristic. -/
theorem subgroup_eq_bot_of_card_coprime_every_prime
    {G : Type u} [Group G] (I : Subgroup G) [Finite I]
    (hCoprime : ∀ p : ℕ, p.Prime → Nat.Coprime (Nat.card I) p) :
    I = ⊥ := by
  apply (Subgroup.eq_bot_iff_card I).2
  apply Nat.eq_one_iff_not_exists_prime_dvd.mpr
  intro p hp hpdvd
  exact (hp.coprime_iff_not_dvd.mp (hCoprime p hp).symm) hpdvd

end ProCGroups.Boundary
