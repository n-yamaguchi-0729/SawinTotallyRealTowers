/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.RingTheory.DedekindDomain.Factorization

/-!
# Prime factorization of fractional ideals over a Dedekind domain

The standard fractional-ideal unit group is identified with finitely
supported integer exponents. The inverse is the prime-count vector itself.
-/

@[expose] public section

open scoped nonZeroDivisors
open IsDedekindDomain

universe u v

variable {R : Type u} {F : Type v}
    [CommRing R] [IsDedekindDomain R] [Field F]
    [Algebra R F] [IsFractionRing R F]

noncomputable section

namespace ClassFieldTheory.FractionalIdealFactorization

/-- The fractional ideal represented by a finite prime. -/
noncomputable def prime (v : HeightOneSpectrum R) :
    (FractionalIdeal R⁰ F)ˣ :=
  Units.mk0 (v.asIdeal : FractionalIdeal R⁰ F)
    (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- The homomorphism sending an integer exponent to the corresponding
power of a finite prime. -/
noncomputable def primePowerHom (v : HeightOneSpectrum R) :
    Multiplicative ℤ →* (FractionalIdeal R⁰ F)ˣ :=
  MonoidHom.mk' (fun n => prime v ^ n.toAdd) fun m n => by
    simp only [toAdd_mul, zpow_add]

/-- Reconstruct a fractional ideal from its finitely supported vector
of prime exponents. -/
noncomputable def factorization :
    Multiplicative (HeightOneSpectrum R →₀ ℤ) →*
      (FractionalIdeal R⁰ F)ˣ :=
  MonoidHom.mk' (fun exps =>
      exps.toAdd.prod fun v n => primePowerHom v (Multiplicative.ofAdd n))
    fun a b => by
      exact Finsupp.prod_hom_add_index (fun v => primePowerHom v)

/-- The underlying fractional ideal is the product of its prime powers. -/
@[simp]
theorem factorization_val (exps :
    Multiplicative (HeightOneSpectrum R →₀ ℤ)) :
    ((factorization exps : (FractionalIdeal R⁰ F)ˣ) :
      FractionalIdeal R⁰ F) =
      exps.toAdd.prod fun v n =>
        (v.asIdeal : FractionalIdeal R⁰ F) ^ n := by
  classical
  simp only [factorization, Finsupp.prod, primePowerHom, prime, MonoidHom.mk'_apply, toAdd_ofAdd,
    Units.coe_prod, Units.val_zpow_eq_zpow_val, Units.val_mk0]

/-- Only finitely many primes have nonzero count. -/
theorem finite_count_support (I : (FractionalIdeal R⁰ F)ˣ) :
    {v : HeightOneSpectrum R |
      FractionalIdeal.count F v
        (I : FractionalIdeal R⁰ F) ≠ 0}.Finite :=
  Filter.eventually_cofinite.mp
    (FractionalIdeal.finite_factors
      (I : FractionalIdeal R⁰ F))

/-- The fractional-ideal count of a nonzero integral ideal is its prime multiplicity. -/
theorem count_coeIdeal_eq_multiplicity (v : HeightOneSpectrum R) {I : Ideal R}
    (hI : I ≠ ⊥) :
    FractionalIdeal.count F v (I : FractionalIdeal R⁰ F) = (multiplicity v.asIdeal I : ℤ) := by
  classical
  rw [FractionalIdeal.count_coeIdeal F v hI,
    Ideal.count_associates_factors_eq hI v.isPrime v.ne_bot,
    v.count_normalizedFactors_eq_multiplicity hI]

/-- A nonzero integral ideal has nonzero prime multiplicity exactly when it lies in the prime. -/
theorem multiplicity_ne_zero_iff_le (v : HeightOneSpectrum R) {I : Ideal R} (hI : I ≠ ⊥) :
    multiplicity v.asIdeal I ≠ 0 ↔ I ≤ v.asIdeal := by
  have h := (FiniteMultiplicity.of_prime_left v.prime hI).pow_dvd_iff_le_multiplicity (k := 1)
  rw [pow_one, Ideal.dvd_iff_le, Nat.one_le_iff_ne_zero] at h
  exact h.symm

/-- The finitely supported vector of prime exponents of a nonzero
fractional ideal. -/
noncomputable def countVector (I : (FractionalIdeal R⁰ F)ˣ) :
    HeightOneSpectrum R →₀ ℤ :=
  Finsupp.onFinset (finite_count_support I).toFinset
    (fun v => FractionalIdeal.count F v
      (I : FractionalIdeal R⁰ F))
    (fun v hv => by
      rw [Set.Finite.mem_toFinset]
      exact hv)

/-- A coordinate of the count vector is the corresponding prime count. -/
@[simp]
theorem countVector_apply (I : (FractionalIdeal R⁰ F)ˣ)
    (v : HeightOneSpectrum R) :
    countVector I v =
      FractionalIdeal.count F v
        (I : FractionalIdeal R⁰ F) :=
  rfl

/-- Factorization has exactly the prescribed prime exponents. -/
@[simp]
theorem count_factorization (exps :
    Multiplicative (HeightOneSpectrum R →₀ ℤ))
    (v : HeightOneSpectrum R) :
    FractionalIdeal.count F v
      ((factorization exps : (FractionalIdeal R⁰ F)ˣ) :
        FractionalIdeal R⁰ F) =
      exps.toAdd v := by
  rw [factorization_val]
  exact FractionalIdeal.count_finsuppProd F v exps.toAdd

/-- Prime counts determine a nonzero fractional ideal. -/
theorem ext_count {I J : (FractionalIdeal R⁰ F)ˣ}
    (h : ∀ v : HeightOneSpectrum R,
      FractionalIdeal.count F v
        (I : FractionalIdeal R⁰ F) =
      FractionalIdeal.count F v
        (J : FractionalIdeal R⁰ F)) :
    I = J := by
  apply Units.ext
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      F (Units.ne_zero I),
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      F (Units.ne_zero J)]
  exact finprod_congr fun v => congrArg
    (fun n : ℤ =>
      (v.asIdeal : FractionalIdeal R⁰ F) ^ n) (h v)

/-- Distinct exponent vectors give distinct fractional ideals. -/
theorem factorization_injective :
    Function.Injective (factorization (R := R) (F := F)) := by
  intro a b hab
  apply Multiplicative.ext
  ext v
  rw [← count_factorization (F := F) a v, ← count_factorization (F := F) b v, hab]

/-- Every nonzero fractional ideal factors into prime powers. -/
theorem factorization_surjective :
    Function.Surjective (factorization (R := R) (F := F)) := by
  intro I
  refine ⟨Multiplicative.ofAdd (countVector I), ?_⟩
  apply ext_count
  intro v
  rw [count_factorization]
  change countVector I v =
    FractionalIdeal.count F v
      (I : FractionalIdeal R⁰ F)
  exact countVector_apply I v

/-- Multiplicative unique factorization of nonzero fractional ideals by
finite primes. -/
noncomputable def factorizationEquiv :
    Multiplicative (HeightOneSpectrum R →₀ ℤ) ≃*
      (FractionalIdeal R⁰ F)ˣ :=
  { factorization (R := R) (F := F) with
    invFun := fun I => Multiplicative.ofAdd (countVector I)
    left_inv := by
      intro e
      apply Multiplicative.ext
      ext v
      exact count_factorization e v
    right_inv := by
      intro I
      apply ext_count
      intro v
      exact count_factorization (Multiplicative.ofAdd (countVector I)) v }

/-- The inverse factorization map is the actual prime-count vector. -/
@[simp]
theorem factorizationEquiv_symm_toAdd (I : (FractionalIdeal R⁰ F)ˣ) :
    ((factorizationEquiv (R := R) (F := F)).symm I).toAdd = countVector I :=
  rfl

/-- Fractional ideals having count zero at every prime in a prescribed set. -/
def primeTo (S : Set (HeightOneSpectrum R)) :
    Subgroup (FractionalIdeal R⁰ F)ˣ where
  carrier := {I | ∀ v, v ∈ S → FractionalIdeal.count F v (I : FractionalIdeal R⁰ F) = 0}
  one_mem' v _ := FractionalIdeal.count_one F v
  mul_mem' {I J} hI hJ v hv := by
    rw [Units.val_mul,
      FractionalIdeal.count_mul F v (Units.ne_zero I) (Units.ne_zero J),
      hI v hv, hJ v hv, add_zero]
  inv_mem' {I} hI v hv := by
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv F v, hI v hv, neg_zero]

/-- A prime outside the prescribed set belongs to the corresponding prime-to subgroup. -/
noncomputable def primeToPrime (S : Set (HeightOneSpectrum R))
    (v : HeightOneSpectrum R) (hv : v ∉ S) : primeTo (F := F) S :=
  ⟨prime v, by
    intro w hw
    have hwv : w ≠ v := fun h => hv (h ▸ hw)
    change FractionalIdeal.count F w (v.asIdeal : FractionalIdeal R⁰ F) = 0
    exact FractionalIdeal.count_maximal_coprime F w hwv.symm⟩

/-- The prime-to generator has its original prime fractional ideal as value. -/
@[simp]
theorem primeToPrime_coe (S : Set (HeightOneSpectrum R))
    (v : HeightOneSpectrum R) (hv : v ∉ S) :
    (primeToPrime (F := F) S v hv : (FractionalIdeal R⁰ F)ˣ) = prime v :=
  rfl

/-- Homomorphisms out of a prime-to subgroup are determined by primes outside the set. -/
theorem primeTo_hom_ext (S : Set (HeightOneSpectrum R))
    {G : Type*} [Monoid G]
    (f g : primeTo (F := F) S →* G)
    (hprime : ∀ v (hv : v ∉ S),
      f (primeToPrime S v hv) = g (primeToPrime S v hv)) : f = g := by
  classical
  let P := primeTo (F := F) S
  let p (v : HeightOneSpectrum R) : P :=
    if hv : v ∉ S then primeToPrime S v hv else 1
  have hp (v : HeightOneSpectrum R) : f (p v) = g (p v) := by
    by_cases hv : v ∉ S
    · simpa only [p, dite_eq_left hv] using hprime v hv
    · simp only [p, dite_eq_right hv, map_one]
  apply MonoidHom.ext
  intro I
  let c := countVector (I : (FractionalIdeal R⁰ F)ˣ)
  have hfactor : factorization (Multiplicative.ofAdd c) =
      (I : (FractionalIdeal R⁰ F)ˣ) :=
    (factorizationEquiv (R := R) (F := F)).apply_symm_apply I
  have hI : I = c.prod (fun v e => p v ^ e) := by
    apply Subtype.ext
    change (I : (FractionalIdeal R⁰ F)ˣ) =
      (P.subtype : P →* (FractionalIdeal R⁰ F)ˣ) (c.prod (fun v e => p v ^ e))
    rw [← hfactor]
    change factorization (Multiplicative.ofAdd c) =
      (P.subtype : P →* (FractionalIdeal R⁰ F)ˣ)
        (c.support.prod (fun v => p v ^ c v))
    rw [map_prod]
    change c.support.prod (fun v => prime v ^ c v) =
      c.support.prod (fun v => (P.subtype : P →* (FractionalIdeal R⁰ F)ˣ) (p v ^ c v))
    apply Finset.prod_congr rfl
    intro v hv
    have hv' : v ∉ S := by
      intro hvm
      exact (Finsupp.mem_support_iff.mp hv) (I.property v hvm)
    rw [map_zpow]
    change prime v ^ c v = (p v : (FractionalIdeal R⁰ F)ˣ) ^ c v
    simp only [p, dite_eq_left hv', primeToPrime_coe]
  change I ∈ f.eqLocus g
  rw [hI]
  change c.support.prod (fun v => p v ^ c v) ∈ f.eqLocus g
  exact (f.eqLocus g).prod_mem fun v _ => (f.eqLocus g).zpow_mem (hp v) (c v)

end ClassFieldTheory.FractionalIdealFactorization
