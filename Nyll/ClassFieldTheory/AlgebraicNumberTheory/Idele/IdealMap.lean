/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.ClassFieldTheory.Algebra.RestrictedProduct.Valuation
import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The ideal attached to an idele

This file formalizes the ideal map from ideles. Its construction
is explicit: local discrete valuations form a finitely supported integer
vector, and unique factorization of fractional ideals identifies that vector
with a nonzero fractional ideal.  We prove both stages surjective and identify
the kernel with the ideles integral at every finite place.
-/



open scoped NumberField RestrictedProduct WithZero
open NumberField IsDedekindDomain

noncomputable section


variable {K : Type*} [Field K] [NumberField K]

namespace FiniteIdeleGroup

/-- The exponent of a local multiplicative element, normalized so that a
uniformizer has exponent one. -/
def localOrder (v : HeightOneSpectrum (𝓞 K)) :
    (v.adicCompletion K)ˣ →* Multiplicative ℤ :=
  RestrictedProduct.DiscreteValuation.localOrder (v.adicCompletion K)

@[simp]
theorem localOrder_apply (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    (localOrder v x).toAdd =
      -WithZero.log (Valued.v (x : v.adicCompletion K)) :=
  RestrictedProduct.DiscreteValuation.localOrder_apply (v.adicCompletion K) x

@[simp]
theorem localOrder_eq_zero_iff (v : HeightOneSpectrum (𝓞 K))
    (x : (v.adicCompletion K)ˣ) :
    (localOrder v x).toAdd = 0 ↔
      x ∈ (v.adicCompletionIntegers K).units :=
  RestrictedProduct.DiscreteValuation.localOrder_eq_zero_iff (v.adicCompletion K) x

/-- The set of finite places where a finite idele is not an integral unit is
finite. -/
theorem finite_nonLocalUnits (a : FiniteIdeleGroup K) :
    {v : HeightOneSpectrum (𝓞 K) |
      a v ∉ (v.adicCompletionIntegers K).units}.Finite :=
  RestrictedProduct.DiscreteValuation.finite_nonLocalUnits
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) a

/-- The finitely supported family of normalized local orders of a finite
idele. -/
def valuationVectorAdd (a : FiniteIdeleGroup K) :
    HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  RestrictedProduct.DiscreteValuation.valuationVectorAdd
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) a

@[simp]
theorem valuationVectorAdd_apply (a : FiniteIdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    valuationVectorAdd a v = (localOrder v (a v)).toAdd :=
  RestrictedProduct.DiscreteValuation.valuationVectorAdd_apply
    (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) a v

/-- The finite valuation vector is a homomorphism from finite ideles to the
free abelian group on finite places. -/
def valuationVector :
    FiniteIdeleGroup K →* Multiplicative
      (HeightOneSpectrum (𝓞 K) →₀ ℤ) :=
  RestrictedProduct.DiscreteValuation.valuationVector
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)

@[simp]
theorem valuationVector_apply (a : FiniteIdeleGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    (valuationVector a).toAdd v =
      (localOrder v (a v)).toAdd :=
  RestrictedProduct.DiscreteValuation.valuationVector_apply
    (fun w : HeightOneSpectrum (𝓞 K) => w.adicCompletion K) a v

/-- A chosen local element of prescribed normalized order. -/
def chosenLocalOrderSection (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (v.adicCompletion K)ˣ :=
  RestrictedProduct.DiscreteValuation.chosenLocalOrderSection (v.adicCompletion K)
    (HeightOneSpectrum.valuedAdicCompletion_surjective K v) n

@[simp]
theorem localOrder_chosenLocalOrderSection
    (v : HeightOneSpectrum (𝓞 K)) (n : ℤ) :
    (localOrder v (chosenLocalOrderSection v n)).toAdd = n :=
  RestrictedProduct.DiscreteValuation.localOrder_chosenLocalOrderSection
    (v.adicCompletion K) (HeightOneSpectrum.valuedAdicCompletion_surjective K v) n

/-- A finite idele with a prescribed finitely supported valuation vector. -/
def valuationVectorSection
    (e : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    FiniteIdeleGroup K :=
  RestrictedProduct.DiscreteValuation.valuationVectorSection
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => HeightOneSpectrum.valuedAdicCompletion_surjective K v) e

@[simp]
theorem valuationVector_valuationVectorSection
    (e : HeightOneSpectrum (𝓞 K) →₀ ℤ) :
    valuationVector (valuationVectorSection e) =
      Multiplicative.ofAdd e :=
  RestrictedProduct.DiscreteValuation.valuationVector_valuationVectorSection
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => HeightOneSpectrum.valuedAdicCompletion_surjective K v) e

theorem valuationVector_surjective :
    Function.Surjective (valuationVector (K := K)) :=
  RestrictedProduct.DiscreteValuation.valuationVector_surjective
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)
    (fun v => HeightOneSpectrum.valuedAdicCompletion_surjective K v)

end FiniteIdeleGroup

/-- The group of nonzero fractional ideals of a number field. -/
abbrev FractionalIdealGroup (K : Type*) [Field K] [NumberField K] :=
  (FractionalIdeal (nonZeroDivisors (𝓞 K)) K)ˣ

namespace FractionalIdealGroup

/-- The fractional ideal represented by a finite prime. -/
def prime (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdealGroup K :=
  Units.mk0 (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
    (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)

/-- The homomorphism sending an integer exponent to the corresponding
power of a finite prime. -/
def primePowerHom (v : HeightOneSpectrum (𝓞 K)) :
    Multiplicative ℤ →* FractionalIdealGroup K :=
  MonoidHom.mk' (fun n => prime v ^ n.toAdd) fun m n => by
    simp [zpow_add]

/-- Reconstruct a fractional ideal from its finitely supported vector
of prime exponents. -/
def factorization :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) →*
      FractionalIdealGroup K :=
  MonoidHom.mk' (fun exps =>
      exps.toAdd.prod fun v n => primePowerHom v (Multiplicative.ofAdd n))
    fun a b => by
      exact Finsupp.prod_hom_add_index (fun v => primePowerHom v)

@[simp]
theorem factorization_val (exps :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ)) :
    ((factorization exps : FractionalIdealGroup K) :
      FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      exps.toAdd.prod fun v n =>
        (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n := by
  classical
  simp [factorization, primePowerHom, prime, Finsupp.prod]

theorem finite_count_support (I : FractionalIdealGroup K) :
    {v : HeightOneSpectrum (𝓞 K) |
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0}.Finite :=
  Filter.eventually_cofinite.mp
    (FractionalIdeal.finite_factors
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))

/-- The finitely supported vector of prime exponents of a nonzero
fractional ideal. -/
def countVector (I : FractionalIdealGroup K) :
    HeightOneSpectrum (𝓞 K) →₀ ℤ :=
  Finsupp.onFinset (finite_count_support I).toFinset
    (fun v => FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K))
    (fun v hv => by
      rw [Set.Finite.mem_toFinset]
      exact hv)

@[simp]
theorem countVector_apply (I : FractionalIdealGroup K)
    (v : HeightOneSpectrum (𝓞 K)) :
    countVector I v =
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :=
  rfl

@[simp]
theorem count_factorization (exps :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ))
    (v : HeightOneSpectrum (𝓞 K)) :
    FractionalIdeal.count K v
      ((factorization exps : FractionalIdealGroup K) :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      exps.toAdd v := by
  rw [factorization_val]
  exact FractionalIdeal.count_finsuppProd K v exps.toAdd

theorem ext_count {I J : FractionalIdealGroup K}
    (h : ∀ v : HeightOneSpectrum (𝓞 K),
      FractionalIdeal.count K v
        (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) =
      FractionalIdeal.count K v
        (J : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) :
    I = J := by
  apply Units.ext
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      K (Units.ne_zero I),
    ← FractionalIdeal.finprod_heightOneSpectrum_factorization'
      K (Units.ne_zero J)]
  exact finprod_congr fun v => congrArg
    (fun n : ℤ =>
      (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ^ n) (h v)

theorem factorization_injective :
    Function.Injective (factorization (K := K)) := by
  intro a b hab
  apply Multiplicative.ext
  ext v
  rw [← count_factorization a v, ← count_factorization b v, hab]

theorem factorization_surjective :
    Function.Surjective (factorization (K := K)) := by
  intro I
  refine ⟨Multiplicative.ofAdd (countVector I), ?_⟩
  apply ext_count
  intro v
  rw [count_factorization]
  change countVector I v =
    FractionalIdeal.count K v
      (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)
  exact countVector_apply I v

/-- Multiplicative unique factorization of nonzero fractional ideals by
finite primes. -/
def factorizationEquiv :
    Multiplicative (HeightOneSpectrum (𝓞 K) →₀ ℤ) ≃*
      FractionalIdealGroup K :=
  MulEquiv.ofBijective (factorization (K := K))
    ⟨factorization_injective, factorization_surjective⟩

end FractionalIdealGroup

namespace FiniteIdeleGroup

/-- The fractional ideal attached to a finite idele. -/
def fractionalIdeal :
    FiniteIdeleGroup K →* FractionalIdealGroup K :=
  (FractionalIdealGroup.factorizationEquiv (K := K)).toMonoidHom.comp
    (valuationVector (K := K))

theorem fractionalIdeal_surjective :
    Function.Surjective (fractionalIdeal (K := K)) :=
  (FractionalIdealGroup.factorizationEquiv (K := K)).surjective.comp
    valuationVector_surjective

/-- Finite ideles integral at every finite place. -/
def integralSubgroup : Subgroup (FiniteIdeleGroup K) :=
  RestrictedProduct.DiscreteValuation.integralSubgroup
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K)

@[simp]
theorem mem_integralSubgroup_iff (a : FiniteIdeleGroup K) :
    a ∈ integralSubgroup ↔
      ∀ v : HeightOneSpectrum (𝓞 K),
        a v ∈ (v.adicCompletionIntegers K).units :=
  Iff.rfl

theorem fractionalIdeal_ker :
    (fractionalIdeal (K := K)).ker = integralSubgroup := by
  apply Subgroup.ext
  intro a
  have hv := RestrictedProduct.DiscreteValuation.valuationVector_eq_one_iff
    (fun v : HeightOneSpectrum (𝓞 K) => v.adicCompletion K) a
  change valuationVector a = 1 ↔ a ∈ integralSubgroup at hv
  constructor
  · intro ha
    apply hv.1
    apply (FractionalIdealGroup.factorizationEquiv (K := K)).injective
    change fractionalIdeal a = FractionalIdealGroup.factorizationEquiv 1
    rw [map_one]
    exact ha
  · intro ha
    change FractionalIdealGroup.factorizationEquiv (valuationVector a) = 1
    rw [hv.2 ha, map_one]

/-- The ideal group as the quotient of finite ideles by the everywhere
integral finite ideles. -/
def quotientIntegralEquiv :
    FiniteIdeleGroup K ⧸ integralSubgroup ≃*
      FractionalIdealGroup K := by
  rw [← fractionalIdeal_ker]
  exact QuotientGroup.quotientKerEquivOfSurjective
    fractionalIdeal fractionalIdeal_surjective

end FiniteIdeleGroup

namespace IdeleGroup

/-- The fractional ideal attached to an idele. The archimedean components
do not contribute. -/
def fractionalIdeal :
    IdeleGroup K →* FractionalIdealGroup K :=
  (FiniteIdeleGroup.fractionalIdeal (K := K)).comp
    (MonoidHom.snd _ _)

theorem fractionalIdeal_surjective :
    Function.Surjective (fractionalIdeal (K := K)) := by
  intro I
  obtain ⟨a, rfl⟩ :=
    FiniteIdeleGroup.fractionalIdeal_surjective (K := K) I
  exact ⟨(1, a), rfl⟩

/-- Ideles integral at every finite place; this is the subgroup
`I_K^{S∞}`. -/
def integralAtFinitePlaces : Subgroup (IdeleGroup K) :=
  Subgroup.comap (MonoidHom.snd _ _)
    (FiniteIdeleGroup.integralSubgroup (K := K))

theorem fractionalIdeal_ker :
    (fractionalIdeal (K := K)).ker = integralAtFinitePlaces := by
  ext a
  change FiniteIdeleGroup.fractionalIdeal a.2 = 1 ↔
    a.2 ∈ FiniteIdeleGroup.integralSubgroup
  rw [← MonoidHom.mem_ker,
    FiniteIdeleGroup.fractionalIdeal_ker]

/-- The ideal group as the quotient of all ideles by those integral at
every finite place. -/
def quotientIntegralEquiv :
    IdeleGroup K ⧸ integralAtFinitePlaces ≃*
      FractionalIdealGroup K := by
  rw [← fractionalIdeal_ker]
  exact QuotientGroup.quotientKerEquivOfSurjective
    fractionalIdeal fractionalIdeal_surjective

/-- The canonical surjection from ideles to the ordinary ideal class
group. -/
def idealClass :
    IdeleGroup K →* ClassGroup (𝓞 K) :=
  (ClassGroup.mk K).comp (fractionalIdeal (K := K))

theorem idealClass_surjective :
    Function.Surjective (idealClass (K := K)) := by
  intro c
  induction c using ClassGroup.induction (R := 𝓞 K) K with
  | h I =>
      obtain ⟨a, ha⟩ := fractionalIdeal_surjective (K := K) I
      exact ⟨a, by simp [idealClass, ha]⟩

/-- A quotient form of the ideal-class map. The following results identify
this kernel with `I_K^{S∞} Kˣ`. -/
def quotientIdealClassKernelEquiv :
    IdeleGroup K ⧸ (idealClass (K := K)).ker ≃*
      ClassGroup (𝓞 K) :=
  QuotientGroup.quotientKerEquivOfSurjective
    idealClass idealClass_surjective

end IdeleGroup
