/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.FinitePlaceModel
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.IntegerRingComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Completion.LocalizedValuation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FinitePlaceArtin.Construction
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicLocalization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalPrimeFactorization
public import Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.SemilinearNaturality
public import Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicValuationComparison
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
public import Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuativeExtension
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import Mathlib.Tactic.Convert

/-!
# Canonical completion and localization structures for rational cyclotomic levels
-/

@[expose] public section

open scoped NNReal NumberField ValuativeRel
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open AlgebraicNumberTheory.Valuations
open HilbertRamification
open LocalClassFieldTheory
open LocalFieldTheory
open LocalFieldTheory.DiscreteValuationField
open LocalFieldTheory.DiscreteValuationField.Examples.Qp

-- Specialization at ℚ retains the generic comparison's `Algebra.id` owner.
/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[reducible] noncomputable def rationalFinitePlaceCompletionRatAlgebra
    (v : HeightOneSpectrum (𝓞 ℚ)) :
    Algebra ℚ (HeightOneSpectrum.adicAbv ℚ v).Completion :=
  AbsoluteValue.Completion.instAlgebra (HeightOneSpectrum.adicAbv ℚ v)

attribute [local instance] rationalFinitePlaceCompletionRatAlgebra

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicPrimeFact (q : Nat.Primes) : Fact q.1.Prime :=
  ⟨q.2⟩

attribute [local instance] rationalCyclotomicPrimeFact

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicLevelNeZero (m : ℕ+) : NeZero (m : ℕ) :=
  ⟨m.ne_zero⟩

attribute [local instance] rationalCyclotomicLevelNeZero

attribute [local instance]
  KummerTheory.rationalCyclotomicLevelFiniteDimensional
  KummerTheory.rationalCyclotomicLevelIsAbelianGalois

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[reducible]
noncomputable def rationalFinitePlaceBaseNontriviallyNormedField
    (q : Nat.Primes) :
    NontriviallyNormedField
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  absoluteValueExtension_completionNontriviallyNormedField
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q))
    (RayClass.adicAbv_isNontrivial
      (RayClass.rationalPrime q))

attribute [local instance] rationalFinitePlaceBaseNontriviallyNormedField

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalFinitePlaceBaseLocallyCompactSpace
    (q : Nat.Primes) :
    LocallyCompactSpace
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  AbsoluteValue.Completion.locallyCompactSpace
    (finitePlaceCompletionBaseMap_isometry
      (RayClass.rationalPrime q))

attribute [local instance] rationalFinitePlaceBaseLocallyCompactSpace

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalFinitePlaceBaseIsUltrametricDist
    (q : Nat.Primes) :
    IsUltrametricDist
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  finitePlaceArtinCompletionIsUltrametricDist
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (RayClass.rationalPrime q))

attribute [local instance] rationalFinitePlaceBaseIsUltrametricDist

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[reducible]
noncomputable def rationalFinitePlaceBaseValued
    (q : Nat.Primes) :
    Valued
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion ℝ≥0 :=
  finitePlaceArtinCompletionValued
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (RayClass.rationalPrime q))

attribute [local instance] rationalFinitePlaceBaseValued

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[reducible]
noncomputable def rationalFinitePlaceBaseValuativeRel
    (q : Nat.Primes) :
    ValuativeRel
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  finitePlaceLocalArtinCompletionValuativeRel
    (K := ℚ) (RayClass.rationalPrime q)

attribute [local instance] rationalFinitePlaceBaseValuativeRel

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalFinitePlaceBaseValuationIsNontrivial
    (q : Nat.Primes) :
    (Valued.v :
      Valuation
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        ℝ≥0).IsNontrivial :=
  (inferInstance :
    (NormedField.valuation
      (K :=
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion)).IsNontrivial)

attribute [local instance] rationalFinitePlaceBaseValuationIsNontrivial

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalFinitePlaceBaseValuationCompatible
    (q : Nat.Primes) :
    (Valued.v :
      Valuation
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation _

attribute [local instance] rationalFinitePlaceBaseValuationCompatible

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalFinitePlaceBaseValuativeRelIsNontrivial
    (q : Nat.Primes) :
    ValuativeRel.IsNontrivial
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (Valued.v :
      Valuation
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        ℝ≥0)).2 inferInstance

attribute [local instance] rationalFinitePlaceBaseValuativeRelIsNontrivial

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalFinitePlaceBaseIsValuativeTopology
    (q : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  isValuativeTopology_of_valued_ofValuation
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion ℝ≥0

attribute [local instance] rationalFinitePlaceBaseIsValuativeTopology

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalFinitePlaceBaseIsNonarchimedeanLocalField
    (q : Nat.Primes) :
    IsNonarchimedeanLocalField
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion :=
  finitePlaceLocalArtinCompletionIsNonarchimedeanLocalField
    (K := ℚ) (RayClass.rationalPrime q)

attribute [local instance] rationalFinitePlaceBaseIsNonarchimedeanLocalField

/-- The canonical nontrivially normed field structure on the completion of
`ℚ` at the rational prime `p`, exposed for principal-prime constructions. -/
@[reducible]
noncomputable def rationalPrimeFactorCompletionNontriviallyNormedField
    (p : Nat.Primes) :
    NontriviallyNormedField
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseNontriviallyNormedField p

/-- The completion of `ℚ` at `p` is locally compact. -/
theorem rationalPrimeFactorCompletionLocallyCompactSpace
    (p : Nat.Primes) :
    LocallyCompactSpace
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseLocallyCompactSpace p

/-- The completion of `ℚ` at `p` carries its canonical ultrametric distance. -/
theorem rationalPrimeFactorCompletionIsUltrametricDist
    (p : Nat.Primes) :
    IsUltrametricDist
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseIsUltrametricDist p

/-- The canonical `ℝ≥0`-valued structure on the completion of `ℚ` at `p`. -/
@[reducible]
noncomputable def rationalPrimeFactorCompletionValued
    (p : Nat.Primes) :
    Valued
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion ℝ≥0 :=
  rationalFinitePlaceBaseValued p

/-- The valuative relation induced by the canonical valuation on the
completion of `ℚ` at `p`. -/
@[reducible]
noncomputable def rationalPrimeFactorCompletionValuativeRel
    (p : Nat.Primes) :
    ValuativeRel
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseValuativeRel p

/-- The canonical valuation on the completion of `ℚ` at `p` is nontrivial. -/
theorem rationalPrimeFactorCompletionValuationIsNontrivial
    (p : Nat.Primes) :
    (Valued.v : Valuation
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion ℝ≥0).IsNontrivial :=
  rationalFinitePlaceBaseValuationIsNontrivial p

/-- The canonical valuation on the completion of `ℚ` at `p` is compatible
with its field structure. -/
theorem rationalPrimeFactorCompletionValuationCompatible
    (p : Nat.Primes) :
    (Valued.v : Valuation
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion ℝ≥0).Compatible :=
  rationalFinitePlaceBaseValuationCompatible p

/-- The canonical valuative relation on the completion at `p` is nontrivial. -/
theorem rationalPrimeFactorCompletionValuativeRelIsNontrivial
    (p : Nat.Primes) :
    ValuativeRel.IsNontrivial
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseValuativeRelIsNontrivial p

/-- The completion topology at `p` is induced by its canonical valuation. -/
theorem rationalPrimeFactorCompletionIsValuativeTopology
    (p : Nat.Primes) :
    IsValuativeTopology
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseIsValuativeTopology p

/-- The completion of `ℚ` at `p` is a nonarchimedean local field. -/
theorem rationalPrimeFactorCompletionIsNonarchimedeanLocalField
    (p : Nat.Primes) :
    IsNonarchimedeanLocalField
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion :=
  rationalFinitePlaceBaseIsNonarchimedeanLocalField p

/-- The positive conductor of the `n`-th ramified cyclotomic level at
`p`. -/
def rationalCyclotomicPrincipalPrimeModulus
    (p : Nat.Primes) (n : ℕ) : ℕ+ :=
  ⟨p.1 ^ (n + 1), pow_pos p.2.pos (n + 1)⟩

/-- The rational finite-place completion used at the prime `p`. -/
abbrev RationalCyclotomicPrincipalPrimeCompletion
    (p : Nat.Primes) :=
  (HeightOneSpectrum.adicAbv ℚ
    (RayClass.rationalPrime p)).Completion

/-- The chosen localized cyclotomic field at level `p ^ (n + 1)`. -/
abbrev RationalCyclotomicPrincipalPrimeLocalizedLevel
    (p : Nat.Primes) (n : ℕ) :=
  rationalCyclotomicLocalizedCompletion
    (rationalCyclotomicPrincipalPrimeModulus p n)
    (RayClass.rationalPrime p)

/-- The valuation ring of the absolute-value completion at `q`, identified
with the standard p-adic integer ring `ℤ_q`. -/
noncomputable def rationalFinitePlaceCompletionIntegerRingEquivPadicInt
    (q : Nat.Primes) :
    𝒪[(HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion] ≃+*
      ℤ_[q.1] := by
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    RayClass.rationalPrime q
  let vQ := HeightOneSpectrum.adicAbv ℚ v
  let eConcreteIntegers :
      𝒪[vQ.Completion] ≃+*
        v.adicCompletionIntegers ℚ :=
    finitePlaceCompletionIntegerRingEquiv v
  exact
    eConcreteIntegers.trans
      (PadicInt.adicCompletionIntegersEquiv
        (𝓞 ℚ) q).symm.toRingEquiv

/-- The absolute-value completion at the rational prime `q`, identified
with the standard field `ℚ_q`. -/
noncomputable def rationalFinitePlaceCompletionRingEquivPadic
    (q : Nat.Primes) :
    (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion ≃+*
      ℚ_[q.1] :=
  IsFractionRing.ringEquivOfRingEquiv
    (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)

/-- The completion-to-`ℚ_q` equivalence respects the rational embedding. -/
theorem rationalFinitePlaceCompletionRingEquivPadic_algebraMap
    (q : Nat.Primes) (a : ℚ) :
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion a) =
      algebraMap ℚ ℚ_[q.1] a := by
  exact
    (rationalFinitePlaceCompletionRingEquivPadic q).toRingHom.map_rat_algebraMap a

/-- The completion field equivalence and its restriction to valuation
rings commute with the natural inclusions into the fields. -/
theorem rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe
    (q : Nat.Primes)
    (a :
      𝒪[(HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion]) :
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion a) =
      algebraMap ℤ_[q.1] ℚ_[q.1]
        (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q a) := by
  exact
    (IsFractionRing.ringEquivOfRingEquiv_algebraMap
      (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q) a)

open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension
  (valuation_hasExtension_of_valuationSubring_equiv) in
/-- The canonical rational-completion equivalence preserves the canonical
valuations. -/
theorem
    rationalFinitePlaceCompletionRingEquivPadic_semilinearValuationCompatible
    (p : Nat.Primes) :
    SemilinearValuationCompatible
      (RationalCyclotomicPrincipalPrimeCompletion p) ℚ_[p.1]
      (rationalFinitePlaceCompletionRingEquivPadic p) := by
  let F := RationalCyclotomicPrincipalPrimeCompletion p
  let eK := rationalFinitePlaceCompletionRingEquivPadic p
  let : Algebra F ℚ_[p.1] := eK.toRingHom.toAlgebra
  change
    (ValuativeRel.valuation F).HasExtension
      (ValuativeRel.valuation ℚ_[p.1])
  let eO :=
    (rationalFinitePlaceCompletionIntegerRingEquivPadicInt p).trans
      (padicIntEquivValuationSubring p.1)
  have hChosen :
      (localCompleteDVF F).valuation.HasExtension
        (padicDVRValuation p.1) := by
    change
      (localCompleteDVF F).valuation.HasExtension
        (padicCompleteDVF p.1).valuation
    apply
      valuation_hasExtension_of_valuationSubring_equiv
        (localCompleteDVF F)
        (padicCompleteDVF p.1)
        eO
    intro z
    change
      algebraMap
          (padicDVRValuation p.1).valuationSubring ℚ_[p.1]
          (padicIntEquivValuationSubring p.1
            (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
              p z)) =
        rationalFinitePlaceCompletionRingEquivPadic p
          (algebraMap 𝒪[F] F z)
    symm
    calc
      rationalFinitePlaceCompletionRingEquivPadic p
          (algebraMap 𝒪[F] F z) =
        algebraMap ℤ_[p.1] ℚ_[p.1]
          (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
            p z) :=
        rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe
          p z
      _ =
        algebraMap
          (padicDVRValuation p.1).valuationSubring ℚ_[p.1]
          (padicIntEquivValuationSubring p.1
            (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
              p z)) := by
        rw [PadicInt.algebraMap_apply,
          ValuationSubring.algebraMap_apply]
        exact
          (padicIntEquivValuationSubring_coe p.1
            (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
              p z)).symm
  have hBase :
      (ValuativeRel.valuation F).HasExtension
        (padicDVRValuation p.1) := by
    rw [← localCompleteDVF_valuation_eq]
    exact hChosen
  refine
    { val_isEquiv_comap := ?_ }
  exact
    hBase.val_isEquiv_comap.trans
      ((padicDVRValuation_isEquiv_valuativeRelValuation
        p.1).comap (algebraMap F ℚ_[p.1]))

/-- The rational prime, pulled back from `ℤ_q` to the valuation ring of
the absolute-value completion at `q`. -/
noncomputable def rationalPrimeFinitePlaceInteger
    (q : Nat.Primes) :
    𝒪[(HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion] :=
  (rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).symm
    (q.1 : ℤ_[q.1])

/-- The pulled-back rational prime is irreducible in the completion
valuation ring. -/
theorem rationalPrimeFinitePlaceInteger_irreducible
    (q : Nat.Primes) :
    Irreducible (rationalPrimeFinitePlaceInteger q) := by
  exact
    (MulEquiv.irreducible_iff
      (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
        q).symm.toMulEquiv).2
      ((PadicInt.prime_p :
        Prime (q.1 : ℤ_[q.1])).irreducible)

/-- Coercing the pulled-back prime to the completion field gives the
ordinary image of the rational number `q`. -/
theorem rationalPrimeFinitePlaceInteger_coe
    (q : Nat.Primes) :
    ((rationalPrimeFinitePlaceInteger q :
      𝒪[(HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion]) :
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion) =
      algebraMap ℚ
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (q.1 : ℚ) := by
  apply
    (rationalFinitePlaceCompletionRingEquivPadic q).injective
  change
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeFinitePlaceInteger q)) =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (q.1 : ℚ))
  calc
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeFinitePlaceInteger q)) =
      algebraMap ℤ_[q.1] ℚ_[q.1]
        ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
          (rationalPrimeFinitePlaceInteger q)) :=
        rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe
          q (rationalPrimeFinitePlaceInteger q)
    _ = (q.1 : ℚ_[q.1]) := by
      rw [rationalPrimeFinitePlaceInteger,
        (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
          q).apply_symm_apply,
        PadicInt.algebraMap_apply,
        PadicInt.coe_natCast]
    _ =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (q.1 : ℚ)) := by
      rw [
        rationalFinitePlaceCompletionRingEquivPadic_algebraMap]
      norm_num

/-- The rational prime as a field unit of its absolute-value completion. -/
noncomputable def rationalPrimeFinitePlaceFieldUnit
    (q : Nat.Primes) :
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completionˣ :=
  Units.mk0
    (rationalPrimeFinitePlaceInteger q :
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion)
    (by
      intro hzero
      exact
        (rationalPrimeFinitePlaceInteger_irreducible q).ne_zero
          (Subtype.ext hzero))

/-- In the inverse-standard local reciprocity normalization, the rational
prime itself has normalized additive value `-1`. -/
theorem rationalPrimeFinitePlaceFieldUnit_valuationMap
    (q : Nat.Primes) :
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          (rationalPrimeFinitePlaceFieldUnit q)) =
      -1 := by
  simpa [IsNonarchimedeanLocalField.valuationMap_apply] using
    (LocalFieldTheory.v_integerRingIrreducibleFieldUnit
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion
      (rationalPrimeFinitePlaceInteger q)
      (rationalPrimeFinitePlaceInteger_irreducible q)
      (rationalPrimeFinitePlaceFieldUnit q) rfl)

/-- The rational `q`-unit part of `x`, pulled back from `ℤ_qˣ` to the
valuation ring of the absolute-value completion. -/
noncomputable def rationalPrimeUnitFinitePlaceIntegerUnit
    (x : ℚˣ) (q : Nat.Primes) :
    𝒪[(HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion]ˣ :=
  Units.map
      (rationalFinitePlaceCompletionIntegerRingEquivPadicInt
        q).symm.toMonoidHom
    (padicIntUnitOfRat q
      (rationalPrimeUnit x q : ℚ)
      (rationalPrimeUnit x q).ne_zero
      (padicValRat_rationalPrimeUnit x q))

/-- Forgetting the integrality proof from the pulled-back `q`-unit gives
the ordinary image of the rational `q`-unit in the completion field. -/
theorem rationalPrimeUnitFinitePlaceIntegerUnit_coe
    (x : ℚˣ) (q : Nat.Primes) :
    (((rationalPrimeUnitFinitePlaceIntegerUnit x q :
        𝒪[(HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion]ˣ) :
        𝒪[(HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion]) :
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion) =
      algebraMap ℚ
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (rationalPrimeUnit x q : ℚ) := by
  apply
    (rationalFinitePlaceCompletionRingEquivPadic q).injective
  change
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
            𝒪[(HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion])) =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeUnit x q : ℚ))
  calc
    rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion]
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
          𝒪[(HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion])) =
      algebraMap ℤ_[q.1] ℚ_[q.1]
        ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q)
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
            𝒪[(HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion])) :=
        rationalFinitePlaceCompletionIntegerRingEquivPadicInt_coe q
          (rationalPrimeUnitFinitePlaceIntegerUnit x q :
            𝒪[(HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion])
    _ =
      ((padicIntUnitOfRat q
        (rationalPrimeUnit x q : ℚ)
        (rationalPrimeUnit x q).ne_zero
        (padicValRat_rationalPrimeUnit x q) :
          ℤ_[q.1]) : ℚ_[q.1]) := by
      rw [rationalPrimeUnitFinitePlaceIntegerUnit]
      simp only [Units.coe_map, PadicInt.algebraMap_apply]
      exact congrArg (fun z : ℤ_[q.1] => (z : ℚ_[q.1]))
        ((rationalFinitePlaceCompletionIntegerRingEquivPadicInt q).apply_symm_apply _)
    _ = ((rationalPrimeUnit x q : ℚ) : ℚ_[q.1]) := by
      rw [padicIntUnitOfRat_coe]
    _ =
      rationalFinitePlaceCompletionRingEquivPadic q
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion
          (rationalPrimeUnit x q : ℚ)) := by
      rw [
        rationalFinitePlaceCompletionRingEquivPadic_algebraMap]
      exact (map_ratCast (algebraMap ℚ ℚ_[q.1])
        (rationalPrimeUnit x q : ℚ)).symm

/-- The completion field unit underlying the pulled-back rational `q`-unit
has normalized additive value zero. -/
theorem rationalPrimeUnitFinitePlaceField_valuationMap
    (x : ℚˣ) (q : Nat.Primes) :
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          (IsNonarchimedeanLocalField.integerUnitsToFieldUnits
            (HeightOneSpectrum.adicAbv ℚ
              (RayClass.rationalPrime q)).Completion
            (rationalPrimeUnitFinitePlaceIntegerUnit x q))) =
      0 := by
  rw [IsNonarchimedeanLocalField.valuationMap_apply]
  exact
    IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime q)).Completion
      (rationalPrimeUnitFinitePlaceIntegerUnit x q)

/-- The rational prime `q`, regarded as a unit of `ℚ`. -/
def rationalPrimeGeneratorUnit (q : Nat.Primes) : ℚˣ :=
  Units.mk0 (q.1 : ℚ) (by exact_mod_cast q.2.ne_zero)

/-- The underlying rational number of the prime generator unit is `q`. -/
@[simp]
theorem rationalPrimeGeneratorUnit_coe (q : Nat.Primes) :
    (rationalPrimeGeneratorUnit q : ℚ) = q.1 :=
  rfl

/-- Reattaching the removed `q`-power to the rational `q`-unit recovers
the original rational field unit. -/
theorem rationalPrimeGeneratorUnit_zpow_mul_rationalPrimeUnit
    (x : ℚˣ) (q : Nat.Primes) :
    rationalPrimeGeneratorUnit q ^
          padicValRat q.1 (x : ℚ) *
        rationalPrimeUnit x q =
      x := by
  rw [rationalPrimeGeneratorUnit, rationalPrimeUnit,
    ← mul_assoc, ← zpow_add]
  rw [add_neg_cancel, zpow_zero, one_mul]

/-- The source unit in the absolute-value completion represented by the
finite component of a rational principal idele. -/
noncomputable def rationalPrincipalFinitePlaceInput
    (x : ℚˣ) (q : Nat.Primes) :
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completionˣ :=
  (finitePlaceCompletionUnitsContinuousMulEquiv
      (RayClass.rationalPrime q)).symm
    (IdeleGroup.finiteComponent
      (RayClass.rationalPrime q)
      (IdeleGroup.principalIdele ℚ x))

/-- The source unit represented by a principal finite component is the
ordinary image of the rational field unit in the absolute-value
completion. -/
theorem rationalPrincipalFinitePlaceInput_eq_algebraMap
    (x : ℚˣ) (q : Nat.Primes) :
    rationalPrincipalFinitePlaceInput x q =
      Units.map
        (algebraMap ℚ
          (HeightOneSpectrum.adicAbv ℚ
            (RayClass.rationalPrime q)).Completion).toMonoidHom
        x := by
  apply Units.ext
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    RayClass.rationalPrime q
  let vQ := HeightOneSpectrum.adicAbv ℚ v
  let component : (v.adicCompletion ℚ)ˣ :=
    IdeleGroup.finiteComponent v
      (IdeleGroup.principalIdele ℚ x)
  apply (finitePlaceCompletionRingEquiv v).injective
  change
    finitePlaceCompletionRingEquiv v
        (rationalPrincipalFinitePlaceInput x q : vQ.Completion) =
      finitePlaceCompletionRingEquiv v
        (algebraMap ℚ vQ.Completion (x : ℚ))
  have hCompletion :
      finitePlaceCompletionRingEquiv v
          (rationalPrincipalFinitePlaceInput x q :
            vQ.Completion) =
        (component : v.adicCompletion ℚ) := by
    have hUnits :=
      congrArg Units.val
        ((finitePlaceCompletionUnitsContinuousMulEquiv v).apply_symm_apply
          component)
    exact hUnits
  have hComponent :
      (component : v.adicCompletion ℚ) =
        algebraMap ℚ (v.adicCompletion ℚ) (x : ℚ) := by
    apply (Padic.adicCompletionEquiv (𝓞 ℚ) q).symm.injective
    calc
      (Padic.adicCompletionEquiv (𝓞 ℚ) q).symm
          (component : v.adicCompletion ℚ) =
        algebraMap ℚ ℚ_[q.1] (x : ℚ) := by
          dsimp only [component]
          rw [IdeleGroup.finiteComponent_principalIdele]
          exact
            (Padic.adicCompletionEquiv
              (𝓞 ℚ) q).symm.commutes (x : ℚ)
      _ = (Padic.adicCompletionEquiv (𝓞 ℚ) q).symm
          (algebraMap ℚ (v.adicCompletion ℚ) (x : ℚ)) := by
        symm
        exact
          (Padic.adicCompletionEquiv
            (𝓞 ℚ) q).symm.commutes (x : ℚ)
  calc
    finitePlaceCompletionRingEquiv v
        (rationalPrincipalFinitePlaceInput x q :
          vQ.Completion) =
      (component : v.adicCompletion ℚ) := hCompletion
    _ = algebraMap ℚ (v.adicCompletion ℚ) (x : ℚ) := hComponent
    _ = finitePlaceCompletionRingEquiv v
        (algebraMap ℚ vQ.Completion (x : ℚ)) := by
      symm
      exact
        (finitePlaceCompletionAlgEquiv (K := ℚ) v).commutes (x : ℚ)

/-- The normalized local exponent of a rational principal finite
component is the negative of the usual `q`-adic exponent.  The minus sign
records the inverse-standard local reciprocity convention in which a
prime element has normalized value `-1`. -/
theorem rationalPrincipalFiniteComponent_valuationMap
    (x : ℚˣ) (q : Nat.Primes) :
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          ((finitePlaceCompletionUnitsContinuousMulEquiv
            (RayClass.rationalPrime q)).symm
            (IdeleGroup.finiteComponent
              (RayClass.rationalPrime q)
              (IdeleGroup.principalIdele ℚ x)))) =
      -padicValRat q.1 (x : ℚ) := by
  let F :=
    (HeightOneSpectrum.adicAbv ℚ
      (RayClass.rationalPrime q)).Completion
  let embed : ℚˣ →* Fˣ :=
    Units.map (algebraMap ℚ F).toMonoidHom
  let primeUnit : Fˣ :=
    rationalPrimeFinitePlaceFieldUnit q
  let integralUnit : 𝒪[F]ˣ :=
    rationalPrimeUnitFinitePlaceIntegerUnit x q
  let unitPart : Fˣ :=
    IsNonarchimedeanLocalField.integerUnitsToFieldUnits
      F integralUnit
  have hInput :
      rationalPrincipalFinitePlaceInput x q =
        embed x := by
    exact rationalPrincipalFinitePlaceInput_eq_algebraMap x q
  have hPrime :
      embed (rationalPrimeGeneratorUnit q) =
        primeUnit := by
    apply Units.ext
    exact
      (rationalPrimeFinitePlaceInteger_coe q).symm
  have hUnit :
      embed (rationalPrimeUnit x q) =
        unitPart := by
    apply Units.ext
    exact
      (rationalPrimeUnitFinitePlaceIntegerUnit_coe
        x q).symm
  change
    IsNonarchimedeanLocalField.valuationMap F
        (Additive.ofMul
          (rationalPrincipalFinitePlaceInput x q)) =
      -padicValRat q.1 (x : ℚ)
  rw [hInput]
  conv_lhs =>
    rw [← rationalPrimeGeneratorUnit_zpow_mul_rationalPrimeUnit
      x q]
  rw [map_mul, map_zpow, hPrime, hUnit,
    IsNonarchimedeanLocalField.valuationMap_ofMul_mul,
    IsNonarchimedeanLocalField.valuationMap_ofMul_zpow,
    rationalPrimeFinitePlaceFieldUnit_valuationMap,
    rationalPrimeUnitFinitePlaceField_valuationMap]
  ring

/-- The principal finite component of the rational prime itself has
normalized local exponent `-1`. -/
theorem rationalPrimePrincipalFiniteComponent_valuationMap
    (q : Nat.Primes) :
    IsNonarchimedeanLocalField.valuationMap
        (HeightOneSpectrum.adicAbv ℚ
          (RayClass.rationalPrime q)).Completion
        (Additive.ofMul
          ((finitePlaceCompletionUnitsContinuousMulEquiv
            (RayClass.rationalPrime q)).symm
            (IdeleGroup.finiteComponent
              (RayClass.rationalPrime q)
              (IdeleGroup.principalIdele ℚ
                (rationalPrimeGeneratorUnit q))))) =
      -1 := by
  rw [rationalPrincipalFiniteComponent_valuationMap,
    rationalPrimeGeneratorUnit_coe,
    padicValRat.self q.2.one_lt]

/-- A cyclotomic automorphism which raises the selected primitive root to
the `q`-th power has cyclotomic character equal to the residue-prime unit. -/
theorem rationalCyclotomicLevel_galEquivZMod_eq_unitOfCoprime
    (m : ℕ+) (q : Nat.Primes)
    (hq : ¬ q.1 ∣ (m : ℕ))
    (σ : KummerTheory.rationalCyclotomicLevel m ≃ₐ[ℚ]
      KummerTheory.rationalCyclotomicLevel m)
    (hσ :
      σ (rationalCyclotomicLevelPrimitiveRoot m) =
        rationalCyclotomicLevelPrimitiveRoot m ^ q.1) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (m : ℕ) (KummerTheory.rationalCyclotomicLevel m) σ =
      ZMod.unitOfCoprime q.1
        (q.2.coprime_iff_not_dvd.mpr hq) := by
  let ζ := rationalCyclotomicLevelPrimitiveRoot m
  have hζ : IsPrimitiveRoot ζ (m : ℕ) :=
    rationalCyclotomicLevelPrimitiveRoot_isPrimitiveRoot m
  have hCharacterRoot :
      σ ζ =
        ζ ^
          (IsCyclotomicExtension.Rat.galEquivZMod
            (m : ℕ) (KummerTheory.rationalCyclotomicLevel m) σ).val.val :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (m : ℕ) (KummerTheory.rationalCyclotomicLevel m) σ
      hζ.pow_eq_one
  have hPowers :
      ζ ^
          (IsCyclotomicExtension.Rat.galEquivZMod
            (m : ℕ) (KummerTheory.rationalCyclotomicLevel m) σ).val.val =
        ζ ^ q.1 :=
    hCharacterRoot.symm.trans hσ
  rw [(hζ.isOfFinOrder m.ne_zero).pow_inj_mod,
    ← hζ.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff',
    ZMod.natCast_val] at hPowers
  apply Units.ext
  simpa using hPowers

/-- The rational finite place used in the cyclotomic Artin calculation. -/
abbrev rationalCyclotomicArtinPlace (q : Nat.Primes) :
    HeightOneSpectrum (𝓞 ℚ) :=
  RayClass.rationalPrime q

/-- The absolute value of the rational cyclotomic base at a prime. -/
abbrev rationalCyclotomicArtinBaseAbv (q : Nat.Primes) :
    AbsoluteValue ℚ ℝ :=
  rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)

/-- The rational cyclotomic field at a positive level. -/
abbrev rationalCyclotomicArtinLevel (m : ℕ+) :=
  KummerTheory.rationalCyclotomicLevel m

/-- The chosen extension of the rational prime to the cyclotomic field. -/
abbrev rationalCyclotomicArtinExtension
    (m : ℕ+) (q : Nat.Primes) :
    AbsoluteValueExtension
      (rationalCyclotomicArtinBaseAbv q)
      (rationalCyclotomicArtinLevel m) :=
  rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q)

/-- The chosen localization of the rational cyclotomic level. -/
abbrev rationalCyclotomicArtinLocalizedField
    (m : ℕ+) (q : Nat.Primes) :=
  rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[reducible]
noncomputable def rationalCyclotomicArtinExtensionAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra ℚ
      (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q)).1.Completion :=
  AbsoluteValue.extensionCompletionAlgebra
    (K := ℚ) (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q)).1

attribute [local instance] rationalCyclotomicArtinExtensionAlgebra

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[reducible]
noncomputable def rationalCyclotomicArtinExtensionSMul
    (m : ℕ+) (q : Nat.Primes) :
    SMul ℚ
      (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q)).1.Completion :=
  (rationalCyclotomicArtinExtensionAlgebra m q).toSMul

attribute [local instance] rationalCyclotomicArtinExtensionSMul

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[reducible]
noncomputable def rationalCyclotomicArtinCompletionAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion
      (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q)).1.Completion :=
  AbsoluteValue.completionAlgebra
    (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q))
    (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q)).1
    (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q)).2

attribute [local instance] rationalCyclotomicArtinCompletionAlgebra

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[reducible]
noncomputable def rationalCyclotomicArtinLocalizedAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) :=
  finitePlaceLocalArtinLocalizedAlgebra
    (K := ℚ) (L := (KummerTheory.rationalCyclotomicLevel m))
    (RayClass.rationalPrime q)
    (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q))

attribute [local instance] rationalCyclotomicArtinLocalizedAlgebra

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[instance_reducible]
noncomputable def rationalCyclotomicArtinLocalizedGlobalAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra ℚ (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) :=
  LocalClassFieldTheory.localizedCompletionGlobalAlgebra
    (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q))
    (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q))

attribute [local instance] rationalCyclotomicArtinLocalizedGlobalAlgebra

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[instance_reducible]
noncomputable def rationalCyclotomicArtinLocalizedGlobalSMul
    (m : ℕ+) (q : Nat.Primes) :
    SMul ℚ (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) :=
  (rationalCyclotomicArtinLocalizedGlobalAlgebra m q).toSMul

attribute [local instance] rationalCyclotomicArtinLocalizedGlobalSMul

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedScalarTower
    (m : ℕ+) (q : Nat.Primes) :
    IsScalarTower ℚ
      (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) := by
  exact IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

attribute [local instance] rationalCyclotomicArtinLocalizedScalarTower

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedFiniteDimensional
    (m : ℕ+) (q : Nat.Primes) :
    FiniteDimensional
      (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) :=
  finitePlaceLocalArtinFiniteDimensional
    (K := ℚ) (L := (KummerTheory.rationalCyclotomicLevel m))
    (RayClass.rationalPrime q)
    (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q))

attribute [local instance] rationalCyclotomicArtinLocalizedFiniteDimensional

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedIsAbelianGalois
    (m : ℕ+) (q : Nat.Primes) :
    IsAbelianGalois
      (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) :=
  finitePlaceLocalArtinIsAbelianGalois
    (K := ℚ) (L := (KummerTheory.rationalCyclotomicLevel m))
    (RayClass.rationalPrime q)
    (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q))
    (inferInstance :
      FiniteDimensional ℚ (KummerTheory.rationalCyclotomicLevel m))

attribute [local instance] rationalCyclotomicArtinLocalizedIsAbelianGalois

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedIsSeparable
    (m : ℕ+) (q : Nat.Primes) :
    Algebra.IsSeparable
      (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) :=
  (rationalCyclotomicArtinLocalizedIsAbelianGalois m q).toIsGalois.to_isSeparable

attribute [local instance] rationalCyclotomicArtinLocalizedIsSeparable

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedIsCyclotomic
    (m : ℕ+) (q : Nat.Primes) :
    IsCyclotomicExtension {(m : ℕ)}
      (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) :=
  rationalCyclotomicLevel_localizedCompletion_isCyclotomicExtension
    m (RayClass.rationalPrime q)

attribute [local instance] rationalCyclotomicArtinLocalizedIsCyclotomic

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinExtensionFiniteDimensional
    (m : ℕ+) (q : Nat.Primes) :
    FiniteDimensional
      (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion
      (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q)).1.Completion :=
  completionModuleFinite
    (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q))
    (RayClass.adicAbv_isNontrivial
      (RayClass.rationalPrime q))
    (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q))

attribute [local instance] rationalCyclotomicArtinExtensionFiniteDimensional

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinExtensionContinuousSMul
    (m : ℕ+) (q : Nat.Primes) :
    ContinuousSMul
      (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion
      (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q)).1.Completion :=
  continuousSMul_of_algebraMap _ _
    (AbsoluteValue.completionMap_isometry
      (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q))
      (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q)).1
      (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q)).2).continuous

attribute [local instance] rationalCyclotomicArtinExtensionContinuousSMul

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinExtensionLocallyCompact
    (m : ℕ+) (q : Nat.Primes) :
    LocallyCompactSpace
      (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q)).1.Completion :=
  LocallyCompactSpace.of_finiteDimensional_of_complete
    (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion
    (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q)).1.Completion

attribute [local instance] rationalCyclotomicArtinExtensionLocallyCompact

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedLocallyCompact
    (m : ℕ+) (q : Nat.Primes) :
    LocallyCompactSpace
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) := by
  let e : (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) ≃ᵢ
      (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q)).1.Completion :=
    { toEquiv :=
        (localizedCompletionEquivCompletion
          (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q))
          (RayClass.adicAbv_isNontrivial (RayClass.rationalPrime q))
          (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q))).toEquiv
      isometry_toFun := Isometry.of_dist_eq fun _ _ => rfl }
  exact e.toHomeomorph.locallyCompactSpace_iff.mpr inferInstance

attribute [local instance] rationalCyclotomicArtinLocalizedLocallyCompact

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedIsUltrametricDist
    (m : ℕ+) (q : Nat.Primes) :
    IsUltrametricDist
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) :=
  localizedCompletionIsUltrametricDist
    (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q))
    (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (RayClass.rationalPrime q))

attribute [local instance] rationalCyclotomicArtinLocalizedIsUltrametricDist

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[instance_reducible]
noncomputable def rationalCyclotomicArtinLocalizedValued
    (m : ℕ+) (q : Nat.Primes) :
    Valued (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) ℝ≥0 :=
  localizedCompletionFinitePlaceValued
    (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q))
    (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (RayClass.rationalPrime q))

attribute [local instance] rationalCyclotomicArtinLocalizedValued

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[reducible]
noncomputable def rationalCyclotomicArtinLocalizedValuativeRel
    (m : ℕ+) (q : Nat.Primes) :
    ValuativeRel (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) :=
  localizedCompletionFinitePlaceValuativeRel
    (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q))
    (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (RayClass.rationalPrime q))

attribute [local instance] rationalCyclotomicArtinLocalizedValuativeRel

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedValuationCompatible
    (m : ℕ+) (q : Nat.Primes) :
    (Valued.v : Valuation
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) ℝ≥0).Compatible :=
  Valuation.Compatible.ofValuation _

attribute [local instance] rationalCyclotomicArtinLocalizedValuationCompatible

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedValuationHasExtension
    (m : ℕ+) (q : Nat.Primes) :
    Valuation.HasExtension
      (ValuativeRel.valuation
        (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion)
      (ValuativeRel.valuation
        (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q))) :=
  localizedCompletionValuationHasExtension
    (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q))
    (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (RayClass.rationalPrime q))

attribute [local instance] rationalCyclotomicArtinLocalizedValuationHasExtension

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedValuationIsNontrivial
    (m : ℕ+) (q : Nat.Primes) :
    (ValuativeRel.valuation
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q))).IsNontrivial :=
  Valuation.IsNontrivial.of_hasExtension
    (ValuativeRel.valuation
      (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion)
    (ValuativeRel.valuation
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)))

attribute [local instance] rationalCyclotomicArtinLocalizedValuationIsNontrivial

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedValuativeRelIsNontrivial
    (m : ℕ+) (q : Nat.Primes) :
    ValuativeRel.IsNontrivial
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) :=
  (ValuativeRel.isNontrivial_iff_isNontrivial
    (ValuativeRel.valuation
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)))).2 inferInstance

attribute [local instance] rationalCyclotomicArtinLocalizedValuativeRelIsNontrivial

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedIsValuativeTopology
    (m : ℕ+) (q : Nat.Primes) :
    IsValuativeTopology
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) :=
  isValuativeTopology_of_valued_ofValuation
    (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) ℝ≥0

attribute [local instance] rationalCyclotomicArtinLocalizedIsValuativeTopology

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedIsNonarchimedeanLocalField
    (m : ℕ+) (q : Nat.Primes) :
    IsNonarchimedeanLocalField
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) :=
  { toIsValuativeTopology := inferInstance
    toLocallyCompactSpace := inferInstance
    toIsNontrivial := inferInstance }

attribute [local instance] rationalCyclotomicArtinLocalizedIsNonarchimedeanLocalField

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[instance_reducible]
noncomputable def rationalCyclotomicArtinLocalizedIntegerAlgebra
    (m : ℕ+) (q : Nat.Primes) :
    Algebra
      𝒪[(rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion]
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) :=
  Algebra.ofSubsemiring
    𝒪[(rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion]

attribute [local instance] rationalCyclotomicArtinLocalizedIntegerAlgebra

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedIsIntegralClosure
    (m : ℕ+) (q : Nat.Primes) :
    IsIntegralClosure
      𝒪[(rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q))]
      𝒪[(rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion]
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)) :=
  localizedCompletionIsIntegralClosureWithExtension
    (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q))
    (rationalCyclotomicChosenFinitePlaceExtension m (RayClass.rationalPrime q))
    (RayClass.adicAbv_isNontrivial
      (RayClass.rationalPrime q))
    (HeightOneSpectrum.isNonarchimedean_adicAbv
      ℚ (RayClass.rationalPrime q))

attribute [local instance] rationalCyclotomicArtinLocalizedIsIntegralClosure

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedIntegerModuleFinite
    (m : ℕ+) (q : Nat.Primes) :
    Module.Finite
      𝒪[(rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion]
      𝒪[(rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q))] := by
  let K := (rationalCyclotomicAdicAbsoluteValue (RayClass.rationalPrime q)).Completion
  let L : Type := rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime q)
  exact @integerRing_moduleFinite_of_isIntegralClosure K L
    _ _ _ _ _ _ _ _ _ _ (rationalCyclotomicArtinLocalizedIsIntegralClosure m q)

attribute [local instance] rationalCyclotomicArtinLocalizedIntegerModuleFinite

end Reciprocity
end GlobalClassFieldTheory
