/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.RationalCyclotomicCompletionComparison
public import Nyll.ClassFieldTheory.LubinTate.FiniteLevel.LevelAbelian
public import Nyll.ClassFieldTheory.LubinTate.Padic.MultiplicativeEvaluation.FiniteLevelPrimitiveRoot
public import Nyll.ValuedFieldTheory.LocalField.Padic.Cyclotomic.TotallyRamified.EisensteinPolynomial

/-!
# The p-adic model of a localized cyclotomic prime-power level
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
open LubinTate
open _root_.ValuationTheory.DiscreteValuationField.ValuedExtension

attribute [local instance]
  rationalFinitePlaceCompletionRatAlgebra
  rationalCyclotomicPrimeFact
  rationalCyclotomicLevelNeZero
  KummerTheory.rationalCyclotomicLevelFiniteDimensional
  KummerTheory.rationalCyclotomicLevelIsAbelianGalois
  rationalFinitePlaceBaseNontriviallyNormedField
  rationalFinitePlaceBaseLocallyCompactSpace
  rationalFinitePlaceBaseIsUltrametricDist
  rationalFinitePlaceBaseValued
  rationalFinitePlaceBaseValuativeRel
  rationalFinitePlaceBaseValuationIsNontrivial
  rationalFinitePlaceBaseValuationCompatible
  rationalFinitePlaceBaseValuativeRelIsNontrivial
  rationalFinitePlaceBaseIsValuativeTopology
  rationalFinitePlaceBaseIsNonarchimedeanLocalField
  rationalCyclotomicArtinExtensionAlgebra
  rationalCyclotomicArtinExtensionSMul
  rationalCyclotomicArtinCompletionAlgebra
  rationalCyclotomicArtinLocalizedAlgebra
  rationalCyclotomicArtinLocalizedGlobalAlgebra
  rationalCyclotomicArtinLocalizedGlobalSMul
  rationalCyclotomicArtinLocalizedScalarTower
  rationalCyclotomicArtinLocalizedFiniteDimensional
  rationalCyclotomicArtinLocalizedIsAbelianGalois
  rationalCyclotomicArtinLocalizedIsSeparable
  rationalCyclotomicArtinLocalizedIsCyclotomic
  rationalCyclotomicArtinExtensionFiniteDimensional
  rationalCyclotomicArtinExtensionContinuousSMul
  rationalCyclotomicArtinExtensionLocallyCompact
  rationalCyclotomicArtinLocalizedLocallyCompact
  rationalCyclotomicArtinLocalizedIsUltrametricDist
  rationalCyclotomicArtinLocalizedValued
  rationalCyclotomicArtinLocalizedValuativeRel
  rationalCyclotomicArtinLocalizedValuationCompatible
  rationalCyclotomicArtinLocalizedValuationHasExtension
  rationalCyclotomicArtinLocalizedValuationIsNontrivial
  rationalCyclotomicArtinLocalizedValuativeRelIsNontrivial
  rationalCyclotomicArtinLocalizedIsValuativeTopology
  rationalCyclotomicArtinLocalizedIsNonarchimedeanLocalField
  rationalCyclotomicArtinLocalizedIntegerAlgebra
  rationalCyclotomicArtinLocalizedIsIntegralClosure
  rationalCyclotomicArtinLocalizedIntegerModuleFinite

/-- The standard multiplicative Lubin--Tate field at level `n`. -/
abbrev RationalCyclotomicPrincipalPrimePadicLevel
    (p : Nat.Primes) (n : ℕ) :=
  standardLubinTateLevelField
    (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicPrincipalPrimeLevelIsCyclotomicExtension
    (p : Nat.Primes) (n : ℕ) :
    IsCyclotomicExtension {p.1 ^ (n + 1)} ℚ
      (KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus p n)) := by
  change
    IsCyclotomicExtension
      {(rationalCyclotomicPrincipalPrimeModulus p n : ℕ)} ℚ
      (KummerTheory.rationalCyclotomicLevel
        (rationalCyclotomicPrincipalPrimeModulus p n))
  exact
    KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
      (rationalCyclotomicPrincipalPrimeModulus p n)

attribute [local instance] rationalCyclotomicPrincipalPrimeLevelIsCyclotomicExtension

/-- The global level underlying the ramified prime-power comparison. -/
abbrev rationalCyclotomicPrincipalPrimeLevel
    (m : ℕ+) :=
  rationalCyclotomicArtinLevel m

/-- The `ℚ_[p]`-algebra structure on the localized cyclotomic completion,
transported through the canonical comparison with the `p`-adic completion. -/
@[reducible]
noncomputable def
    rationalCyclotomicPrincipalPrimeLocalizedPadicAlgebra
    (m : ℕ+) (p : Nat.Primes) :
    Algebra ℚ_[p.1]
      (rationalCyclotomicLocalizedCompletion m
        (RayClass.rationalPrime p)) :=
  ((algebraMap
      (HeightOneSpectrum.adicAbv ℚ
        (RayClass.rationalPrime p)).Completion
      (rationalCyclotomicLocalizedCompletion m
        (RayClass.rationalPrime p))).comp
    (rationalFinitePlaceCompletionRingEquivPadic p).symm.toRingHom).toAlgebra

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[reducible]
noncomputable def rationalCyclotomicArtinLocalizedPadicAlgebra
    (m : ℕ+) (p : Nat.Primes) :
    Algebra ℚ_[p.1] (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime p)) :=
  rationalCyclotomicPrincipalPrimeLocalizedPadicAlgebra m p

attribute [local instance] rationalCyclotomicArtinLocalizedPadicAlgebra

/-- The canonical rational-algebra equivalence from the prime completion to the p-adic field. -/
noncomputable def rationalFinitePlaceCompletionAlgEquivPadic
    (p : Nat.Primes) :
    (rationalCyclotomicArtinBaseAbv p).Completion ≃ₐ[ℚ] ℚ_[p.1] :=
  AlgEquiv.ofRingEquiv
    (f := rationalFinitePlaceCompletionRingEquivPadic p)
    (rationalFinitePlaceCompletionRingEquivPadic_algebraMap p)

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicArtinLocalizedPadicScalarTower
    (m : ℕ+) (p : Nat.Primes) :
    IsScalarTower ℚ ℚ_[p.1]
      (rationalCyclotomicLocalizedCompletion m (RayClass.rationalPrime p)) := by
  exact IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)

attribute [local instance] rationalCyclotomicArtinLocalizedPadicScalarTower

private theorem rationalCyclotomicArtin_padic_algebraMap
    (m : ℕ+) (p : Nat.Primes) :
    algebraMap (rationalCyclotomicArtinBaseAbv p).Completion
        (rationalCyclotomicArtinLocalizedField m p) =
      (algebraMap ℚ_[p.1]
        (rationalCyclotomicArtinLocalizedField m p)) ∘
        (rationalFinitePlaceCompletionAlgEquivPadic p) := by
  funext a
  change
    algebraMap (rationalCyclotomicArtinBaseAbv p).Completion
        (rationalCyclotomicArtinLocalizedField m p) a =
      algebraMap (rationalCyclotomicArtinBaseAbv p).Completion
        (rationalCyclotomicArtinLocalizedField m p)
        ((rationalFinitePlaceCompletionRingEquivPadic p).symm
          (rationalFinitePlaceCompletionRingEquivPadic p a))
  exact
    congrArg
      (algebraMap (rationalCyclotomicArtinBaseAbv p).Completion
        (rationalCyclotomicArtinLocalizedField m p))
      ((rationalFinitePlaceCompletionRingEquivPadic p).symm_apply_apply a).symm

private theorem rationalCyclotomicArtin_algebraAdjoin_restrictScalars
    (m : ℕ+) (p : Nat.Primes) :
    (Algebra.adjoin (rationalCyclotomicArtinBaseAbv p).Completion
      (Set.singleton (rationalCyclotomicLocalizedPrimitiveRoot m
        (rationalCyclotomicArtinPlace p)) :
        Set (rationalCyclotomicArtinLocalizedField m p))).restrictScalars ℚ =
      (Algebra.adjoin ℚ_[p.1]
        (Set.singleton (rationalCyclotomicLocalizedPrimitiveRoot m
          (rationalCyclotomicArtinPlace p)) :
          Set (rationalCyclotomicArtinLocalizedField m p))).restrictScalars ℚ := by
  exact
    Algebra.restrictScalars_adjoin_of_algEquiv
      (E := rationalCyclotomicArtinLocalizedField m p)
      (rationalFinitePlaceCompletionAlgEquivPadic p)
      (rationalCyclotomicArtin_padic_algebraMap m p)
      (Set.singleton (rationalCyclotomicLocalizedPrimitiveRoot m
        (rationalCyclotomicArtinPlace p)) :
        Set (rationalCyclotomicArtinLocalizedField m p))

private theorem
    rationalCyclotomicArtin_baseAlgebraAdjoin_restrict_eq_top
    (m : ℕ+) (p : Nat.Primes) :
    (Algebra.adjoin (rationalCyclotomicArtinBaseAbv p).Completion
      (Set.singleton (rationalCyclotomicLocalizedPrimitiveRoot m
        (rationalCyclotomicArtinPlace p)) :
        Set (rationalCyclotomicArtinLocalizedField m p))).restrictScalars ℚ =
      (⊤ : Subalgebra (rationalCyclotomicArtinBaseAbv p).Completion
      (rationalCyclotomicArtinLocalizedField m p)).restrictScalars ℚ := by
  have hRoot : IsPrimitiveRoot
      (show rationalCyclotomicArtinLocalizedField m p from
        rationalCyclotomicLocalizedPrimitiveRoot m
          (rationalCyclotomicArtinPlace p))
      (m : ℕ) :=
    rationalCyclotomicLocalizedPrimitiveRoot_isPrimitiveRoot
      m (rationalCyclotomicArtinPlace p)
  have hTop :
      Algebra.adjoin (rationalCyclotomicArtinBaseAbv p).Completion
        (Set.singleton (rationalCyclotomicLocalizedPrimitiveRoot m
          (rationalCyclotomicArtinPlace p)) :
          Set (rationalCyclotomicArtinLocalizedField m p)) = ⊤ :=
    IsCyclotomicExtension.adjoin_primitive_root_eq_top
      (A := (rationalCyclotomicArtinBaseAbv p).Completion)
      (B := rationalCyclotomicArtinLocalizedField m p) hRoot
  exact congrArg
    (fun A : Subalgebra (rationalCyclotomicArtinBaseAbv p).Completion
      (rationalCyclotomicArtinLocalizedField m p) => A.restrictScalars ℚ)
    hTop

private theorem rationalCyclotomicArtin_restrictScalars_top_base_eq_padic
    (m : ℕ+) (p : Nat.Primes) :
    (⊤ : Subalgebra (rationalCyclotomicArtinBaseAbv p).Completion
        (rationalCyclotomicArtinLocalizedField m p)).restrictScalars ℚ =
      (⊤ : Subalgebra ℚ_[p.1]
        (rationalCyclotomicArtinLocalizedField m p)).restrictScalars ℚ :=
  (Subalgebra.restrictScalars_top ℚ).trans
    (Subalgebra.restrictScalars_top ℚ).symm

private theorem
    rationalCyclotomicArtin_padicAlgebraAdjoin_restrict_eq_top
    (m : ℕ+) (p : Nat.Primes) :
    (Algebra.adjoin ℚ_[p.1]
      (Set.singleton (rationalCyclotomicLocalizedPrimitiveRoot m
        (rationalCyclotomicArtinPlace p)) :
        Set (rationalCyclotomicArtinLocalizedField m p))).restrictScalars ℚ =
      (⊤ : Subalgebra ℚ_[p.1]
        (rationalCyclotomicArtinLocalizedField m p)).restrictScalars ℚ := by
  exact
    (rationalCyclotomicArtin_algebraAdjoin_restrictScalars m p).symm.trans
      ((rationalCyclotomicArtin_baseAlgebraAdjoin_restrict_eq_top m p).trans
        (rationalCyclotomicArtin_restrictScalars_top_base_eq_padic m p))

/-- The finite-dimensional instance for the standard multiplicative level,
named once so all consumers use the same proof term. -/
theorem rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional
    (p : Nat.Primes) (n : ℕ) :
    FiniteDimensional ℚ_[p.1]
      (standardLubinTateLevelField
        (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n) :=
  standardLubinTateLevelField_finiteDimensional
    (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n

attribute [local instance]
  rationalCyclotomicPrincipalPrimePadicLevelFiniteDimensional

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
theorem rationalCyclotomicPrincipalPrimePadicLevelIsAbelianGalois
    (p : Nat.Primes) (n : ℕ) :
    IsAbelianGalois ℚ_[p.1]
      (RationalCyclotomicPrincipalPrimePadicLevel p n) :=
  standardLubinTateLevelField_isAbelianGalois
    (padicLocalField p.1)
    (padicMultiplicativeLubinTateSeries_isUniformizer p.1) n

attribute [local instance] rationalCyclotomicPrincipalPrimePadicLevelIsAbelianGalois

/-- Canonical structure for the rational cyclotomic completion tower.
Its instance registration is local to the finite-place calculation. -/
@[reducible]
noncomputable def rationalPrimeFactorCompletionPadicAlgebra
    (p : Nat.Primes) :
    Algebra (RationalCyclotomicPrincipalPrimeCompletion p) ℚ_[p.1] :=
  (rationalFinitePlaceCompletionRingEquivPadic p).toRingHom.toAlgebra

attribute [local instance] rationalPrimeFactorCompletionPadicAlgebra

/-- The genuine multiplicative Lubin--Tate level is generated by its
primitive `p ^ (n + 1)`-st root of unity. -/
theorem padicMultiplicativePrimitiveRoot_adjoin_eq_top
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let T := standardLubinTateLevelField hπ n
    Algebra.adjoin ℚ_[p]
        ({padicMultiplicativePrimitiveRoot p n} : Set T) =
      ⊤ := by
  intro hπ T
  let ζ : T := padicMultiplicativePrimitiveRoot p n
  let m := p ^ (n + 1)
  let : NeZero m :=
    ⟨pow_ne_zero _ (Fact.out : Nat.Prime p).ne_zero⟩
  let : FiniteDimensional ℚ_[p] T :=
    standardLubinTateLevelField_finiteDimensional hπ n
  have hζ : IsPrimitiveRoot ζ m := by
    simpa only [ζ, m] using
      padicMultiplicativePrimitiveRoot_isPrimitiveRoot p n
  let A : IntermediateField ℚ_[p] T :=
    IntermediateField.adjoin ℚ_[p] {ζ}
  let : IsCyclotomicExtension {m} ℚ_[p] A :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ_[p]
  have hAfin :
      Module.finrank ℚ_[p] A = Nat.totient m := by
    exact
      IsCyclotomicExtension.finrank A
        (by
          simpa only [m] using
            padicCyclotomicPolynomial_irreducible_prime_pow_succ
              p n)
  have hTfin :
      Module.finrank ℚ_[p] T = Nat.totient m := by
    rw [standardLubinTateLevelField_finrank hπ n]
    have hcard :
        Nat.card (padicLocalField p).residueField = p := by
      exact padicCompleteDVF_residueField_card p
    rw [hcard, Nat.totient_prime_pow
      (Fact.out : Nat.Prime p) (Nat.succ_pos n)]
    exact Nat.mul_comm (p - 1) (p ^ n)
  have hAeq : A = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    simpa using hAfin.trans hTfin.symm
  calc
    Algebra.adjoin ℚ_[p] {ζ} = A.toSubalgebra := by
      exact
        (IntermediateField.adjoin_toSubalgebra
          ({ζ} : Set T)).symm
    _ = (⊤ : IntermediateField ℚ_[p] T).toSubalgebra :=
      congrArg IntermediateField.toSubalgebra hAeq
    _ = ⊤ := rfl

/-- The standard multiplicative Lubin--Tate level is the actual
`p ^ (n + 1)`-cyclotomic extension of `ℚ_p`. -/
theorem padicMultiplicativeLevel_isCyclotomicExtension
    (p : ℕ) [Fact p.Prime] (n : ℕ) :
    let hπ := padicMultiplicativeLubinTateSeries_isUniformizer p
    let T := standardLubinTateLevelField hπ n
    IsCyclotomicExtension {p ^ (n + 1)} ℚ_[p] T := by
  intro hπ T
  exact
    padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top
      (padicMultiplicativePrimitiveRoot p n)
      (padicMultiplicativePrimitiveRoot_isPrimitiveRoot p n)
      (padicMultiplicativePrimitiveRoot_adjoin_eq_top p n)

private theorem
    rationalCyclotomicPrincipalPrimeLocalizedPrimitiveRoot_isPrimitiveRoot
    (p : Nat.Primes) (n : ℕ) :
    IsPrimitiveRoot
      (rationalCyclotomicLocalizedPrimitiveRoot
        (rationalCyclotomicPrincipalPrimeModulus p n)
        (RayClass.rationalPrime p))
      (p.1 ^ (n + 1)) := by
  change
    IsPrimitiveRoot
      (rationalCyclotomicLocalizedPrimitiveRoot
        (rationalCyclotomicPrincipalPrimeModulus p n)
        (RayClass.rationalPrime p))
      (rationalCyclotomicPrincipalPrimeModulus p n : ℕ)
  exact
    rationalCyclotomicLocalizedPrimitiveRoot_isPrimitiveRoot
      (rationalCyclotomicPrincipalPrimeModulus p n)
      (RayClass.rationalPrime p)

private theorem
    rationalCyclotomicPrincipalPrimeLocalizedPrimitiveRoot_adjoin_eq_top
    (p : Nat.Primes) (n : ℕ) :
    Algebra.adjoin ℚ_[p.1]
        (Set.singleton (rationalCyclotomicLocalizedPrimitiveRoot
          (rationalCyclotomicPrincipalPrimeModulus p n)
          (rationalCyclotomicArtinPlace p)) :
          Set (rationalCyclotomicArtinLocalizedField
            (rationalCyclotomicPrincipalPrimeModulus p n) p)) =
      ⊤ := by
  exact
    (Subalgebra.restrictScalars_injective ℚ)
      (rationalCyclotomicArtin_padicAlgebraAdjoin_restrict_eq_top
        (rationalCyclotomicPrincipalPrimeModulus p n) p)

/-- The localized prime-power cyclotomic level is cyclotomic over the
standard p-adic field through the canonical completion comparison. -/
theorem
    rationalCyclotomicPrincipalPrimeLocalizedLevel_isCyclotomicExtension
    (p : Nat.Primes) (n : ℕ) :
    IsCyclotomicExtension {p.1 ^ (n + 1)} ℚ_[p.1]
      (RationalCyclotomicPrincipalPrimeLocalizedLevel p n) := by
  exact
    padic_isCyclotomicExtension_of_primitiveRoot_adjoin_eq_top
      (rationalCyclotomicLocalizedPrimitiveRoot
        (rationalCyclotomicPrincipalPrimeModulus p n)
        (RayClass.rationalPrime p))
      (rationalCyclotomicPrincipalPrimeLocalizedPrimitiveRoot_isPrimitiveRoot
        p n)
      (rationalCyclotomicPrincipalPrimeLocalizedPrimitiveRoot_adjoin_eq_top
        p n)

/-- The chosen localized global cyclotomic level, transported over the
completion equivalence, is the standard multiplicative Lubin--Tate level. -/
noncomputable def rationalCyclotomicLocalizedCompletionPadicAlgEquiv
    (p : Nat.Primes) (n : ℕ) :
    RationalCyclotomicPrincipalPrimeLocalizedLevel p n ≃ₐ[ℚ_[p.1]]
      RationalCyclotomicPrincipalPrimePadicLevel p n := by
  let : IsCyclotomicExtension {p.1 ^ (n + 1)} ℚ_[p.1]
      (RationalCyclotomicPrincipalPrimeLocalizedLevel p n) :=
    rationalCyclotomicPrincipalPrimeLocalizedLevel_isCyclotomicExtension p n
  let : IsCyclotomicExtension {p.1 ^ (n + 1)} ℚ_[p.1]
      (RationalCyclotomicPrincipalPrimePadicLevel p n) :=
    padicMultiplicativeLevel_isCyclotomicExtension p.1 n
  exact
    IsCyclotomicExtension.algEquiv
      {p.1 ^ (n + 1)} ℚ_[p.1]
      (RationalCyclotomicPrincipalPrimeLocalizedLevel p n)
      (RationalCyclotomicPrincipalPrimePadicLevel p n)

/-! ## The ramified principal finite-place factor -/

/-- The cyclotomic character is determined by the prime-power primitive-root action. -/
theorem rationalCyclotomicPrincipalPrime_galEquivZMod_eq_of_action
    (p : Nat.Primes) (n : ℕ)
    (sigma : Gal(rationalCyclotomicPrincipalPrimeLevel
      (rationalCyclotomicPrincipalPrimeModulus p n)/ℚ))
    (a : (ZMod (p.1 ^ (n + 1)))ˣ)
    (haction :
      sigma (rationalCyclotomicLevelPrimitiveRoot
          (rationalCyclotomicPrincipalPrimeModulus p n)) =
        rationalCyclotomicLevelPrimitiveRoot
            (rationalCyclotomicPrincipalPrimeModulus p n) ^ a.val.val) :
    IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ (n + 1))
        (rationalCyclotomicPrincipalPrimeLevel
          (rationalCyclotomicPrincipalPrimeModulus p n))
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension
            (rationalCyclotomicPrincipalPrimeModulus p n)) sigma =
      a := by
  let m := rationalCyclotomicPrincipalPrimeModulus p n
  let L := rationalCyclotomicPrincipalPrimeLevel m
  let zeta : L := rationalCyclotomicLevelPrimitiveRoot m
  have hzeta : IsPrimitiveRoot zeta (p.1 ^ (n + 1)) := by
    change
      IsPrimitiveRoot
        (rationalCyclotomicLevelPrimitiveRoot m) (m : ℕ)
    exact rationalCyclotomicLevelPrimitiveRoot_isPrimitiveRoot m
  change
    IsCyclotomicExtension.Rat.galEquivZMod
        (p.1 ^ (n + 1)) L
        (hK :=
          KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension m)
        sigma = a
  let c :=
    IsCyclotomicExtension.Rat.galEquivZMod
      (p.1 ^ (n + 1)) L
      (hK :=
        KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension m)
      sigma
  have hc :
      sigma zeta = zeta ^ c.val.val :=
    IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq
      (hK :=
        KummerTheory.rationalCyclotomicLevel_isCyclotomicExtension m)
      (p.1 ^ (n + 1)) L sigma hzeta.pow_eq_one
  have hpowers :
      zeta ^ c.val.val = zeta ^ a.val.val :=
    hc.symm.trans haction
  rw [(hzeta.isOfFinOrder m.ne_zero).pow_inj_mod,
    ← hzeta.eq_orderOf,
    ← ZMod.natCast_eq_natCast_iff'] at hpowers
  change
      (c.val.val : ZMod (p.1 ^ (n + 1))) =
        (a.val.val : ZMod (p.1 ^ (n + 1))) at hpowers
  have hValues : c.val = a.val := by
    calc
      c.val = (c.val.val : ZMod (p.1 ^ (n + 1))) :=
        (ZMod.natCast_zmod_val c.val).symm
      _ = (a.val.val : ZMod (p.1 ^ (n + 1))) := hpowers
      _ = a.val := ZMod.natCast_zmod_val a.val
  change c = a
  apply Units.ext
  exact hValues

end Reciprocity
end GlobalClassFieldTheory
