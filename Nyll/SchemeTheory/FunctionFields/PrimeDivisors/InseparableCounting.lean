/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.PrimeDivisors.Centered
import Nyll.SchemeTheory.FunctionFields.Valuations.PurelyInseparable

/-!
# Reducing prime-divisor counts to the separable subextension

The normalization-finiteness theorem used in the separable proofs of
Fried--Jarden 6.2.2(b),(d) need only be applied to the maximal separable
subextension.  A valuation subring of the full field is determined by its
restriction to that subextension, because the remaining extension is purely
inseparable.

This file first proves the corresponding general counting theorem for
`FiniteDivisorOver`.  Unlike the earlier fraction-field theorem, the ambient
field may now be a purely inseparable extension of the fraction field of the
Dedekind model.
-/

noncomputable section

namespace FieldArithmetic
namespace Chapter06
namespace InseparablePrimeDivisorReduction

open IsLocalRing

universe uK uR uS uM uF

namespace ValuationCenter

variable {S : Type uS} {M : Type uM}
  [CommRing S] [Field M] [Algebra S M]

/-- A valuation subring contains the image of the chosen model. -/
def FiniteOn (A : ValuationSubring M) : Prop :=
  ∀ s : S, algebraMap S M s ∈ A

/-- The model map factored through a valuation subring. -/
def finiteRingHom (A : ValuationSubring M)
    (hfinite : FiniteOn (S := S) A) :
    S →+* A where
  toFun s := ⟨algebraMap S M s, hfinite s⟩
  map_zero' := Subtype.ext (map_zero (algebraMap S M))
  map_one' := Subtype.ext (map_one (algebraMap S M))
  map_add' x y := Subtype.ext (map_add (algebraMap S M) x y)
  map_mul' x y := Subtype.ext (map_mul (algebraMap S M) x y)

/-- The center of a valuation subring on a model it contains. -/
def center (A : ValuationSubring M)
    (hfinite : FiniteOn (S := S) A) : Ideal S :=
  (maximalIdeal A).comap (finiteRingHom (S := S) A hfinite)

@[simp]
theorem mem_center_iff_mem_nonunits
    (A : ValuationSubring M) (hfinite : FiniteOn (S := S) A) (s : S) :
    s ∈ center (S := S) A hfinite ↔
      algebraMap S M s ∈ A.nonunits := by
  change
    finiteRingHom (S := S) A hfinite s ∈ maximalIdeal A ↔
      algebraMap S M s ∈ A.nonunits
  exact A.coe_mem_nonunits_iff.symm

/-- The center on any contained model is prime. -/
theorem center_isPrime
    (A : ValuationSubring M) (hfinite : FiniteOn (S := S) A) :
    (center (S := S) A hfinite).IsPrime := by
  let : (maximalIdeal A).IsPrime :=
    (maximalIdeal.isMaximal A).isPrime
  exact Ideal.IsPrime.comap _

/--
The center of a proper valuation subring on a model with fraction field `M`
is nonzero.
-/
theorem center_ne_bot
    [IsDomain S] [IsFractionRing S M]
    (A : ValuationSubring M) (hfinite : FiniteOn (S := S) A)
    (hproper : A ≠ ⊤) :
    center (S := S) A hfinite ≠ ⊥ := by
  intro hcenter
  apply hproper
  apply top_unique
  intro x _
  obtain ⟨⟨a, s⟩, hxs⟩ :=
    IsLocalization.surj (nonZeroDivisors S) x
  have hs0 : (s : S) ≠ 0 :=
    mem_nonZeroDivisors_iff_ne_zero.mp s.property
  have hs_not_center : (s : S) ∉ center (S := S) A hfinite := by
    rw [hcenter, Ideal.mem_bot]
    exact hs0
  have hs_not_nonunit :
      algebraMap S M (s : S) ∉ A.nonunits := by
    intro hs
    exact hs_not_center
      ((mem_center_iff_mem_nonunits A hfinite (s : S)).2 hs)
  have hs_inv : (algebraMap S M (s : S))⁻¹ ∈ A := by
    by_contra hs
    exact hs_not_nonunit
      (A.mem_nonunits_iff_or.mpr (Or.inr hs))
  have ha : algebraMap S M a ∈ A :=
    hfinite a
  have hquot :
      algebraMap S M a * (algebraMap S M (s : S))⁻¹ ∈ A :=
    A.mul_mem _ _ ha hs_inv
  rw [← hxs] at hquot
  simpa [mul_assoc, hs0] using hquot

/-- The height-one center on a Dedekind model. -/
def centerHeightOneSpectrum
    [IsDedekindDomain S] [IsFractionRing S M]
    (A : ValuationSubring M) (hfinite : FiniteOn (S := S) A)
    (hproper : A ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum S :=
  ⟨center (S := S) A hfinite, center_isPrime A hfinite,
    center_ne_bot A hfinite hproper⟩

/--
The canonical localization at the center is contained in the valuation
subring.
-/
theorem valuationSubringAtCenter_le
    [IsDedekindDomain S] [IsFractionRing S M]
    (A : ValuationSubring M) (hfinite : FiniteOn (S := S) A)
    (hproper : A ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M
        (centerHeightOneSpectrum A hfinite hproper) ≤ A := by
  rintro x ⟨a, s, hs, rfl⟩
  have hs_not_nonunit :
      algebraMap S M s ∉ A.nonunits := by
    intro hs_nonunit
    exact hs
      ((mem_center_iff_mem_nonunits A hfinite s).2 hs_nonunit)
  have hs_inv : (algebraMap S M s)⁻¹ ∈ A := by
    by_contra hs_not_mem
    exact hs_not_nonunit
      (A.mem_nonunits_iff_or.mpr (Or.inr hs_not_mem))
  simpa [div_eq_mul_inv] using
    (A.mul_mem _ _ (hfinite a) hs_inv)

/--
A proper valuation subring containing a Dedekind model is the canonical
localization at its center.
-/
theorem valuationSubringAtCenter_eq
    [IsDedekindDomain S] [IsFractionRing S M]
    (A : ValuationSubring M) (hfinite : FiniteOn (S := S) A)
    (hproper : A ≠ ⊤) :
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M
        (centerHeightOneSpectrum A hfinite hproper) = A :=
  ValuationSubring.eq_of_le_of_ne_top _
    (valuationSubringAtCenter_le A hfinite hproper) hproper

/--
Proper valuation subrings containing a Dedekind model are determined by
their centers, without assuming a DVR structure on the restrictions.
-/
theorem eq_of_center_eq
    [IsDedekindDomain S] [IsFractionRing S M]
    (A B : ValuationSubring M)
    (hfiniteA : FiniteOn (S := S) A)
    (hfiniteB : FiniteOn (S := S) B)
    (hproperA : A ≠ ⊤) (hproperB : B ≠ ⊤)
    (hcenter :
      center (S := S) A hfiniteA =
        center (S := S) B hfiniteB) :
    A = B := by
  have hheight :
      centerHeightOneSpectrum A hfiniteA hproperA =
        centerHeightOneSpectrum B hfiniteB hproperB := by
    apply IsDedekindDomain.HeightOneSpectrum.ext
    exact hcenter
  calc
    A =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M
          (centerHeightOneSpectrum A hfiniteA hproperA) :=
      (valuationSubringAtCenter_eq A hfiniteA hproperA).symm
    _ =
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime M
          (centerHeightOneSpectrum B hfiniteB hproperB) := by
      rw [hheight]
    _ = B :=
      valuationSubringAtCenter_eq B hfiniteB hproperB

end ValuationCenter

/-- Nonunits are preserved and reflected by restriction to a subfield. -/
theorem mem_comap_nonunits_iff
    {M : Type uM} {F : Type uF} [Field M] [Field F]
    (A : ValuationSubring F) (ι : M →+* F) (x : M) :
    x ∈ (A.comap ι).nonunits ↔ ι x ∈ A.nonunits := by
  rw [(A.comap ι).mem_nonunits_iff_or, A.mem_nonunits_iff_or]
  simp [ValuationSubring.mem_comap]

section PurelyInseparableFractionField

variable {K : Type uK} {R : Type uR} {S : Type uS}
  {M : Type uM} {F : Type uF}
  [Field K] [CommRing R] [CommRing S] [Field M] [Field F]
  [Algebra R S] [Algebra K S] [Algebra K F] [Algebra S F]
  [IsScalarTower K S F]
  [Algebra S M] [Algebra M F] [IsScalarTower S M F]
  [IsDedekindDomain S] [IsFractionRing S M]
  [IsPurelyInseparable M F]

open PrimeDivisorCounting

/-- Restrict the valuation subring underlying a divisor to `M`. -/
def restrictedValuationSubring
    {p : Ideal R}
    (v : FiniteDivisorOver (K := K) (S := S) (F := F) p) :
    ValuationSubring M :=
  v.divisor.valuationSubring.comap (algebraMap M F)

omit [IsDedekindDomain S] [IsFractionRing S M] [IsPurelyInseparable M F] in
/-- The restricted valuation subring still contains the Dedekind model. -/
theorem restrictedValuationSubring_finite
    {p : Ideal R}
    (v : FiniteDivisorOver (K := K) (S := S) (F := F) p) :
    ValuationCenter.FiniteOn (S := S)
      (restrictedValuationSubring (M := M) v) := by
  intro s
  change
    algebraMap M F (algebraMap S M s) ∈
      v.divisor.valuationSubring
  rw [← IsScalarTower.algebraMap_apply S M F]
  exact v.finite s

omit [Algebra S M] [IsScalarTower S M F] [IsDedekindDomain S] [IsFractionRing S M] in
/--
The restriction is proper.  Otherwise pure-inseparable injectivity would
force the original prime-divisor valuation subring to be the whole field.
-/
theorem restrictedValuationSubring_ne_top
    {p : Ideal R}
    (v : FiniteDivisorOver (K := K) (S := S) (F := F) p) :
    restrictedValuationSubring (M := M) v ≠ ⊤ := by
  intro htop
  apply v.divisor.valuationSubring_ne_top
  apply PurelyInseparableValuation.restriction_injective
    (F := M) (E := F)
  change
    v.divisor.valuationSubring.comap (algebraMap M F) =
      (⊤ : ValuationSubring F).comap (algebraMap M F)
  calc
    v.divisor.valuationSubring.comap (algebraMap M F) =
        (⊤ : ValuationSubring M) := htop
    _ = (⊤ : ValuationSubring F).comap (algebraMap M F) := by
      apply ValuationSubring.ext
      intro x
      simp

omit [IsDedekindDomain S] [IsFractionRing S M] [IsPurelyInseparable M F] in
/-- The center is unchanged after restricting the valuation to `M`. -/
theorem restrictedValuationSubring_center_eq
    {p : Ideal R}
    (v : FiniteDivisorOver (K := K) (S := S) (F := F) p) :
    ValuationCenter.center
        (restrictedValuationSubring (M := M) v)
        (restrictedValuationSubring_finite (M := M) v) =
      v.divisor.centerAlong (IsScalarTower.toAlgHom K S F) v.finite := by
  ext s
  rw [ValuationCenter.mem_center_iff_mem_nonunits,
    v.divisor.mem_centerAlong_iff_mem_nonunits]
  change
    algebraMap S M s ∈
        (v.divisor.valuationSubring.comap
          (algebraMap M F)).nonunits ↔
      algebraMap S F s ∈ v.divisor.valuationSubring.nonunits
  rw [mem_comap_nonunits_iff]
  rw [IsScalarTower.algebraMap_apply S M F]

/--
The existing center map remains injective when the ambient field is a purely
inseparable extension of the fraction field of the Dedekind model.
-/
theorem centerMap_injective_of_isPurelyInseparable
    (M : Type uM) [Field M] [Algebra S M] [Algebra M F]
    [IsScalarTower S M F] [IsFractionRing S M]
    [IsPurelyInseparable M F] {p : Ideal R} :
    Function.Injective
      (FiniteDivisorOver.centerMap :
        FiniteDivisorOver (K := K) (S := S) (F := F) p →
          p.primesOver S) := by
  intro v w hcenter
  apply FiniteDivisorOver.ext
  apply FunctionFieldPrimeDivisor.ext_valuationSubring
  have hrestricted :
      restrictedValuationSubring (M := M) v =
        restrictedValuationSubring (M := M) w := by
    apply ValuationCenter.eq_of_center_eq
      (restrictedValuationSubring (M := M) v)
      (restrictedValuationSubring (M := M) w)
      (restrictedValuationSubring_finite (M := M) v)
      (restrictedValuationSubring_finite (M := M) w)
      (restrictedValuationSubring_ne_top (M := M) v)
      (restrictedValuationSubring_ne_top (M := M) w)
    rw [restrictedValuationSubring_center_eq (M := M) v,
      restrictedValuationSubring_center_eq (M := M) w]
    exact congrArg Subtype.val hcenter
  apply PurelyInseparableValuation.restriction_injective
    (F := M) (E := F)
  exact hrestricted

/--
Prime-divisor counting over a finite Dedekind model is unchanged after a
purely inseparable extension of its fraction field.
-/
theorem card_finiteDivisorOver_le_finrank_of_isPurelyInseparable
    [IsDomain R] [Module.Finite R S] [Module.Flat R S]
    (M : Type uM) [Field M] [Algebra S M] [Algebra M F]
    [IsScalarTower S M F] [IsFractionRing S M]
    [IsPurelyInseparable M F]
    (p : Ideal R) [p.IsPrime] :
    Nat.card (FiniteDivisorOver (K := K) (S := S) (F := F) p) ≤
      Module.finrank R S := by
  let : Fintype (p.primesOver S) :=
    (Algebra.QuasiFinite.finite_primesOver
      (R := R) (S := S) p).fintype
  calc
    Nat.card (FiniteDivisorOver (K := K) (S := S) (F := F) p) ≤
        Nat.card (p.primesOver S) :=
      Nat.card_le_card_of_injective
        FiniteDivisorOver.centerMap
        (centerMap_injective_of_isPurelyInseparable (M := M))
    _ ≤ Module.finrank R S :=
      PrimeCounting.card_primesOver_le_finrank p

end PurelyInseparableFractionField

end InseparablePrimeDivisorReduction
end Chapter06
end FieldArithmetic
