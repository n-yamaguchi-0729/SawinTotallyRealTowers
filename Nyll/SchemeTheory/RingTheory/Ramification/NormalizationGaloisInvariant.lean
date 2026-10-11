/-
Copyright (c) 2024 Thomas Browning. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning, Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Nyll.SchemeTheory.CategoryTheory.CommAlgRingMap
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Invariant.Defs

/-!
# Native Galois invariance of the actual integral closure

The prescribed normalization action is invariant over the original normal
base. Field fixedness gives a fraction-field preimage. The integral-closure
subtype supplies its integrality, and normality descends it to the base.
The final proof uses the literal inclusion and the existing coefficient
square, without opening an algebra from the integral closure to the field.

The descent specializes the proof of `Algebra.isInvariant_of_isGalois`:
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/Invariant/Galois.lean
Its field-fixedness, integrality, and normality facts are reused below.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory

universe u v w

/-- The already constructed native inclusion, retained with its literal carrier. -/
private def normalizationInclusionRingHom
    (A : Type u) (F : Type w) [CommRing A] [CommRing F] [Algebra A F] :
    integralClosure A F →+* F :=
  subalgebraRingMap (integralClosure A F)

/-- The already constructed native coefficient map on the same carrier. -/
private def normalizationCoefficientRingHom
    (A : Type u) (F : Type w) [CommRing A] [CommRing F] [Algebra A F] :
    A →+* integralClosure A F :=
  subalgebraBaseMap (integralClosure A F)

private theorem normalizationInclusionRingHom_injective
    (A : Type u) (F : Type w) [CommRing A] [CommRing F] [Algebra A F] :
    Function.Injective (normalizationInclusionRingHom A F).toFun :=
  subalgebraRingMap_injective (integralClosure A F)

/-- The existing subtype coefficient square, before Galois data occur. -/
private theorem normalizationInclusionRingHom_comp_coefficient
    (A : Type u) (F : Type w) [CommRing A] [CommRing F] [Algebra A F] :
    (normalizationInclusionRingHom A F).comp (normalizationCoefficientRingHom A F) =
      algebraMap A F :=
  subalgebraRingMap_comp_base (integralClosure A F)

/-- A field fixed by its full Galois group is the original base field. -/
private theorem galois_fixed_exists_field_coefficient
    (K : Type v) (F : Type w) [Field K] [Field F] [Algebra K F]
    [IsGalois K F] (x : F)
    (hx : ∀ σ : Gal(F/K), σ.toRingHom.toFun x = x) :
    ∃ k : K, (algebraMap K F).toFun k = x := by
  exact (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := K) (K := F) x).mpr hx

/-- An integral image of a fraction-field element comes from the normal base. -/
private theorem integral_field_preimage_exists_coefficient
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsIntegrallyClosed A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K] [Algebra K F] [Algebra A F]
    [IsScalarTower A K F] (k : K)
    (hk : IsIntegral A ((algebraMap K F).toFun k)) :
    ∃ a : A, (algebraMap A F).toFun a = (algebraMap K F).toFun k := by
  have hkIntegral : IsIntegral A k :=
    (isIntegral_algebraMap_iff (R := A) (A := K) (B := F)).mp hk
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hkIntegral
  refine ⟨a, ?_⟩
  exact (IsScalarTower.algebraMap_apply A K F a).trans
    (congrArg (algebraMap K F).toFun ha)

section RawNormalizationAction

attribute [local instance] normalizationInertiaImageAction

/-- Fixed normalization elements descend using their literal subtype integrality. -/
private theorem normalization_fixed_exists_coefficient
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsIntegrallyClosed A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K] [Algebra K F] [Algebra A F]
    [IsScalarTower A K F] [IsGalois K F]
    (b : integralClosure A F) (hb : ∀ σ : Gal(F/K), σ • b = b) :
    ∃ a : A, (normalizationCoefficientRingHom A F).toFun a = b := by
  have hfixed : ∀ σ : Gal(F/K),
      σ.toRingHom.toFun ((normalizationInclusionRingHom A F).toFun b) =
        (normalizationInclusionRingHom A F).toFun b := by
    intro σ
    have hcoeff := congrArg (fun f : integralClosure A F →+* F => f.toFun b)
      (normalizationInertiaImageAction_comp_inclusion A K F σ)
    change σ.toRingHom.toFun ((normalizationInclusionRingHom A F).toFun b) =
      (normalizationInclusionRingHom A F).toFun (σ • b) at hcoeff
    exact hcoeff.trans (congrArg (normalizationInclusionRingHom A F).toFun (hb σ))
  obtain ⟨k, hk⟩ := galois_fixed_exists_field_coefficient K F
    ((normalizationInclusionRingHom A F).toFun b) hfixed
  have hbIntegral : IsIntegral A ((normalizationInclusionRingHom A F).toFun b) := b.property
  have hkIntegral : IsIntegral A ((algebraMap K F).toFun k) :=
    (congrArg (IsIntegral A) hk).mpr hbIntegral
  obtain ⟨a, ha⟩ := integral_field_preimage_exists_coefficient A K F k hkIntegral
  refine ⟨a, ?_⟩
  apply normalizationInclusionRingHom_injective A F
  have hbase := congrArg (fun f : A →+* F => f.toFun a)
    (normalizationInclusionRingHom_comp_coefficient A F)
  exact hbase.trans (ha.trans hk)

/-- Construct the native invariant property only after coefficient descent is proved. -/
private theorem coefficientDescent_isInvariant
    (A : Type u) (B G : Type w) [CommRing A] [CommRing B] [Algebra A B]
    [Group G] [MulSemiringAction G B]
    (h : ∀ b : B, (∀ g : G, g • b = b) →
      ∃ a : A, (algebraMap A B).toFun a = b) : Algebra.IsInvariant A B G := by
  constructor
  intro b hb
  exact h b hb

/-- The original possibly infinite Galois action on the literal integral closure is
invariant over the original normal base. The proof uses the native subtype
inclusion and does not instantiate the general integral-closure-to-field
algebra interface of `Algebra.isInvariant_of_isGalois`. -/
theorem integralClosure_isInvariant_of_isGalois
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsIntegrallyClosed A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K] [Algebra K F] [Algebra A F]
    [IsScalarTower A K F] [IsGalois K F] :
    Algebra.IsInvariant A (integralClosure A F) Gal(F/K) :=
  coefficientDescent_isInvariant A (integralClosure A F) Gal(F/K)
    (normalization_fixed_exists_coefficient A K F)

end RawNormalizationAction

private theorem normalizationCommAlgInclusion_injective
    (A : Type u) (F : Type w) [CommRing A] [CommRing F] [Algebra A F] :
    Function.Injective (normalizationCommAlgInclusion A F).toFun :=
  subalgebraRingMap_injective (integralClosure A F)

private theorem normalizationCommAlgInclusion_comp_coefficient
    (A : Type u) (F : Type w) [CommRing A] [CommRing F] [Algebra A F] :
    (normalizationCommAlgInclusion A F).comp
        (commAlgCoefficientMap (normalizationCommAlgCat A F)) = algebraMap A F :=
  subalgebraRingMap_comp_base (integralClosure A F)

attribute [local instance] normalizationCommAlgGaloisAction

/-- Fixed native normalization elements descend by the existing literal
integrality and normality proof, along the stored coefficient map. -/
theorem normalizationCommAlg_fixed_exists_coefficient
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [IsIntegrallyClosed A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K] [Algebra K F] [Algebra A F]
    [IsScalarTower A K F] [IsGalois K F]
    (b : normalizationCommAlgCat A F) (hb : ∀ σ : Gal(F/K), σ • b = b) :
    ∃ a : A, (commAlgCoefficientMap (normalizationCommAlgCat A F)).toFun a = b :=
  normalization_fixed_exists_coefficient A K F b hb

/-- The actual native normalization stabilizers are open in the Krull topology. -/
theorem normalizationCommAlg_fixedSet_isOpen_krull
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K] [Algebra K F] [Algebra A F]
    [IsScalarTower A K F] [Algebra.IsAlgebraic K F]
    (b : normalizationCommAlgCat A F) : IsOpen (fun σ : Gal(F/K) => σ • b = b) :=
  integralClosure_fixedSet_isOpen_krull A K F b

/-- The prescribed normalization action fixes the actual coefficient map.
The proof cancels the literal inclusion and uses the native field square. -/
theorem normalizationCommAlg_action_comp_coefficient
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K] [Algebra K F] [Algebra A F]
    [IsScalarTower A K F] [IsGalois K F] (σ : Gal(F/K)) :
    (MulSemiringAction.toRingHom Gal(F/K) (normalizationCommAlgCat A F) σ).comp
        (commAlgCoefficientMap (normalizationCommAlgCat A F)) =
      commAlgCoefficientMap (normalizationCommAlgCat A F) := by
  apply (RingHom.cancel_left (g := normalizationCommAlgInclusion A F)
    (normalizationCommAlgInclusion_injective A F)).mp
  calc
    (normalizationCommAlgInclusion A F).comp
        ((MulSemiringAction.toRingHom Gal(F/K) (normalizationCommAlgCat A F) σ).comp
          (commAlgCoefficientMap (normalizationCommAlgCat A F))) =
      ((normalizationCommAlgInclusion A F).comp
        (MulSemiringAction.toRingHom Gal(F/K) (normalizationCommAlgCat A F) σ)).comp
          (commAlgCoefficientMap (normalizationCommAlgCat A F)) :=
      (RingHom.comp_assoc (commAlgCoefficientMap (normalizationCommAlgCat A F))
        (MulSemiringAction.toRingHom Gal(F/K) (normalizationCommAlgCat A F) σ)
        (normalizationCommAlgInclusion A F)).symm
    _ = (σ.toRingHom.comp (normalizationCommAlgInclusion A F)).comp
        (commAlgCoefficientMap (normalizationCommAlgCat A F)) :=
      congrArg (fun f : normalizationCommAlgCat A F →+* F =>
        f.comp (commAlgCoefficientMap (normalizationCommAlgCat A F)))
        (normalizationCommAlg_action_comp_inclusion A K F σ).symm
    _ = σ.toRingHom.comp ((normalizationCommAlgInclusion A F).comp
        (commAlgCoefficientMap (normalizationCommAlgCat A F))) :=
      RingHom.comp_assoc (commAlgCoefficientMap (normalizationCommAlgCat A F))
        (normalizationCommAlgInclusion A F) σ.toRingHom
    _ = σ.toRingHom.comp (algebraMap A F) :=
      congrArg (fun f : A →+* F => σ.toRingHom.comp f)
        (normalizationCommAlgInclusion_comp_coefficient A F)
    _ = algebraMap A F := (σ.restrictScalars A).toAlgHom.comp_algebraMap
    _ = (normalizationCommAlgInclusion A F).comp
        (commAlgCoefficientMap (normalizationCommAlgCat A F)) :=
      (normalizationCommAlgInclusion_comp_coefficient A F).symm

end EtaleFundamentalGroups.Inertia
