/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.RingTheory.Ramification.ProfiniteInertiaMap
import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Ring.Action.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IntegralRestrict
import Mathlib.RingTheory.Invariant.Galois
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Compactness.Compact


/-!
# Finite-level images of inertia in an arbitrary Galois normalization

The canonical action on the actual integral closure is continuous for the
Krull topology and the discrete ring topology. The subgroup fixing an actual
intermediate field has that field's integral closure as its invariant base.
These two facts supply the profinite inertia-image theorem at every finite
Galois intermediate field. No equality of inertia images is an input.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

universe u v w

/- The forward map in Mathlib's `galRestrict'` is precisely the following
composition of existing native maps. Keeping its A-linear input in this
sparse scope avoids reopening the entire AKLB scalar interface downstream.
Source: https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/RingTheory/IntegralClosure/IntegralRestrict.lean
-/
private def integralClosureRestrictionRingHom
    (A : Type u) (L : Type v) [CommRing A] [CommRing L] [Algebra A L]
    (f : L →ₐ[A] L) : integralClosure A L →+* integralClosure A L :=
  ((IsIntegralClosure.equiv A (integralClosure A L) L (integralClosure A L)).toAlgHom.comp
    f.mapIntegralClosure).toRingHom

private theorem integralClosureRestrictionRingHom_comp
    (A : Type u) (L : Type v) [CommRing A] [CommRing L] [Algebra A L]
    (f : L →ₐ[A] L) :
    (integralClosure A L).toSubring.subtype.comp (integralClosureRestrictionRingHom A L f) =
      f.toRingHom.comp (integralClosure A L).toSubring.subtype := by
  apply RingHom.ext
  intro b
  change algebraMap (integralClosure A L) L
      (IsIntegralClosure.equiv A (integralClosure A L) L (integralClosure A L)
        (f.mapIntegralClosure b)) = f (b : L)
  exact (IsIntegralClosure.algebraMap_equiv A (integralClosure A L) L
    (integralClosure A L) (f.mapIntegralClosure b)).trans (AlgHom.coe_mapIntegralClosure f b)


section NativeNormalizationCarrier

open SchemeTheory

/-- The literal normalization inclusion on its existing native algebra object. -/
def normalizationCommAlgInclusion
    (A : Type u) (F : Type w) [CommRing A] [CommRing F] [Algebra A F] :
    normalizationCommAlgCat A F →+* F :=
  subalgebraRingMap (integralClosure A F)

/-- The existing normalization restriction on the identical native carrier. -/
private def normalizationCommAlgRestrictionRingHom
    (A : Type u) (F : Type w) [CommRing A] [CommRing F] [Algebra A F]
    (f : F →ₐ[A] F) : normalizationCommAlgCat A F →+* normalizationCommAlgCat A F :=
  integralClosureRestrictionRingHom A F f

/-- The actual restriction square is converted before fraction-field data occur. -/
private theorem normalizationCommAlgRestrictionRingHom_comp
    (A : Type u) (F : Type w) [CommRing A] [CommRing F] [Algebra A F]
    (f : F →ₐ[A] F) :
    (normalizationCommAlgInclusion A F).comp (normalizationCommAlgRestrictionRingHom A F f) =
      f.toRingHom.comp (normalizationCommAlgInclusion A F) :=
  integralClosureRestrictionRingHom_comp A F f

end NativeNormalizationCarrier

/-- The native field stabilizer is open, with the field action closed in
this field-only scope. -/
private theorem galois_fixedSet_isOpen
    (K : Type v) (L : Type w) [Field K] [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (x : L) :
    IsOpen (fun σ : Gal(L/K) => σ.toRingHom.toFun x = x) := by
  change IsOpen (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K))
  exact stabilizer_isOpen_of_isIntegral x

private theorem continuousSMul_of_open_fixedSets
    {G X : Type w} [Group G] [MulAction G X]
    [TopologicalSpace G] [IsTopologicalGroup G]
    [TopologicalSpace X] [DiscreteTopology X]
    (hopen : ∀ x : X, IsOpen (fun g : G => g • x = x)) : ContinuousSMul G X :=
  continuousSMul_iff_stabilizer_isOpen.mpr hopen

section RawNormalizationAction

variable (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra K L] [Algebra A L] [IsScalarTower A K L]

local instance normalizationInertiaImageAction [Algebra.IsAlgebraic K L] :
    MulSemiringAction Gal(L/K) (integralClosure A L) :=
  IsIntegralClosure.MulSemiringAction A K L (integralClosure A L)

local instance normalizationInertiaImageTower (E : IntermediateField K L) :
    IsScalarTower A E L :=
  Subalgebra.isScalarTower_mid (S := E.toSubalgebra) (α := A) (β := L)

/-- The actual normalization Galois action commutes with the literal
integral-closure inclusion, as a bundled ring-map equality. -/
theorem normalizationInertiaImageAction_comp_inclusion [IsGalois K L]
    (σ : Gal(L/K)) :
    σ.toRingHom.comp (integralClosure A L).toSubring.subtype =
      (integralClosure A L).toSubring.subtype.comp
        (MulSemiringAction.toRingHom Gal(L/K) (integralClosure A L) σ) := by
  exact (integralClosureRestrictionRingHom_comp A L (σ.restrictScalars A).toAlgHom).symm

/-- Fixedness under the prescribed normalization action is detected by
its literal inclusion. The actual RingHom coefficient square proves both
directions without opening the normalization-to-field algebra. -/
private theorem normalizationInertiaImageAction_fixed_iff [Algebra.IsAlgebraic K L]
    (σ : Gal(L/K)) (b : integralClosure A L) :
    σ • b = b ↔ σ.toRingHom.toFun (b : L) = (b : L) := by
  have hcoeff := congrArg
    (fun f : integralClosure A L →+* L => f.toFun b)
    (integralClosureRestrictionRingHom_comp A L (σ.restrictScalars A).toAlgHom)
  change ((σ • b : integralClosure A L) : L) = σ.toRingHom.toFun (b : L) at hcoeff
  constructor
  · intro h
    exact hcoeff.symm.trans (congrArg (fun c : integralClosure A L => (c : L)) h)
  · intro h
    apply Subtype.ext
    exact hcoeff.trans h

/-- The actual normalization stabilizer is open before a topology on the
normalization carrier is introduced. -/
theorem integralClosure_fixedSet_isOpen_krull [Algebra.IsAlgebraic K L]
    (b : integralClosure A L) : IsOpen (fun σ : Gal(L/K) => σ • b = b) := by
  have heq : (fun σ : Gal(L/K) => σ • b = b) =
      (fun σ : Gal(L/K) => σ.toRingHom.toFun (b : L) = (b : L)) :=
    funext (fun σ => propext (normalizationInertiaImageAction_fixed_iff A K L σ b))
  rw [heq]
  exact galois_fixedSet_isOpen K L (b : L)

/-- The existing prescribed normalization action is continuous for the
Krull topology and any discrete topology on the literal integral closure. -/
theorem integralClosure_continuousSMul_krull [Algebra.IsAlgebraic K L]
    [TopologicalSpace (integralClosure A L)] [DiscreteTopology (integralClosure A L)] :
    ContinuousSMul Gal(L/K) (integralClosure A L) :=
  continuousSMul_of_open_fixedSets (integralClosure_fixedSet_isOpen_krull A K L)

private theorem integralClosure_isInvariant_fixingSubgroup [IsGalois K L]
    (E : IntermediateField K L) :
    let : Algebra (integralClosure A E) (integralClosure A L) :=
      (IsScalarTower.toAlgHom A E L).mapIntegralClosure.toRingHom.toAlgebra
    Algebra.IsInvariant (integralClosure A E) (integralClosure A L) E.fixingSubgroup := by
  intro inclusionAction
  constructor
  intro b hb
  have hbE : (b : L) ∈ E := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup E]
    apply (IntermediateField.mem_fixedField_iff (E.fixingSubgroup) (b : L)).mpr
    intro σ hσ
    have h := hb ⟨σ, hσ⟩
    change galRestrict A K L (integralClosure A L) σ b = b at h
    exact (algebraMap_galRestrict_apply A σ b).symm.trans (congrArg Subtype.val h)
  let e : E := ⟨(b : L), hbE⟩
  have he : IsIntegral A e :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom A E L)
      (algebraMap E L).injective).mp b.property
  refine ⟨⟨e, he⟩, ?_⟩
  apply Subtype.ext
  rfl

/-- Restricting inertia in an arbitrary Galois normalization to an actual
finite Galois intermediate field gives the entire inertia group of the
literal contracted prime. The prime is arbitrary, and the ambient extension
is not assumed finite. -/
theorem integralClosure_inertia_map_eq_finiteGalois_contraction [IsGalois K L]
    (E : FiniteGaloisIntermediateField K L)
    (Q : Ideal (integralClosure A L)) [Q.IsPrime] :
    (Q.inertia Gal(L/K)).map (AlgEquiv.restrictNormalHom E) =
      (Q.comap (IsScalarTower.toAlgHom A E L).mapIntegralClosure).inertia Gal(E/K) := by
  let : Algebra (integralClosure A E) (integralClosure A L) :=
    (IsScalarTower.toAlgHom A E L).mapIntegralClosure.toRingHom.toAlgebra
  let : TopologicalSpace (integralClosure A L) := ⊥
  have : DiscreteTopology (integralClosure A L) := ⟨rfl⟩
  have : ContinuousSMul Gal(L/K) (integralClosure A L) :=
    integralClosure_continuousSMul_krull A K L
  have : CompactSpace E.toIntermediateField.fixingSubgroup :=
    isCompact_iff_compactSpace.mp
      (IntermediateField.fixingSubgroup_isClosed E.toIntermediateField).isCompact
  have : Algebra.IsInvariant (integralClosure A E) (integralClosure A L)
      E.toIntermediateField.fixingSubgroup :=
    integralClosure_isInvariant_fixingSubgroup A K L E.toIntermediateField
  have hker : E.toIntermediateField.fixingSubgroup ≤
      (AlgEquiv.restrictNormalHom E : Gal(L/K) →* Gal(E/K)).ker :=
    (IntermediateField.restrictNormalHom_ker E.toIntermediateField).ge
  have hcompat : ∀ (σ : Gal(L/K)) (b : integralClosure A E),
      algebraMap (integralClosure A E) (integralClosure A L)
          (AlgEquiv.restrictNormalHom E σ • b) =
        σ • algebraMap (integralClosure A E) (integralClosure A L) b := by
    intro σ b
    apply Subtype.ext
    change algebraMap E L
        (algebraMap (integralClosure A E) E
          (galRestrict A K E (integralClosure A E) (AlgEquiv.restrictNormalHom E σ) b)) =
      algebraMap (integralClosure A L) L
        (galRestrict A K L (integralClosure A L) σ
          ((IsScalarTower.toAlgHom A E L).mapIntegralClosure b))
    rw [algebraMap_galRestrict_apply A, algebraMap_galRestrict_apply A]
    exact AlgEquiv.restrictNormal_commutes σ E (algebraMap (integralClosure A E) E b)
  exact SchemeTheory.map_inertia_of_surjective_of_profinite
    (AlgEquiv.restrictNormalHom E) E.toIntermediateField.fixingSubgroup
    (Q.under (integralClosure A E)) Q
    (AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := E) L) hker hcompat

end RawNormalizationAction

section NativeNormalizationAction

open SchemeTheory

/-- The already prescribed normalization action, on its identical native carrier.
This is the existing action value, without a new action construction. -/
abbrev normalizationCommAlgGaloisAction
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K] [Algebra K F] [Algebra A F]
    [IsScalarTower A K F] [Algebra.IsAlgebraic K F] :
    MulSemiringAction Gal(F/K) (normalizationCommAlgCat A F).carrier :=
  normalizationInertiaImageAction A K F

attribute [local instance] normalizationCommAlgGaloisAction

/-- The actual action-inclusion square, through the native restriction owner. -/
theorem normalizationCommAlg_action_comp_inclusion
    (A : Type u) (K : Type v) (F : Type w)
    [CommRing A] [Field K] [Field F]
    [Algebra A K] [IsFractionRing A K] [Algebra K F] [Algebra A F]
    [IsScalarTower A K F] [Algebra.IsAlgebraic K F] (σ : Gal(F/K)) :
    σ.toRingHom.comp (normalizationCommAlgInclusion A F) =
      (normalizationCommAlgInclusion A F).comp
        (MulSemiringAction.toRingHom Gal(F/K) (normalizationCommAlgCat A F) σ) :=
  (normalizationCommAlgRestrictionRingHom_comp A F (σ.restrictScalars A).toAlgHom).symm

end NativeNormalizationAction

end EtaleFundamentalGroups.Inertia
