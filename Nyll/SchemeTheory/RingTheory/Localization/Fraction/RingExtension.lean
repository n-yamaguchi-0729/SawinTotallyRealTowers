/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Localization.FractionRing

/-!
# A chosen field extension over the literal fraction ring

An application may use an arbitrary chosen fraction field `K` of a domain
`V`, while a generic construction is formulated over the literal quotient
type `FractionRing V`.  This file fixes the canonical composite algebra on an
extension `L / K` and transports finiteness and separability across the
canonical fraction-field equivalence.
-/

noncomputable section

namespace EtaleFundamentalGroups

universe uV uK uL

variable {V : Type uV} {K : Type uK} {L : Type uL}
variable [CommRing V] [IsDomain V]
variable [Field K] [Algebra V K] [IsFractionRing V K]
variable [Field L] [Algebra K L]

/-- The canonical algebra on `L` over the literal fraction ring of `V`,
factored through the chosen fraction field `K`. -/
noncomputable abbrev fractionRingToExtensionAlgebra :
    Algebra (FractionRing V) L := by
  letI : Algebra (FractionRing V) K := FractionRing.liftAlgebra V K
  exact ((algebraMap K L).comp
    (algebraMap (FractionRing V) K)).toAlgebra

/-- The canonical map from the literal fraction ring to a chosen fraction
field is an algebra equivalence over the literal fraction ring itself. -/
noncomputable def fractionRingChosenFractionFieldAlgEquiv :
    letI : Algebra (FractionRing V) K := FractionRing.liftAlgebra V K
    FractionRing V ≃ₐ[FractionRing V] K := by
  letI : Algebra (FractionRing V) K := FractionRing.liftAlgebra V K
  refine AlgEquiv.ofRingEquiv
    (f := (FractionRing.algEquiv V K).toRingEquiv) fun x ↦ ?_
  change (FractionRing.algEquiv V K) x = algebraMap (FractionRing V) K x
  have h : (FractionRing.algEquiv V K).toRingEquiv.toRingHom =
      algebraMap (FractionRing V) K := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors V)
    ext v
    change (FractionRing.algEquiv V K) (algebraMap V (FractionRing V) v) =
      algebraMap (FractionRing V) K (algebraMap V (FractionRing V) v)
    rw [(FractionRing.algEquiv V K).commutes]
    exact IsScalarTower.algebraMap_apply V (FractionRing V) K v
  exact DFunLike.congr_fun h x

omit [IsDomain V] in
/-- The literal fraction ring, chosen fraction field, and extension use a
definitionally compatible scalar tower. -/
theorem fractionRingToChosenFractionFieldToExtension_isScalarTower :
    letI : Algebra (FractionRing V) K := FractionRing.liftAlgebra V K
    letI : Algebra (FractionRing V) L :=
      fractionRingToExtensionAlgebra (V := V) (K := K) (L := L)
    IsScalarTower (FractionRing V) K L := by
  let : Algebra (FractionRing V) K := FractionRing.liftAlgebra V K
  let : Algebra (FractionRing V) L :=
    fractionRingToExtensionAlgebra (V := V) (K := K) (L := L)
  exact IsScalarTower.of_algebraMap_eq' rfl

variable [Algebra V L] [IsScalarTower V K L]

omit [IsDomain V] in
/-- The original base map and the composite map from the literal fraction
ring are compatible. -/
theorem fractionRingToExtension_isScalarTower :
    letI : Algebra (FractionRing V) L :=
      fractionRingToExtensionAlgebra (V := V) (K := K) (L := L)
    IsScalarTower V (FractionRing V) L := by
  let : Algebra (FractionRing V) K := FractionRing.liftAlgebra V K
  let : IsScalarTower V (FractionRing V) K :=
    FractionRing.isScalarTower_liftAlgebra V K
  let : Algebra (FractionRing V) L :=
    fractionRingToExtensionAlgebra (V := V) (K := K) (L := L)
  let : IsScalarTower (FractionRing V) K L :=
    fractionRingToChosenFractionFieldToExtension_isScalarTower
      (V := V) (K := K) (L := L)
  refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
  change algebraMap V L x =
    algebraMap K L
      (algebraMap (FractionRing V) K
        (algebraMap V (FractionRing V) x))
  rw [← IsScalarTower.algebraMap_apply V (FractionRing V) K,
    ← IsScalarTower.algebraMap_apply V K L]

variable [FiniteDimensional K L]

omit [Algebra V L] [IsScalarTower V K L] in
/-- Finite dimensionality over a chosen fraction field transports to the
literal fraction ring. -/
theorem fractionRingToExtension_finiteDimensional :
    letI : Algebra (FractionRing V) L :=
      fractionRingToExtensionAlgebra (V := V) (K := K) (L := L)
    FiniteDimensional (FractionRing V) L := by
  let : Algebra (FractionRing V) K := FractionRing.liftAlgebra V K
  let : Algebra (FractionRing V) L :=
    fractionRingToExtensionAlgebra (V := V) (K := K) (L := L)
  let : IsScalarTower (FractionRing V) K L :=
    fractionRingToChosenFractionFieldToExtension_isScalarTower
      (V := V) (K := K) (L := L)
  let e : FractionRing V ≃ₐ[FractionRing V] K :=
    fractionRingChosenFractionFieldAlgEquiv (V := V) (K := K)
  let : Module.Finite (FractionRing V) K :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  exact Module.Finite.trans K L

variable [Algebra.IsSeparable K L]

omit [Algebra V L] [IsScalarTower V K L] [FiniteDimensional K L] in
/-- Separability over a chosen fraction field transports to the literal
fraction ring. -/
theorem fractionRingToExtension_isSeparable :
    letI : Algebra (FractionRing V) L :=
      fractionRingToExtensionAlgebra (V := V) (K := K) (L := L)
    Algebra.IsSeparable (FractionRing V) L := by
  let : Algebra (FractionRing V) K := FractionRing.liftAlgebra V K
  let : Algebra (FractionRing V) L :=
    fractionRingToExtensionAlgebra (V := V) (K := K) (L := L)
  let : IsScalarTower (FractionRing V) K L :=
    fractionRingToChosenFractionFieldToExtension_isScalarTower
      (V := V) (K := K) (L := L)
  let e : FractionRing V ≃ₐ[FractionRing V] K :=
    fractionRingChosenFractionFieldAlgEquiv (V := V) (K := K)
  let : Algebra.IsSeparable (FractionRing V) K :=
    AlgEquiv.Algebra.isSeparable e
  exact Algebra.IsSeparable.trans (FractionRing V) K L

end EtaleFundamentalGroups
