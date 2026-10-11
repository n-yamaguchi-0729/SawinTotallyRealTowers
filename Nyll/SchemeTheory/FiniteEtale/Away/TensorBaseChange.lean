/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.RingHom.Etale
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Base change of a literal etale away map

The complement hypothesis on a finite normalization is stated using the
literal map between two away localizations.  This file transports that map
through a pushout.  The proof pastes the original pushout with the four
canonical localization squares, so it never assumes that the unlocalized
map is etale.
-/

noncomputable section

open scoped TensorProduct

namespace EtaleFundamentalGroups

universe uA uB uC uD

/-- A literal etale away map remains etale in any pushout square.  All
localization algebras are constructed internally, and the conclusion is the
literal `Localization.awayMap` for the lower horizontal map. -/
theorem localization_awayMap_etale_of_isPushout
    {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
    [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    [Algebra A B] [Algebra A C]
    [Algebra A D] [Algebra B D] [Algebra C D]
    [IsScalarTower A B D] [IsScalarTower A C D]
    [Algebra.IsPushout A B C D]
    (f : A)
    (hAway :
      (Localization.awayMap (algebraMap A B) f).Etale) :
    (Localization.awayMap
      (algebraMap C D) (algebraMap A C f)).Etale := by
  let fB : B := algebraMap A B f
  let fC : C := algebraMap A C f
  let fD : D := algebraMap C D fC
  let S := Localization.Away f
  let T := Localization.Away fB
  let U := Localization.Away fC
  let V := Localization.Away fD
  let : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq' rfl
  let mapST : S →+* T :=
    Localization.awayMap (algebraMap A B) f
  let : Algebra S T := mapST.toAlgebra
  let : IsScalarTower A S T :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap A T a = mapST (algebraMap A S a)
      rw [show mapST (algebraMap A S a) =
          algebraMap B T (algebraMap A B a) by
        simp [mapST, S, T, fB, IsLocalization.Away.map]]
      exact IsScalarTower.algebraMap_apply A B T a
  let : IsScalarTower A C U := IsScalarTower.of_algebraMap_eq' rfl
  have hlocU : IsLocalization
      (Algebra.algebraMapSubmonoid C (Submonoid.powers f)) U := by
    change IsLocalization
      ((Submonoid.powers f).map (algebraMap A C)) U
    rw [Submonoid.map_powers]
    exact Localization.isLocalization
  let : IsLocalization
      (Algebra.algebraMapSubmonoid C (Submonoid.powers f)) U := hlocU
  let mapSU : S →+* U :=
    Localization.awayMap (algebraMap A C) f
  let : Algebra S U := mapSU.toAlgebra
  let : IsScalarTower A S U :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      change algebraMap A U a = mapSU (algebraMap A S a)
      rw [show mapSU (algebraMap A S a) =
          algebraMap C U (algebraMap A C a) by
        simp [mapSU, S, U, fC, IsLocalization.Away.map]]
      exact IsScalarTower.algebraMap_apply A C U a
  let : IsScalarTower B D V := IsScalarTower.of_algebraMap_eq' rfl
  have hfBD : algebraMap B D fB = fD := by
    calc
      algebraMap B D fB = algebraMap A D f :=
        (IsScalarTower.algebraMap_apply A B D f).symm
      _ = algebraMap C D fC :=
        IsScalarTower.algebraMap_apply A C D f
      _ = fD := rfl
  have hlocVFromB : IsLocalization
      (Algebra.algebraMapSubmonoid D (Submonoid.powers fB)) V := by
    change IsLocalization
      ((Submonoid.powers fB).map (algebraMap B D)) V
    rw [Submonoid.map_powers, hfBD]
    exact Localization.isLocalization
  let : IsLocalization
      (Algebra.algebraMapSubmonoid D (Submonoid.powers fB)) V :=
    hlocVFromB
  let : Algebra T V :=
    localizationAlgebra (Submonoid.powers fB) D
  let : IsScalarTower B T V :=
    isScalarTower_localizationAlgebra
      (Submonoid.powers fB) D
  let : IsScalarTower C D V := IsScalarTower.of_algebraMap_eq' rfl
  have hlocVFromC : IsLocalization
      (Algebra.algebraMapSubmonoid D (Submonoid.powers fC)) V := by
    change IsLocalization
      ((Submonoid.powers fC).map (algebraMap C D)) V
    rw [Submonoid.map_powers]
    change IsLocalization (Submonoid.powers fD) V
    exact Localization.isLocalization
  let : IsLocalization
      (Algebra.algebraMapSubmonoid D (Submonoid.powers fC)) V :=
    hlocVFromC
  let mapUV : U →+* V :=
    Localization.awayMap (algebraMap C D) fC
  let : Algebra U V := mapUV.toAlgebra
  let : IsScalarTower C U V :=
    IsScalarTower.of_algebraMap_eq fun c ↦ by
      change algebraMap C V c = mapUV (algebraMap C U c)
      rw [show mapUV (algebraMap C U c) =
          algebraMap D V (algebraMap C D c) by
        simp [mapUV, U, V, fC, fD, IsLocalization.Away.map]]
      exact IsScalarTower.algebraMap_apply C D V c
  let : IsScalarTower A D V := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A T V :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      calc
        algebraMap A V a = algebraMap D V (algebraMap A D a) :=
          IsScalarTower.algebraMap_apply A D V a
        _ = algebraMap D V (algebraMap B D (algebraMap A B a)) := by
          rw [IsScalarTower.algebraMap_apply A B D]
        _ = algebraMap B V (algebraMap A B a) := by
          rw [← IsScalarTower.algebraMap_apply B D V]
        _ = algebraMap T V (algebraMap B T (algebraMap A B a)) :=
          IsScalarTower.algebraMap_apply B T V (algebraMap A B a)
        _ = algebraMap T V (algebraMap A T a) := by
          rw [← IsScalarTower.algebraMap_apply A B T]
  let : IsScalarTower A U V :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      calc
        algebraMap A V a = algebraMap D V (algebraMap A D a) :=
          IsScalarTower.algebraMap_apply A D V a
        _ = algebraMap D V (algebraMap C D (algebraMap A C a)) := by
          rw [IsScalarTower.algebraMap_apply A C D]
        _ = algebraMap C V (algebraMap A C a) := by
          rw [← IsScalarTower.algebraMap_apply C D V]
        _ = algebraMap U V (algebraMap C U (algebraMap A C a)) :=
          IsScalarTower.algebraMap_apply C U V (algebraMap A C a)
        _ = algebraMap U V (algebraMap A U a) := by
          rw [← IsScalarTower.algebraMap_apply A C U]
  let : Algebra S V :=
    ((algebraMap T V).comp (algebraMap S T)).toAlgebra
  let : IsScalarTower S T V := IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower A S V := IsScalarTower.to₁₂₄ A S T V
  let : IsScalarTower S U V := by
    apply IsScalarTower.of_algebraMap_eq'
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    rw [← IsScalarTower.algebraMap_eq A S V, RingHom.comp_assoc,
      ← IsScalarTower.algebraMap_eq A S U,
      ← IsScalarTower.algebraMap_eq A U V]
  have hBLocalization : Algebra.IsPushout B T D V :=
    (Algebra.isPushout_of_isLocalization
      (Submonoid.powers fB) T D V).symm
  have hBig : Algebra.IsPushout A T C V :=
    (Algebra.IsPushout.comp_iff A B C D).2 hBLocalization
  have hCLocalization : Algebra.IsPushout A S C U :=
    (Algebra.isPushout_of_isLocalization
      (Submonoid.powers f) S C U).symm
  let : Algebra.IsPushout A S C U := hCLocalization
  have hAwayPushout : Algebra.IsPushout S T U V :=
    (Algebra.IsPushout.comp_iff A S C U).1 hBig
  let : Algebra.IsPushout S T U V := hAwayPushout
  let e : U ⊗[S] T ≃ₐ[U] V :=
    Algebra.IsPushout.equiv (h := hAwayPushout.symm) S U T V
  have hBaseChange : Algebra.Etale U (U ⊗[S] T) :=
    @Algebra.Etale.baseChange S T U _ _ _ _ _ hAway.toAlgebra
  have hUV : Algebra.Etale U V :=
    @Algebra.Etale.of_equiv U (U ⊗[S] T) V
      _ _ _ _ _ hBaseChange e
  change mapUV.Etale
  exact hUV

universe uR uX uY

/-- Tensor-product specialization of
`localization_awayMap_etale_of_isPushout`. -/
theorem localization_awayMap_tensorProduct_etale
    {R : Type uR} {X : Type uX} {Y : Type uY}
    [CommRing R] [CommRing X] [CommRing Y]
    [Algebra R X] [Algebra R Y]
    (f : R)
    (hAway :
      (Localization.awayMap (algebraMap R X) f).Etale) :
    (Localization.awayMap
      (algebraMap Y (Y ⊗[R] X)) (algebraMap R Y f)).Etale := by
  let : Algebra X (Y ⊗[R] X) := Algebra.TensorProduct.rightAlgebra
  let : IsScalarTower R X (Y ⊗[R] X) :=
    Algebra.TensorProduct.right_isScalarTower
  let : IsScalarTower R Y (Y ⊗[R] X) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.IsPushout R X Y (Y ⊗[R] X) :=
    TensorProduct.isPushout'
  exact localization_awayMap_etale_of_isPushout f hAway

end EtaleFundamentalGroups

end
