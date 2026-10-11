/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Ideal.CotangentBaseChange
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Regularity under etale morphisms

This file proves that regularity of local rings ascends along the local ring
maps induced by etale morphisms.  Consequently, regularity along the support
of an ideal sheaf is preserved after etale pullback.
-/

open CategoryTheory
open TensorProduct
open scoped TensorProduct

namespace RingHom

universe u

/-- A flat, formally unramified, essentially finite type local homomorphism
with regular source has regular target. -/
lemma isRegularLocalRing_of_flat_of_formallyUnramified_of_essFiniteType
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [IsLocalRing S] [IsLocalHom f]
    [IsRegularLocalRing R] (hflat : f.Flat)
    (hunramified : f.FormallyUnramified) (hfiniteType : f.EssFiniteType) :
    IsRegularLocalRing S := by
  algebraize [f]
  let : Module.Flat R S := hflat
  let : Algebra.FormallyUnramified R S := hunramified
  let : Algebra.EssFiniteType R S := hfiniteType
  let : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hdim : ringKrullDim R = ringKrullDim S := by
    have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
      (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal S)
    rw [Algebra.FormallyUnramified.map_maximalIdeal] at h
    calc
      ringKrullDim R = (IsLocalRing.maximalIdeal R).height :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
      _ = (IsLocalRing.maximalIdeal S).height := by
        have hh : (IsLocalRing.maximalIdeal R).height =
            (IsLocalRing.maximalIdeal S).height := by
          simpa only [Ideal.map_quotient_self, Ideal.height_bot, add_zero] using h.symm
        exact congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hh
      _ = ringKrullDim S := IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  calc
    ((IsLocalRing.maximalIdeal S).spanFinrank : WithBot ℕ∞) =
        ((IsLocalRing.maximalIdeal R).map (algebraMap R S)).spanFinrank := by
      rw [Algebra.FormallyUnramified.map_maximalIdeal]
    _ ≤ (IsLocalRing.maximalIdeal R).spanFinrank :=
      by
        norm_cast
        exact Ideal.spanFinrank_map_le_of_fg _
          (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
    _ = ringKrullDim R := IsRegularLocalRing.spanFinrank_maximalIdeal
    _ = ringKrullDim S := hdim

/-- A flat, formally unramified, essentially finite type local homomorphism
with regular target and Noetherian source has regular source. -/
lemma isRegularLocalRing_of_flat_of_formallyUnramified_of_essFiniteType_of_target
    {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) [IsLocalRing R] [IsRegularLocalRing S] [IsLocalHom f]
    [IsNoetherianRing R] (hflat : f.Flat)
    (hunramified : f.FormallyUnramified) (hfiniteType : f.EssFiniteType) :
    IsRegularLocalRing R := by
  algebraize [f]
  let : Module.Flat R S := hflat
  let : Module.FaithfullyFlat R S :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  let : Algebra.FormallyUnramified R S := hunramified
  let : Algebra.EssFiniteType R S := hfiniteType
  let mR := IsLocalRing.maximalIdeal R
  let mS := IsLocalRing.maximalIdeal S
  let : mS.IsMaximal := by
    dsimp [mS]
    infer_instance
  have hm : mR.map (algebraMap R S) = mS :=
    Algebra.FormallyUnramified.map_maximalIdeal
  let gR : mR.Cotangent →ₗ[R] mS.Cotangent :=
    Ideal.mapCotangent mR mS (Algebra.ofId R S) (by
      rw [← hm]
      exact Ideal.le_comap_map)
  let G : S ⊗[R] mR.Cotangent →ₗ[S] mS.Cotangent :=
    gR.liftBaseChange S
  have hG_inj : Function.Injective G := by
    let qR : mR.Cotangent →ₗ[R] R ⧸ mR ^ 2 :=
      mR.cotangentToQuotientSquare
    let qS : mS.Cotangent →ₗ[S] S ⧸ mS ^ 2 :=
      mS.cotangentToQuotientSquare
    let e₁ : S ⊗[R] (R ⧸ mR ^ 2) ≃ₐ[S]
        (S ⧸ (mR ^ 2).map (algebraMap R S)) :=
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (mR ^ 2)).symm
    let e₂ : (S ⧸ (mR ^ 2).map (algebraMap R S)) ≃ₐ[S] (S ⧸ mS ^ 2) :=
      Ideal.quotientEquivAlgOfEq S (by rw [Ideal.map_pow, hm])
    let e := e₁.trans e₂
    let H : S ⊗[R] mR.Cotangent →ₗ[S] S ⧸ mS ^ 2 :=
      e.toLinearMap ∘ₗ AlgebraTensorModule.lTensor S S qR
    have hcomp : qS ∘ₗ G = H := by
      ext x
      obtain ⟨x, rfl⟩ := mR.toCotangent_surjective x
      simp [qR, qS, G, gR, H, e, e₁, e₂, Algebra.smul_def]
      simpa [IsScalarTower.algebraMap_apply] using
        (e₂.commutes (algebraMap R S x)).symm
    suffices h : Function.Injective (qS ∘ₗ G) from .of_comp h
    rw [hcomp, LinearMap.coe_comp]
    exact e.injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap (M := S) qR
        mR.cotangentToQuotientSquare_injective)
  have hG_surj : Function.Surjective G := by
    intro z
    obtain ⟨⟨z, hz⟩, rfl⟩ := mS.toCotangent_surjective z
    have hzmap : z ∈ mR.map (algebraMap R S) := by simpa [hm] using hz
    change z ∈ Submodule.span S ((algebraMap R S) '' (mR : Set R)) at hzmap
    let P : S → Prop := fun x ↦ ∀ hx : x ∈ mS,
      ∃ w, G w = mS.toCotangent ⟨x, hx⟩
    have hP : P z := by
      refine Submodule.span_induction (p := fun x _ ↦ P x) ?_ ?_ ?_ ?_ hzmap
      · intro x hx hxS
        obtain ⟨x, hx, rfl⟩ := hx
        refine ⟨1 ⊗ₜ[R] mR.toCotangent ⟨x, hx⟩, ?_⟩
        simp [G, gR]
      · intro hzero
        refine ⟨0, ?_⟩
        have hz0 : (⟨0, hzero⟩ : mS) = 0 := Subtype.ext rfl
        rw [hz0, map_zero, map_zero]
      · intro x y hx hy ihx ihy hxy
        have hxS : x ∈ mS := by
          rw [← hm]
          exact hx
        have hyS : y ∈ mS := by
          rw [← hm]
          exact hy
        obtain ⟨wx, hwx⟩ := ihx hxS
        obtain ⟨wy, hwy⟩ := ihy hyS
        refine ⟨wx + wy, ?_⟩
        rw [map_add, hwx, hwy, ← map_add]
        congr 1
      · intro a x hx ihx hax
        have hxS : x ∈ mS := by
          rw [← hm]
          exact hx
        obtain ⟨w, hw⟩ := ihx hxS
        refine ⟨a • w, ?_⟩
        rw [map_smul, hw, ← map_smul]
        congr 1
    exact hP hz
  let e : S ⊗[R] mR.Cotangent ≃ₗ[S] mS.Cotangent :=
    LinearEquiv.ofBijective G ⟨hG_inj, hG_surj⟩
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have hdim : ringKrullDim R = ringKrullDim S := by
    have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown mR mS
    rw [hm] at h
    calc
      ringKrullDim R = mR.height :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
      _ = mS.height := by
        have hh : mR.height = mS.height := by
          simpa only [Ideal.map_quotient_self, Ideal.height_bot, add_zero] using h.symm
        exact congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hh
      _ = ringKrullDim S := IsLocalRing.maximalIdeal_height_eq_ringKrullDim
  rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  change (Module.finrank (IsLocalRing.ResidueField R) mR.Cotangent : WithBot ℕ∞) ≤ _
  have hlength : Module.finrank (IsLocalRing.ResidueField R) mR.Cotangent =
      Module.finrank (IsLocalRing.ResidueField S) mS.Cotangent := by
    have hbase := IsLocalRing.length_baseChange R S mR.Cotangent
    have hfibre : Module.length S (S ⧸ mR.map (algebraMap R S)) = 1 := by
      rw [hm]
      apply Module.length_eq_one_iff.mpr
      exact (isSimpleModule_iff_quot_maximal).mpr
        ⟨mS, inferInstance, ⟨LinearEquiv.refl S (S ⧸ mS)⟩⟩
    rw [hfibre, mul_one] at hbase
    have hR : Module.length R mR.Cotangent =
        Module.finrank (IsLocalRing.ResidueField R) mR.Cotangent := by
      rw [Module.length_eq_of_surjective IsLocalRing.residue_surjective,
        Module.length_eq_finrank]
    have hS : Module.length S mS.Cotangent =
        Module.finrank (IsLocalRing.ResidueField S) mS.Cotangent := by
      rw [Module.length_eq_of_surjective IsLocalRing.residue_surjective,
        Module.length_eq_finrank]
    rw [e.length_eq, hR, hS] at hbase
    exact_mod_cast hbase.symm
  rw [hlength, ← IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
    IsRegularLocalRing.spanFinrank_maximalIdeal, ← hdim]

end RingHom

namespace AlgebraicGeometry

universe u

namespace Scheme

/-- Regularity at a point ascends along an etale morphism. -/
lemma IsRegularAt.of_etale {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    (y : Y) (h : X.IsRegularAt (f y)) : Y.IsRegularAt y := by
  let : IsRegularLocalRing (X.presheaf.stalk (f y)) := h
  exact RingHom.isRegularLocalRing_of_flat_of_formallyUnramified_of_essFiniteType
    (f.stalkMap y).hom (Flat.stalkMap f y) (FormallyUnramified.stalkMap f y)
      (LocallyOfFiniteType.stalkMap f y)

/-- Regularity at the source point descends to its image along an etale
morphism when the target scheme is locally Noetherian. -/
lemma IsRegularAt.descend_of_etale {X Y : Scheme.{u}} (f : Y ⟶ X) [Etale f]
    [IsLocallyNoetherian X] (y : Y) (h : Y.IsRegularAt y) :
    X.IsRegularAt (f y) := by
  let : IsRegularLocalRing (Y.presheaf.stalk y) := h
  exact RingHom.isRegularLocalRing_of_flat_of_formallyUnramified_of_essFiniteType_of_target
    (f.stalkMap y).hom (Flat.stalkMap f y) (FormallyUnramified.stalkMap f y)
      (LocallyOfFiniteType.stalkMap f y)

namespace IdealSheafData

variable {X Y : Scheme.{u}}

/-- If the ambient scheme is regular along the support of an ideal sheaf,
then the source of an etale morphism is regular along the support of its
pullback. -/
lemma IsAmbientRegularAlongSupport.comap_of_etale
    (I : X.IdealSheafData) (f : Y ⟶ X) [Etale f]
    (hI : I.IsAmbientRegularAlongSupport) :
    (I.comap f).IsAmbientRegularAlongSupport := by
  intro y hy
  apply Scheme.IsRegularAt.of_etale f y
  apply hI (f y)
  simpa [support_comap] using hy

/-- At a point of its support, a normal-crossings ideal sheaf has regular
ambient local ring.  The regularity is read on a strict-normal-crossings
etale chart and then descended along the chart map. -/
lemma IsNormalCrossingsAt.isRegularAt [IsLocallyNoetherian X]
    {I : X.IdealSheafData} {x : X} (hI : I.IsNormalCrossingsAt x)
    (hx : x ∈ I.support) : X.IsRegularAt x := by
  obtain ⟨U, f, u, hf, hfu, hstrict⟩ := hI
  let : Etale f := hf
  rw [← hfu]
  apply Scheme.IsRegularAt.descend_of_etale f u
  apply (hstrict u ?_).1
  rw [support_comap]
  change f u ∈ I.support
  rw [hfu]
  exact hx

/-- Normal crossings force regularity of the ambient locally Noetherian
scheme along the divisor support. -/
lemma IsNormalCrossings.isAmbientRegularAlongSupport [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (hI : I.IsNormalCrossings) :
    I.IsAmbientRegularAlongSupport :=
  fun x hx ↦ (hI x hx).isRegularAt hx

end IdealSheafData

end Scheme


end AlgebraicGeometry
