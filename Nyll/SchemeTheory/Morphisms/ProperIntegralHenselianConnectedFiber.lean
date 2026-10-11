/-
Copyright (c) 2026 Naganori Yamaguchi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
https://github.com/n-yamaguchi-0729
-/

import Nyll.SchemeTheory.Descent.NoetherianImageIdempotentLift
import Nyll.SchemeTheory.Morphisms.ProperIntegralHenselianSections
import Nyll.SchemeTheory.Affine.ConnectedOfGlobalSections
import Nyll.SchemeTheory.Morphisms.ChowDatumProj_nonempty_of
import Nyll.SchemeTheory.ProjectiveSpace.BaseChange
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Algebra.Ring.Idempotent
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom

/-!
# Connected closed fibers of proper integral henselian families

The actual integral projective Chow cover embeds in the base change of
projective space over the integers. Its closed-fiber idempotents descend to
the actual Noetherian image stages and lift to global sections. The global
section ring of the projective cover is local, so every such idempotent is
zero or one. Connectedness then descends through the actual surjective Chow
morphism. No Noetherian or finite-presentation assumption is made on the
original henselian base or proper family.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.NoetherianImageApproximation

universe u

variable (A₀ A : Type u) [CommRing A₀] [CommRing A] [Algebra A₀ A]
variable [IsNoetherianRing A₀] [HenselianLocalRing A]
variable {X₀ : Scheme.{u}} (f₀ : X₀ ⟶ Spec (CommRingCat.of A₀)) [IsProper f₀]
variable {Z : Scheme.{u}} [IsIntegral Z]
variable (j : Z ⟶ (ambientCone A₀ A f₀).pt) [IsClosedImmersion j]

/-- The actual closed fiber of an integral closed subscheme in the fixed
proper ambient model is preconnected. -/
theorem isPreconnected_preimage_closedPoint :
    _root_.IsPreconnected ((originalBaseMap A₀ A f₀ j) ⁻¹' {IsLocalRing.closedPoint A}) := by
  have : HenselianLocalRing Γ(Z, ⊤) :=
    henselianLocalRing_globalSections_of_universallyClosed (originalBaseMap A₀ A f₀ j)
  have : PreconnectedSpace
      (originalResidueFiber A₀ A f₀ j (IsLocalRing.maximalIdeal A)) := by
    apply Scheme.preconnectedSpace_of_globalSections_idempotents
    intro e he
    obtain ⟨a, ha⟩ := exists_appTop_eq_of_closedFiber_isIdempotentElem A₀ A f₀ j e he
    let r := (pullback.fst (originalBaseMap A₀ A f₀ j)
      (SubalgebraStages.residueSpecBaseTop (IsLocalRing.maximalIdeal A))).appTop
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with hu | hu
    · right
      have heUnit : IsUnit e := by
        have h := hu.map r.hom
        change IsUnit (r a) at h
        exact ha ▸ h
      exact (IsIdempotentElem.iff_eq_one_of_isUnit heUnit).mp he
    · left
      have heUnit : IsUnit (1 - e) := by
        have h := hu.map r.hom
        have hvalue : r.hom a = e := ha
        rw [map_sub, map_one, hvalue] at h
        exact h
      exact sub_eq_self.mp ((IsIdempotentElem.iff_eq_one_of_isUnit heUnit).mp he.one_sub)
  have hRange : Set.range
      (SubalgebraStages.residueSpecBaseTop (IsLocalRing.maximalIdeal A)) =
      {IsLocalRing.closedPoint A} :=
    PrimeSpectrum.residueField_comap (IsLocalRing.closedPoint A)
  have h := isPreconnected_range
    (pullback.fst (originalBaseMap A₀ A f₀ j)
      (SubalgebraStages.residueSpecBaseTop (IsLocalRing.maximalIdeal A))).continuous
  rw [Scheme.Pullback.range_fst, hRange] at h
  exact h

end AlgebraicGeometry.NoetherianImageApproximation

namespace AlgebraicGeometry

universe u

/-- The closed fiber of a proper integral scheme over an arbitrary henselian
local ring is preconnected. The projective model and all approximation data
are constructed from the original morphism. -/
theorem isPreconnected_preimage_closedPoint_of_isProper_of_isIntegral
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {Y : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f] :
    _root_.IsPreconnected (f ⁻¹' {IsLocalRing.closedPoint R}) := by
  obtain ⟨D, hIntegral, hSurjective⟩ := ChowDatumProj.exists_integral f
  have : IsIntegral D.V' := hIntegral
  have : Surjective D.p := hSurjective
  let A₀ : CommRingCat.{u} := CommRingCat.of (ULift.{u} ℤ)
  let hA₀ : IsInitial A₀ := CommRingCat.isInitial
  let : Algebra A₀ R := (hA₀.to (CommRingCat.of R)).hom.toAlgebra
  have : IsNoetherianRing A₀ := isNoetherianRing_of_ringEquiv ℤ
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ).symm
  let f₀ := ProjSpace.π A₀ D.Nd
  let E := (ProjSpace.isPullback_map A₀ R D.Nd).isoPullback
  let j : D.V' ⟶ (NoetherianImageApproximation.ambientCone A₀ R f₀).pt := D.ιN ≫ E.hom
  have : IsClosedImmersion j := by
    dsimp only [j]
    infer_instance
  have hbase : NoetherianImageApproximation.originalBaseMap A₀ R f₀ j = D.p ≫ f := by
    change (D.ιN ≫ E.hom) ≫ pullback.snd f₀ _ = D.p ≫ f
    rw [Category.assoc, IsPullback.isoPullback_hom_snd]
    exact D.hoverN
  have hFiber : _root_.IsPreconnected ((D.p ≫ f) ⁻¹' {IsLocalRing.closedPoint R}) := by
    rw [← hbase]
    exact NoetherianImageApproximation.isPreconnected_preimage_closedPoint A₀ R f₀ j
  have hImage : D.p '' ((D.p ≫ f) ⁻¹' {IsLocalRing.closedPoint R}) =
      f ⁻¹' {IsLocalRing.closedPoint R} := by
    apply Set.ext
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      obtain ⟨x, rfl⟩ := D.p.surjective y
      exact ⟨x, hy, rfl⟩
  rw [← hImage]
  exact hFiber.image D.p D.p.continuous.continuousOn

/-- The same closed fiber is nonempty and connected. Properness sends the
nonempty total space to a closed subset containing the base closed point. -/
theorem isConnected_preimage_closedPoint_of_isProper_of_isIntegral
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {Y : Scheme.{u}} [IsIntegral Y]
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsProper f] :
    _root_.IsConnected (f ⁻¹' {IsLocalRing.closedPoint R}) := by
  let y₀ : Y := Classical.choice inferInstance
  have hRange : IsLocalRing.closedPoint R ∈ Set.range f :=
    Specializes.mem_closed (IsLocalRing.specializes_closedPoint (f y₀))
      f.isClosedMap.isClosed_range (Set.mem_range_self y₀)
  obtain ⟨y, hy⟩ := hRange
  exact ⟨⟨y, hy⟩, isPreconnected_preimage_closedPoint_of_isProper_of_isIntegral f⟩

end AlgebraicGeometry
