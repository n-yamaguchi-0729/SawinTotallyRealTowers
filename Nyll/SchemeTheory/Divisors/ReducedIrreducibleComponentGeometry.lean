/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Divisors.IrreducibleComponentMap
import Nyll.SchemeTheory.FunctionFields.Functoriality
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem

/-!
# Geometry of reduced irreducible components

The reduced closed subscheme carried by an irreducible component is integral.
Its generic point maps to the canonical generic point of the chosen component.
These facts let later local-chart constructions select the correct prime of an
ambient affine neighbourhood without introducing an extra component point.
-/

noncomputable section


open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme

variable (X : Scheme.{u}) (Z : Set X)
  (hZ : Z ∈ irreducibleComponents X)

/-- The reduced closed subscheme supported on an irreducible component is
integral. -/
instance reducedIrreducibleComponent_isIntegral :
    IsIntegral (X.reducedIrreducibleComponent Z hZ) := by
  let I := IdealSheafData.vanishingIdeal
    ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
  let : IrreducibleSpace I.subscheme := by
    change IrreducibleSpace (I.support : Set X)
    rw [IdealSheafData.coe_support_vanishingIdeal]
    exact Subtype.irreducibleSpace hZ.1
  let : IsReduced I.subscheme := by
    simpa only [I, reducedIrreducibleComponent] using
      (reducedIrreducibleComponent_isReduced X Z hZ)
  exact isIntegral_of_irreducibleSpace_of_isReduced I.subscheme

/-- The reduced component immersion has exactly the chosen component as its
set-theoretic range. -/
@[simp]
theorem range_reducedIrreducibleComponentι :
    Set.range (X.reducedIrreducibleComponentι Z hZ) = Z := by
  let I := IdealSheafData.vanishingIdeal
    ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩
  change Set.range I.subschemeι = Z
  calc
    Set.range I.subschemeι = I.support :=
      IdealSheafData.range_subschemeι I
    _ = Z := by
      ext x
      exact Iff.rfl

/-- The generic point of the reduced component maps to the canonical generic
point of its chosen topological irreducible component. -/
theorem reducedIrreducibleComponentι_genericPoint :
    X.reducedIrreducibleComponentι Z hZ
        (genericPoint (X.reducedIrreducibleComponent Z hZ)) =
      (genericPoints.ofComponent ⟨Z, hZ⟩).1 := by
  let C := X.reducedIrreducibleComponent Z hZ
  let i := X.reducedIrreducibleComponentι Z hZ
  have hgeneric : IsGenericPoint (i (genericPoint C)) Z := by
    have himage := (genericPoint_spec C).image i.continuous
    rw [Set.image_univ, show Set.range i = Z by
      simpa only [i] using range_reducedIrreducibleComponentι X Z hZ,
      (isClosed_of_mem_irreducibleComponents Z hZ).closure_eq] at himage
    exact himage
  exact hgeneric.eq
    (genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩)

end Scheme

namespace Scheme.IdealSheafData

variable {X S : Scheme.{u}}

/-- The point of the ambient scheme underlying the generic point of a chosen
irreducible component of an ideal-sheaf subscheme. -/
noncomputable def componentGenericPoint (I : X.IdealSheafData)
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme) : X :=
  I.subschemeι
    (I.subscheme.reducedIrreducibleComponentι Z hZ
      (genericPoint (I.subscheme.reducedIrreducibleComponent Z hZ)))

/-- The component generic point is the image of the canonical topological
generic point of that component. -/
theorem componentGenericPoint_eq (I : X.IdealSheafData)
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme) :
    I.componentGenericPoint Z hZ =
      I.subschemeι (genericPoints.ofComponent ⟨Z, hZ⟩).1 := by
  rw [componentGenericPoint,
    Scheme.reducedIrreducibleComponentι_genericPoint]

/-- The generic point of every irreducible component of an ideal-sheaf
subscheme lies in the support of the ideal sheaf. -/
theorem componentGenericPoint_mem_support (I : X.IdealSheafData)
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme) :
    I.componentGenericPoint Z hZ ∈ I.support := by
  rw [componentGenericPoint_eq]
  exact I.range_subschemeι.le
    ⟨(genericPoints.ofComponent ⟨Z, hZ⟩).1, rfl⟩

/-- Ambient regularity along the support applies, without a separately
chosen point hypothesis, at the generic point of every component. -/
theorem IsAmbientRegularAlongSupport.isRegularAt_componentGenericPoint
    {I : X.IdealSheafData} (hI : I.IsAmbientRegularAlongSupport)
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme) :
    X.IsRegularAt (I.componentGenericPoint Z hZ) :=
  hI _ (I.componentGenericPoint_mem_support Z hZ)

/-- The effective-Cartier structure supplies an affine principal chart at
the generic point of a chosen component.  In particular, no chart or local
equation has to be added as an independent hypothesis downstream. -/
theorem IsEffectiveCartier.exists_affineChart_at_componentGenericPoint
    {I : X.IdealSheafData} (hI : I.IsEffectiveCartier)
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme) :
    ∃ (U : X.affineOpens)
      (_hx : I.componentGenericPoint Z hZ ∈ U.1) (f : Γ(X, U.1)),
      IsRegular f ∧ I.ideal U = Ideal.span {f} :=
  hI (I.componentGenericPoint Z hZ)

/-- The generic point of a component of an effective Cartier divisor on a
locally Noetherian scheme has codimension one.  A Cartier equation is a
non-zero-divisor, so no minimal prime can contain it; global integrality of
the ambient scheme is unnecessary. -/
theorem IsEffectiveCartier.coheight_componentGenericPoint_eq_one
    [IsLocallyNoetherian X]
    {I : X.IdealSheafData} (hI : I.IsEffectiveCartier)
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme) :
    Order.coheight (I.componentGenericPoint Z hZ) = 1 := by
  let η : I.subscheme := (genericPoints.ofComponent ⟨Z, hZ⟩).1
  let x : X := I.componentGenericPoint Z hZ
  obtain ⟨U, hxU, f, hf, hIf⟩ :=
    hI.exists_affineChart_at_componentGenericPoint Z hZ
  let A := Γ(X, U.1)
  let xU : U.1 := ⟨x, hxU⟩
  let : Nonempty U.1 := ⟨xU⟩
  let P : Ideal A := (U.2.primeIdealOf xU).asIdeal
  let j : I.glueDataObj U ⟶ I.subscheme := I.subschemeCover.f U
  let : IsOpenImmersion j := I.subschemeCover.map_prop U
  have hηZ : η ∈ Z :=
    (genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩).mem
  have hηrange : η ∈ Set.range j := by
    change η ∈ j.opensRange
    rw [show j.opensRange = I.subschemeι ⁻¹ᵁ U.1 from
      I.opensRange_subschemeCover_map U]
    change I.subschemeι η ∈ U.1
    rw [← I.componentGenericPoint_eq Z hZ]
    exact hxU
  have hmeet : (Z ∩ Set.range j).Nonempty := ⟨η, hηZ, hηrange⟩
  have hW : j ⁻¹' Z ∈ irreducibleComponents (I.glueDataObj U) :=
    preimage_mem_irreducibleComponents hZ j.isOpenEmbedding hmeet
  let q : PrimeSpectrum (A ⧸ I.ideal U) :=
    (genericPoints.ofComponent ⟨j ⁻¹' Z, hW⟩).1
  have hqgeneric : IsGenericPoint q (j ⁻¹' Z) :=
    genericPoints.isGenericPoint_ofComponent ⟨j ⁻¹' Z, hW⟩
  have hjqgeneric : IsGenericPoint (j q) Z := by
    have himage := hqgeneric.image j.continuous
    have hclosure : closure (j '' (j ⁻¹' Z)) = Z :=
      closure_image_preimage_of_isPreirreducible j j.isOpenMap Z
        hqgeneric.isIrreducible.nonempty hZ.1.2
        (isClosed_of_mem_irreducibleComponents Z hZ)
    exact hclosure ▸ himage
  have hjqη : j q = η :=
    hjqgeneric.eq
      (genericPoints.isGenericPoint_ofComponent ⟨Z, hZ⟩)
  have hqmin : q.asIdeal ∈ minimalPrimes (A ⧸ I.ideal U) := by
    rw [← PrimeSpectrum.vanishingIdeal_singleton,
      PrimeSpectrum.vanishingIdeal_mem_minimalPrimes, hqgeneric.def]
    exact hW
  have hambient :
      (I.glueDataObjι U ≫ U.1.ι) q = x := by
    have hcover : (j ≫ I.subschemeι) q = x := by
      rw [Scheme.Hom.comp_apply, hjqη]
      exact (I.componentGenericPoint_eq Z hZ).symm
    exact (congrArg (fun k : I.glueDataObj U ⟶ X => k q)
      (I.subschemeCover_map_subschemeι U)).symm.trans hcover
  have hfromSpec :
      U.2.fromSpec
          (Spec.map (CommRingCat.ofHom
            (Ideal.Quotient.mk (I.ideal U))) q) = x := by
    rw [I.glueDataObjι_ι U] at hambient
    exact hambient
  have hpoint :
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (I.ideal U))) q =
        U.2.primeIdealOf xU := by
    have : IsOpenImmersion U.2.fromSpec :=
      IsAffineOpen.isOpenImmersion_fromSpec U.2
    apply U.2.fromSpec.isEmbedding.injective
    rw [U.2.fromSpec_primeIdealOf]
    exact hfromSpec
  have hPq : P = q.asIdeal.comap (Ideal.Quotient.mk (I.ideal U)) := by
    change (U.2.primeIdealOf xU).asIdeal = _
    rw [← hpoint]
    rfl
  have hPmin : P ∈ (I.ideal U).minimalPrimes := by
    rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨q.asIdeal, hqmin, hPq.symm⟩
  let : IsNoetherianRing A :=
    IsLocallyNoetherian.component_noetherian U
  let : P.IsPrime := hPmin.isPrime
  have hPminf : P ∈ (Ideal.span {f}).minimalPrimes := by
    rw [← hIf]
    exact hPmin
  have hPheight_le : P.height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes
      (Ideal.span {f}) P hPminf
  have hfP : f ∈ P := by
    apply hPmin.le
    rw [hIf]
    exact Ideal.mem_span_singleton_self f
  have hPheight : P.height = 1 := by
    apply le_antisymm hPheight_le
    apply Order.one_le_iff_ne_zero.mpr
    intro hzero
    have hminimal : P ∈ minimalPrimes A :=
      Ideal.height_eq_zero_iff.mp hzero
    exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes hfP hminimal
      (isRegular_iff_mem_nonZeroDivisors.mp hf)
  let : Algebra Γ(X, U.1) (X.presheaf.stalk (xU : X)) :=
    X.presheaf.algebra_section_stalk xU
  let : IsLocalization.AtPrime (X.presheaf.stalk (xU : X))
      (U.2.primeIdealOf xU).asIdeal := U.2.isLocalization_stalk xU
  have hdim : ringKrullDim (X.presheaf.stalk x) =
      ((P.height : ℕ∞) : WithBot ℕ∞) := by
    simpa only [xU, P, A] using
      (IsLocalization.AtPrime.ringKrullDim_eq_height
        (U.2.primeIdealOf xU).asIdeal
        (X.presheaf.stalk (xU : X)))
  apply WithBot.coe_eq_coe.mp
  calc
    ((Order.coheight x : ℕ∞) : WithBot ℕ∞) =
        ringKrullDim (X.presheaf.stalk x) :=
      (ringKrullDim_stalk_eq_coheight x).symm
    _ = ((P.height : ℕ∞) : WithBot ℕ∞) := hdim
    _ = (((1 : ℕ∞)) : WithBot ℕ∞) := by rw [hPheight]

/-- A dominant structural morphism from a reduced component sends its
generic point to the generic point of the integral base. -/
theorem componentToBase_genericPoint (I : X.IdealSheafData) (p : X ⟶ S)
    [IsIntegral S]
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme)
    (hDense : DenseRange (I.componentToBase p Z hZ)) :
    I.componentToBase p Z hZ
        (genericPoint (I.subscheme.reducedIrreducibleComponent Z hZ)) =
      genericPoint S :=
  Scheme.Hom.map_genericPoint_of_denseRange
    (I.componentToBase p Z hZ) hDense

end Scheme.IdealSheafData

end AlgebraicGeometry

end
