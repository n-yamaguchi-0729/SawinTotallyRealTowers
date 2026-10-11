/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.AbhyankarLemma.Geometry.CyclicInertia.FiniteLevelCyclotomicInversion
import Nyll.SchemeTheory.AbhyankarLemma.Geometry.Inertia.IdealLocalization

/-!
# Cyclotomic inversion for normalization-ideal inertia

Localization identifies ideal-theoretic inertia in a Dedekind normalization
with inertia for the corresponding discrete valuation subring.  Finite-level
cyclotomic inversion therefore gives conjugacy to inversion directly in the
ambient finite Galois group.
-/

noncomputable section


universe uA uB uK uL

namespace TameAbhyankar.SGA1

open RamificationTheory.HilbertRamification
open RamificationTheory.HilbertRamification.ValuationSubring

attribute [local instance] Ideal.Quotient.field

/-- At a nonzero maximal ideal of a Dedekind normalization, geometric
integrality of the characteristic-zero decomposition residue field makes
every ideal-inertia element conjugate to its inverse in the ambient finite
Galois group.

The proof uses the actual finite-level normal residue extension; it does not
identify that residue field with a separable closure. -/
theorem idealInertia_isConj_inv_of_geometricallyIntegral_residue_of_ratEquiv
    (k : Type uL) [Field k] (e : k ≃+* ℚ)
    {A : Type uA} {B : Type uB} {K : Type uK} {L : Type uL}
    [CommRing A] [CommRing B] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K]
    [Algebra B L] [IsFractionRing B L]
    [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsIntegralClosure B A L] [IsDedekindDomain B]
    [FiniteDimensional K L] [IsGalois K L]
    (P : Ideal B) [P.IsMaximal] (hP : P ≠ ⊥)
    [Algebra k (decompositionResidueField K
      (idealLocalizationValuationSubring B L P hP))]
    [Algebra k (selectedResidueField
      (idealLocalizationValuationSubring B L P hP))]
    [IsScalarTower k
      (decompositionResidueField K
        (idealLocalizationValuationSubring B L P hP))
      (selectedResidueField
        (idealLocalizationValuationSubring B L P hP))]
    (hgeo : AlgebraicGeometry.GeometricallyIntegral
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap k (decompositionResidueField K
          (idealLocalizationValuationSubring B L P hP)))))) :
    letI := IsIntegralClosure.MulSemiringAction A K L B
    ∀ sigma : P.toAddSubgroup.inertia Gal(L/K),
      IsConj (sigma : Gal(L/K))
        ((sigma⁻¹ : P.toAddSubgroup.inertia Gal(L/K)) : Gal(L/K)) := by
  let := IsIntegralClosure.MulSemiringAction A K L B
  let V := idealLocalizationValuationSubring B L P hP
  let : Finite Gal(L/K) := IsGaloisGroup.finite Gal(L/K) K L
  let : Finite (inertiaGroup K V) := inferInstance
  obtain ⟨g, hg⟩ :=
    exists_inertiaConjugate_eq_inv_of_geometricallyIntegral_residueExtension_of_ratEquiv
      k e K V hgeo
  intro sigma
  let tau : inertiaGroup K V :=
    globalIdealInertiaToLocalInertia
      (A := A) (P := P) (hP := hP) sigma
  have htau : inertiaConjugate K V g tau = tau⁻¹ := hg tau
  refine isConj_iff.mpr ⟨(g : Gal(L/K)), ?_⟩
  have hdecomp := congrArg Subtype.val htau
  have hgal := congrArg Subtype.val hdecomp
  simpa [inertiaConjugate, tau, globalIdealInertiaToLocalInertia,
    globalIdealInertiaToDecomposition] using hgal

end TameAbhyankar.SGA1

end
