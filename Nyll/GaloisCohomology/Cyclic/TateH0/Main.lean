/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.Cyclic.TateH0.NormImage

/-!
# Degree-zero Tate cohomology and the norm quotient

This module identifies degree-zero Tate cohomology of the multiplicative group
of a finite Galois extension with the corresponding field norm quotient.
-/

@[expose] public section

namespace CyclicCohomology

open LocalFieldTheory CategoryTheory

noncomputable section

universe u v

/-- Descending invariant units and then taking their field norm class gives
the arithmetic quotient, independently of the two field universes. -/
def invariantsQuotientAddEquivNormQuotient (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    letI := AlgEquiv.fintype K L
    (unitsInvariantSubmodule K L ⧸ unitsTateH0NormSubmodule K L) ≃+
      Additive (NormQuotient K L) := by
  let := AlgEquiv.fintype K L
  let eInv := QuotientAddGroup.congr
    (unitsTateH0NormSubmodule K L).toAddSubgroup (additiveNormSubgroup K L)
    (invariantsUnitsAddEquivBaseUnits K L)
    (invariantsUnitsAddEquivBaseUnits_map_tateNormSubgroup K L)
  let eNorm : (Additive Kˣ ⧸ additiveNormSubgroup K L) ≃+
      Additive (NormQuotient K L) :=
    (QuotientAddGroup.quotientAddEquivOfEq
        (additiveNormSubgroup_eq_ker_quotient_map K L)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        (MonoidHom.toAdditive (normClass K L)) (by
          change Function.Surjective (QuotientGroup.mk' (localNormSubgroup K L))
          exact QuotientGroup.mk'_surjective _))
  exact eInv.trans eNorm

/-- On a representative the arithmetic comparison is precisely the original
field norm class of the descended invariant unit. -/
theorem invariantsQuotientAddEquivNormQuotient_mk (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (x : unitsInvariantSubmodule K L) :
    (letI := AlgEquiv.fintype K L
     invariantsQuotientAddEquivNormQuotient K L
       ((unitsTateH0NormSubmodule K L).mkQ x)) =
      Additive.ofMul (normClass K L
        (Additive.toMul (invariantsUnitsAddEquivBaseUnits K L x))) := rfl

/-- Integral degree-zero Tate cohomology of the actual unit representation
is the field norm quotient for independent base and extension universes. -/
def integralH0TateUnitsAddEquivNormQuotient (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    letI := AlgEquiv.fintype K L
    IntegralGroupCohomology.tate (Rep.ofAlgebraAutOnUnits K L) 0 ≃+
      Additive (NormQuotient K L) := by
  let := AlgEquiv.fintype K L
  exact (integralTateUnitsH0AddEquivInvariantsQuotient K L).trans
    (invariantsQuotientAddEquivNormQuotient K L)

/-- The actual Tate class of an invariant unit is sent to its field norm class. -/
theorem integralH0TateUnitsAddEquivNormQuotient_class (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (x : unitsInvariantSubmodule K L) :
    (letI := AlgEquiv.fintype K L
     integralH0TateUnitsAddEquivNormQuotient K L (integralUnitsTateClass K L x)) =
      Additive.ofMul (normClass K L
        (Additive.toMul (invariantsUnitsAddEquivBaseUnits K L x))) := by
  let := AlgEquiv.fintype K L
  change invariantsQuotientAddEquivNormQuotient K L
      (integralTateUnitsH0AddEquivInvariantsQuotient K L
        (integralUnitsTateClass K L x)) = _
  rw [integralTateUnitsH0AddEquivInvariantsQuotient_class,
    invariantsQuotientAddEquivNormQuotient_mk]

/-- The independent-universe Tate owner has the same arithmetic norm quotient. -/
def universeH0TateUnitsAddEquivNormQuotient (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    letI := AlgEquiv.fintype K L
    IntegralGroupCohomology.Universe.tate (Rep.ofAlgebraAutOnUnits K L) 0 ≃+
      Additive (NormQuotient K L) := by
  let := AlgEquiv.fintype K L
  exact (universeTateUnitsH0AddEquivInvariantsQuotient K L).trans
    (invariantsQuotientAddEquivNormQuotient K L)

/-- The canonical comparison between mathlib's degree-zero Tate cohomology of
`Lˣ` and the field norm quotient `Kˣ / N_{L/K}(Lˣ)` for a finite Galois
extension. -/
def H0TateUnitsIsoNormQuotient (K L : Type)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] :
    CategoryTheory.Iso (tateCohomology (Rep.ofAlgebraAutOnUnits K L) 0)
      (ModuleCat.of Int (Additive (NormQuotient K L))) := by
  let := AlgEquiv.fintype K L
  exact (IntegralGroupCohomology.tateIsoOriginal (Rep.ofAlgebraAutOnUnits K L) 0).symm ≪≫
    (integralH0TateUnitsAddEquivNormQuotient K L).toIntLinearEquiv.toModuleIso

/-- The original literal-integer comparison is the specialization of the
actual integral norm-quotient comparison. -/
theorem H0TateUnitsIsoNormQuotient_integral (K L : Type)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (x : IntegralGroupCohomology.tate (Rep.ofAlgebraAutOnUnits K L) 0) :
    (H0TateUnitsIsoNormQuotient K L).hom
        ((IntegralGroupCohomology.tateIsoOriginal (Rep.ofAlgebraAutOnUnits K L) 0).hom x) =
      integralH0TateUnitsAddEquivNormQuotient K L x := by
  change integralH0TateUnitsAddEquivNormQuotient K L
      ((IntegralGroupCohomology.tateIsoOriginal (Rep.ofAlgebraAutOnUnits K L) 0).inv
        ((IntegralGroupCohomology.tateIsoOriginal (Rep.ofAlgebraAutOnUnits K L) 0).hom x)) = _
  rw [CategoryTheory.Iso.hom_inv_id_apply]

/-- Coefficient transport and the norm quotient retain the actual connecting
map into degree zero for every short exact sequence starting in field units. -/
theorem integralH0TateUnitsAddEquivNormQuotient_connecting (K L : Type)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {B C : Rep ℤ Gal(L/K)} (f : Rep.ofAlgebraAutOnUnits K L ⟶ B) (g : B ⟶ C)
    (hfg : f ≫ g = 0) (hS : (CategoryTheory.ShortComplex.mk f g hfg).ShortExact)
    (z : IntegralGroupCohomology.tate C (-1)) :
    integralH0TateUnitsAddEquivNormQuotient K L
        (IntegralGroupCohomology.tateδ hS (-1) z) =
      (H0TateUnitsIsoNormQuotient K L).hom
        (TateCohomology.δ hS (-1)
          ((IntegralGroupCohomology.tateIsoOriginal C (-1)).hom z)) := by
  have h := congrArg (fun k => k z)
    (IntegralGroupCohomology.tateδ_tateIsoOriginal hS (-1))
  change (IntegralGroupCohomology.tateIsoOriginal (Rep.ofAlgebraAutOnUnits K L) 0).hom
      (IntegralGroupCohomology.tateδ hS (-1) z) =
    TateCohomology.δ hS (-1)
      ((IntegralGroupCohomology.tateIsoOriginal C (-1)).hom z) at h
  have hq := congrArg (fun a => (H0TateUnitsIsoNormQuotient K L).hom a) h
  rw [H0TateUnitsIsoNormQuotient_integral] at hq
  exact hq

end
end CyclicCohomology
