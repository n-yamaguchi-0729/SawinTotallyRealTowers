/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Residue fields in scheme-theoretic fibres

The inclusion of a scheme-theoretic fibre is surjective on stalks and hence
does not change residue fields.  For a dominant morphism of integral schemes,
the generic point of the generic fibre maps to the generic point of the
source.  Together these facts give the canonical residue-field comparison
used by divisorial generic-fibre arguments.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

variable {X Y : Scheme.{u}}

/-- A morphism surjective on stalks induces bijections on residue fields. -/
theorem Scheme.Hom.residueFieldMap_bijective_of_surjectiveOnStalks
    (f : X ⟶ Y) [SurjectiveOnStalks f] (x : X) :
    Function.Bijective (f.residueFieldMap x) := by
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro z
  obtain ⟨a, rfl⟩ := X.residue_surjective x z
  obtain ⟨b, rfl⟩ := f.stalkMap_surjective x a
  refine ⟨Y.residue (f x) b, ?_⟩
  exact congr($(Scheme.residue_residueFieldMap f x) b)

/-- The inclusion of a scheme-theoretic fibre does not change residue
fields. -/
theorem Scheme.Hom.fiberι_residueFieldMap_bijective
    (f : X ⟶ Y) (y : Y) (z : f.fiber y) :
    Function.Bijective ((f.fiberι y).residueFieldMap z) :=
  (f.fiberι y).residueFieldMap_bijective_of_surjectiveOnStalks z

/-- The residue-field equivalence induced by the inclusion of a
scheme-theoretic fibre. -/
noncomputable def Scheme.Hom.fiberιResidueFieldRingEquiv
    (f : X ⟶ Y) (y : Y) (z : f.fiber y) :
    X.residueField (f.fiberι y z) ≃+* (f.fiber y).residueField z :=
  RingEquiv.ofBijective ((f.fiberι y).residueFieldMap z).hom
    (f.fiberι_residueFieldMap_bijective y z)

/-- If the generic point of an integral source maps to the generic point of
an integral target, the generic point of the generic fibre maps back to the
generic point of the source. -/
theorem Scheme.Hom.fiberι_genericPoint_eq_genericPoint
    [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
    [IsIntegral (f.fiber (genericPoint Y))] :
    f.fiberι (genericPoint Y) (genericPoint (f.fiber (genericPoint Y))) =
      genericPoint X := by
  let E : Set X := f ⁻¹' {genericPoint Y}
  let a : E := ⟨genericPoint X, hη⟩
  have ha : IsGenericPoint a (Set.univ : Set E) := by
    rw [isGenericPoint_def]
    ext y
    simp only [Set.mem_univ, iff_true]
    rw [closure_subtype, Set.image_singleton]
    change (y : X) ∈ closure ({genericPoint X} : Set X)
    rw [genericPoint_spec X]
    trivial
  have hgeneric :=
    ha.image (f.fiberHomeo (genericPoint Y)).symm.continuous
  have hgeneric' : IsGenericPoint
      ((f.fiberHomeo (genericPoint Y)).symm a)
      (Set.univ : Set (f.fiber (genericPoint Y))) := by
    simpa only [Set.image_univ, EquivLike.range_eq_univ, closure_univ]
      using hgeneric
  have heq :
      (f.fiberHomeo (genericPoint Y)).symm a =
        genericPoint (f.fiber (genericPoint Y)) :=
    hgeneric'.eq (genericPoint_spec (f.fiber (genericPoint Y)))
  rw [← heq]
  exact f.fiberι_fiberHomeo_symm (genericPoint Y) a

/-- The generic fibre and the source have canonically equivalent residue
fields at their generic points. -/
noncomputable def Scheme.Hom.genericFiberResidueFieldRingEquiv
    [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hη : f (genericPoint X) = genericPoint Y)
    [IsIntegral (f.fiber (genericPoint Y))] :
    X.residueField (genericPoint X) ≃+*
      (f.fiber (genericPoint Y)).residueField
        (genericPoint (f.fiber (genericPoint Y))) :=
  (X.residueFieldCongr
      (f.fiberι_genericPoint_eq_genericPoint hη).symm).commRingCatIsoToRingEquiv.trans
    (f.fiberιResidueFieldRingEquiv (genericPoint Y)
      (genericPoint (f.fiber (genericPoint Y))))

end AlgebraicGeometry

end
