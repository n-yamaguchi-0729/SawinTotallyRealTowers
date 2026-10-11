/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Normalization.SubalgebraPreimage
import Nyll.SchemeTheory.RingTheory.Ramification.NativeAlgebraResidueEpi
import Nyll.SchemeTheory.RingTheory.Ramification.NormalizationGaloisInvariant
import Nyll.SchemeTheory.RingTheory.Ramification.FiniteLevelInertiaImage
import Mathlib.FieldTheory.Galois.Profinite

/-!
# The actual normalization residue sequence

The groups and homomorphism below are the native stabilizer and the literal
quotient-algebra automorphism group of the actual integral closure. The
possibly infinite Galois action has the prescribed normalization action.
Normality supplies coefficient descent and the Krull topology supplies the
open stabilizers; the compact residue construction proves surjectivity.
The kernel included into the original Galois group is exactly inertia.
-/

noncomputable section

namespace EtaleFundamentalGroups.Inertia

open SchemeTheory CategoryTheory

universe u v w

attribute [local instance] normalizationCommAlgGaloisAction

/-- The actual decomposition group of the prime of the normalization. -/
def normalizationDecompositionGroup
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
    (Q : Ideal (normalizationCommAlgCat A L)) : GrpCat.{w} :=
  nativeResidueStabilizer (normalizationCommAlgCat A L) Gal(L/K) Q

/-- The literal residue automorphism group over the contracted base prime. -/
def normalizationResidueAutomorphisms
    (A : Type u) (L : Type w) [CommRing A] [CommRing L] [Algebra A L]
    (Q : Ideal (normalizationCommAlgCat A L)) : GrpCat.{w} :=
  nativeAlgebraResidueAutomorphisms (normalizationCommAlgCat A L) Q

/-- The actual decomposition-group inclusion in the original Galois group. -/
def normalizationDecompositionInclusion
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [Algebra.IsAlgebraic K L]
    (Q : Ideal (normalizationCommAlgCat A L)) :
    normalizationDecompositionGroup A K L Q →* Gal(L/K) :=
  nativeResidueStabilizerInclusion (normalizationCommAlgCat A L) Gal(L/K) Q

/-- The actual native stabilizer homomorphism for the original normalization. -/
def normalizationResidueMorphism
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) :
    GrpCat.Hom (normalizationDecompositionGroup A K L Q)
      (normalizationResidueAutomorphisms A L Q) :=
  nativeAlgebraResidueMorphism (normalizationCommAlgCat A L) Gal(L/K) Q
    (normalizationCommAlg_action_comp_coefficient A K L)

/-- Normality and the actual infinite Galois action prove the residue map epic. -/
theorem normalizationResidueMorphism_epi
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsIntegrallyClosed A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsPrime] :
    Epi (C := GrpCat.{w}) (X := normalizationDecompositionGroup A K L Q)
      (Y := normalizationResidueAutomorphisms A L Q)
      (normalizationResidueMorphism A K L Q) :=
  nativeAlgebraResidueMorphism_epi (normalizationCommAlgCat A L) Gal(L/K) Q
    (normalizationCommAlg_action_comp_coefficient A K L)
    (normalizationCommAlg_fixed_exists_coefficient A K L)
    (normalizationCommAlg_fixedSet_isOpen_krull A K L)

/-- The original decomposition group surjects onto the actual residue
algebra automorphisms, with no finite-extension or Henselian hypothesis. -/
theorem normalizationResidueMorphism_surjective
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [IsIntegrallyClosed A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) [Q.IsPrime] :
    Function.Surjective (normalizationResidueMorphism A K L Q).hom'.toFun := by
  have : Epi (C := GrpCat.{w}) (X := normalizationDecompositionGroup A K L Q)
      (Y := normalizationResidueAutomorphisms A L Q)
      (normalizationResidueMorphism A K L Q) :=
    normalizationResidueMorphism_epi A K L Q
  exact nativeGroupMorphism_surjective_of_epi (normalizationResidueMorphism A K L Q)

/-- The actual residue-map kernel, mapped into the original Galois group. -/
def normalizationResidueKernelImage
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) : Subgroup Gal(L/K) :=
  nativeAlgebraResidueKernelImage (normalizationCommAlgCat A L) Gal(L/K) Q
    (normalizationCommAlg_action_comp_coefficient A K L)

/-- The computed kernel image is the native inertia group at the original prime. -/
theorem normalizationResidueKernelImage_eq_inertia
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) :
    normalizationResidueKernelImage A K L Q = Q.inertia Gal(L/K) :=
  nativeAlgebraResidueKernelImage_eq_inertia (normalizationCommAlgCat A L) Gal(L/K) Q
    (normalizationCommAlg_action_comp_coefficient A K L)

/-- The kernel of the literal residue map, included into the original
Galois group, is exactly the original inertia subgroup. -/
theorem normalizationResidueMorphism_map_ker
    (A : Type u) (K : Type v) (L : Type w)
    [CommRing A] [Field K] [Field L]
    [Algebra A K] [IsFractionRing A K] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsGalois K L]
    (Q : Ideal (normalizationCommAlgCat A L)) :
    (normalizationResidueMorphism A K L Q).hom'.ker.map
      (normalizationDecompositionInclusion A K L Q) = Q.inertia Gal(L/K) :=
  normalizationResidueKernelImage_eq_inertia A K L Q

end EtaleFundamentalGroups.Inertia
