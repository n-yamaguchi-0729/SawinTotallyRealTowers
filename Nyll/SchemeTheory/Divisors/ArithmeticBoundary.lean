/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Nyll.SchemeTheory.Divisors.Basic
import Nyll.SchemeTheory.FiniteEtale.Basic
import Nyll.SchemeTheory.Normalization.Normal

/-!
# Arithmetic boundary conditions

This file records the scheme-theoretic data used to state boundary conditions
over an integral base, directly on the closed subschemes defined by
irreducible components.

The condition uses local Noetherianity rather than a finite-type or Nagata
hypothesis.  The base is an arbitrary integral scheme; its generic point
specifies the generic fibres occurring below.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme

/-- The reduced closed subscheme carried by an irreducible component.

Unlike `Scheme.irreducibleComponent`, this construction uses the reduced
induced structure and therefore does not require the ambient scheme to be
globally Noetherian. -/
noncomputable def reducedIrreducibleComponent (X : Scheme.{u})
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) : Scheme.{u} :=
  (IdealSheafData.vanishingIdeal
    ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subscheme

/-- The closed immersion of a reduced irreducible component into its ambient
scheme. -/
noncomputable def reducedIrreducibleComponentι (X : Scheme.{u})
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    X.reducedIrreducibleComponent Z hZ ⟶ X :=
  (IdealSheafData.vanishingIdeal
    ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subschemeι

instance (X : Scheme.{u}) (Z : Set X) (hZ : Z ∈ irreducibleComponents X) :
    IsClosedImmersion (X.reducedIrreducibleComponentι Z hZ) := by
  exact inferInstanceAs
    (IsClosedImmersion
      (IdealSheafData.vanishingIdeal
        (X := X) ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩).subschemeι)

@[simp]
lemma reducedIrreducibleComponentι_apply (X : Scheme.{u})
    (Z : Set X) (hZ : Z ∈ irreducibleComponents X)
    (z : X.reducedIrreducibleComponent Z hZ) :
    X.reducedIrreducibleComponentι Z hZ z = z.1 :=
  rfl

namespace IdealSheafData

variable {X S : Scheme.{u}}

/-- The structural morphism from the reduced subscheme carried by an
irreducible component of an ideal-sheaf subscheme. -/
noncomputable def componentToBase (I : X.IdealSheafData) (p : X ⟶ S)
    (Z : Set I.subscheme) (hZ : Z ∈ irreducibleComponents I.subscheme) :
    I.subscheme.reducedIrreducibleComponent Z hZ ⟶ S :=
  I.subscheme.reducedIrreducibleComponentι Z hZ ≫ I.subschemeι ≫ p

end IdealSheafData

namespace EffectiveCartierDivisor

variable {X S : Scheme.{u}}

/-- Every irreducible component of the divisor dominates the base. -/
def IsHorizontalOver (D : EffectiveCartierDivisor X) (p : X ⟶ S) : Prop :=
  ∀ (Z : Set D.1.subscheme) (hZ : Z ∈ irreducibleComponents D.1.subscheme),
    DenseRange (D.1.componentToBase p Z hZ)

/-- Every irreducible component contains a point of the prescribed residue
characteristic where the whole divisor has normal crossings. -/
def HasNormalCrossingPointOfResidueCharacteristicOnEachComponent
    (D : EffectiveCartierDivisor X) (q : ℕ) : Prop :=
  ∀ (Z : Set D.1.subscheme) (_hZ : Z ∈ irreducibleComponents D.1.subscheme),
    ∃ x : D.1.subscheme,
      x ∈ Z ∧
        ringChar (X.residueField (D.1.subschemeι x)) = q ∧
          D.IsNormalCrossingsAt (D.1.subschemeι x)

/-- The morphism to the arithmetic base from a reduced component of the
pullback of a divisor along a finite etale cover. -/
noncomputable def pulledBackComponentToBase
    (D : EffectiveCartierDivisor X) (p : X ⟶ S) (Y : FiniteEtale X)
    (Z : Set (D.1.comap Y.hom).subscheme)
    (hZ : Z ∈ irreducibleComponents (D.1.comap Y.hom).subscheme) :
    (D.1.comap Y.hom).subscheme.reducedIrreducibleComponent Z hZ ⟶ S :=
  (D.1.comap Y.hom).componentToBase (Y.hom ≫ p) Z hZ

end EffectiveCartierDivisor

end Scheme

end AlgebraicGeometry
