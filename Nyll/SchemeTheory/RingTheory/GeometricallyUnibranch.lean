/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.RingHom.PurelyInseparable

/-!
# Geometrically unibranch local rings

The definition uses the normalization of the reduction in its total fraction
ring. It requires the reduction to be a domain, its normalization to be
local, and the resulting residue field extension to be purely inseparable.
This is Stacks Project, Definition 15.108.1, not a criterion formulated in
terms of strict henselization.
-/

noncomputable section

namespace IsLocalRing

universe u

/-- The integral closure of the reduction in its total ring of fractions.
When the reduction is a domain, the ambient ring is its fraction field. -/
abbrev reducedNormalization (R : Type u) [CommRing R] : Type u :=
  integralClosure (R ⧸ nilradical R) (FractionRing (R ⧸ nilradical R))

/-- The actual quotient map followed by the inclusion into the normalization
of the reduction. -/
def reducedNormalizationMap (R : Type u) [CommRing R] :
    R →+* reducedNormalization R :=
  (algebraMap (R ⧸ nilradical R) (reducedNormalization R)).comp
    (Ideal.Quotient.mk (nilradical R))

/-- The normalization map is integral, including for a nonreduced base. -/
theorem reducedNormalizationMap_isIntegral (R : Type u) [CommRing R] :
    (reducedNormalizationMap R).IsIntegral := by
  apply RingHom.IsIntegral.trans
    (Ideal.Quotient.mk (nilradical R))
    (algebraMap (R ⧸ nilradical R) (reducedNormalization R))
  · exact RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective
  · exact algebraMap_isIntegral_iff.mpr inferInstance

/-- When both rings are local, integrality makes the actual normalization
map local: its maximal ideal contracts to the maximal ideal of the base. -/
theorem reducedNormalizationMap_isLocalHom (R : Type u) [CommRing R]
    [IsLocalRing R] [IsLocalRing (reducedNormalization R)] :
    IsLocalHom (reducedNormalizationMap R) := by
  apply ((local_hom_TFAE (reducedNormalizationMap R)).out 5 1).mp
  exact eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal
    (reducedNormalizationMap R) (reducedNormalizationMap_isIntegral R)
    (maximalIdeal (reducedNormalization R)))

/-- A local ring is geometrically unibranch if its reduction is a domain,
the normalization of that reduction is local, and the induced residue field
extension is purely inseparable. -/
def IsGeometricallyUnibranch (R : Type u) [CommRing R] [IsLocalRing R] : Prop :=
  ∃ (_ : IsDomain (R ⧸ nilradical R)) (_ : IsLocalRing (reducedNormalization R)),
    let _ : IsLocalHom (reducedNormalizationMap R) := reducedNormalizationMap_isLocalHom R
    (ResidueField.map (reducedNormalizationMap R)).IsPurelyInseparable

end IsLocalRing
