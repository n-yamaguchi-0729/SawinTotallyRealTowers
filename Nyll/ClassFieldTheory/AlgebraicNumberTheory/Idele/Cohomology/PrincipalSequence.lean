/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
public import Nyll.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison

/-! # The principal-idèle short exact sequence and its Tate quotient map -/

@[expose] public section

open scoped NumberField
open CategoryTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand

noncomputable section

namespace RelativeIdeleGroup.Cohomology

attribute [local instance] RelativeIdeleGroup.relativeIdeleMulDistribMulAction
  principalIdeleMulDistribMulAction ideleClassMulDistribMulAction

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

/-- The actual principal inclusion and idèle-class quotient, with their
existing equivariant actions, as one short complex of representations. -/
noncomputable def principalIdeleShortComplex : ShortComplex (Rep ℤ (L ≃ₐ[K] L)) :=
  equivariantShortComplex (G := L ≃ₐ[K] L)
    (A := RelativeIdeleGroup.principalSubgroup K L) (B := RelativeIdeleGroup K L)
    (C := RelativeIdeleGroup.ClassGroup K L)
    (RelativeIdeleGroup.principalSubgroup K L).subtype
    (QuotientGroup.mk' (RelativeIdeleGroup.principalSubgroup K L))
    (principalIdeleSubtype_equivariant K L)
    (ideleClassQuotientMap_equivariant K L)
    (principalIdele_ideleClass_exact K L)

omit [NumberField L] [FiniteDimensional K L] [IsGalois K L] in
/-- The principal inclusion and idèle-class quotient form a short exact complex. -/
theorem principalIdeleShortComplex_shortExact :
    (principalIdeleShortComplex K L).ShortExact := by
  unfold principalIdeleShortComplex
  apply equivariantShortComplex_shortExact
  · exact (RelativeIdeleGroup.principalSubgroup K L).subtype_injective
  · exact QuotientGroup.mk'_surjective (RelativeIdeleGroup.principalSubgroup K L)

/-- The quotient map `I_L → C_L` on degree-minus-one Tate cohomology. -/
noncomputable def ideleToClassTateMinusOne :
    Multiplicative (tateCohomology
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (RelativeIdeleGroup K L)) (-1)) →*
    Multiplicative (tateCohomology
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L) (RelativeIdeleGroup.ClassGroup K L)) (-1)) :=
  let f := (tateCohomologyFunctor (-1)).map (principalIdeleShortComplex K L).g
  f.hom.toAddMonoidHom.toMultiplicative

end RelativeIdeleGroup.Cohomology
