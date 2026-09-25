/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.ProP.TrivialZModP
import Mathlib.Algebra.Field.ZMod

set_option autoImplicit false
/-!
# Comparison of small and lifted trivial coefficients

For a group in the base universe, the universe-lifted trivial `ZMod p`
coefficient and the benchmark's small coefficient are isomorphic.  Functoriality
of homogeneous cochains transports this coefficient isomorphism to every
continuous-cohomology degree.
-/

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

variable (p : ℕ) (G : Type)
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

local instance continuousSMulULiftZModSmall :
    ContinuousSMul (ZMod p) (ULift.{0} (ZMod p)) :=
  ContinuousSMul.induced ULift.moduleEquiv.toLinearMap

/-- Forget the universe lift on the trivial coefficient representation. -/
noncomputable def trivialZModPLiftedToSmall :
    trivialZModPLifted p G ⟶ trivialZModP p G := by
  apply TopRep.ofHom
  exact
    { toContinuousLinearMap :=
        (ContinuousLinearEquiv.ulift :
          ULift.{0} (ZMod p) ≃L[ZMod p] ZMod p).toContinuousLinearMap
      isIntertwining' := by
        intro g
        apply ContinuousLinearMap.ext
        intro x
        rfl }

/-- Lift the benchmark's small trivial coefficient representation. -/
noncomputable def trivialZModPSmallToLifted :
    trivialZModP p G ⟶ trivialZModPLifted p G := by
  apply TopRep.ofHom
  exact
    { toContinuousLinearMap :=
        (ContinuousLinearEquiv.ulift :
          ULift.{0} (ZMod p) ≃L[ZMod p] ZMod p).symm.toContinuousLinearMap
      isIntertwining' := by
        intro g
        rfl }

/-- The small and lifted trivial coefficient representations are isomorphic. -/
noncomputable def trivialZModPLiftedSmallIso :
    trivialZModPLifted p G ≅ trivialZModP p G where
  hom := trivialZModPLiftedToSmall p G
  inv := trivialZModPSmallToLifted p G
  hom_inv_id := rfl
  inv_hom_id := rfl

/-- The induced isomorphism between the homogeneous cochain complexes. -/
noncomputable def trivialZModPCochainsLiftedSmallIso :
    TopRep.homogeneousCochains (trivialZModPLifted p G) ≅
      TopRep.homogeneousCochains (trivialZModP p G) where
  hom := ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G)
    (trivialZModPLiftedSmallIso p G).hom
  inv := ContinuousCohomology.cochainsMap (ContinuousMonoidHom.id G)
    (trivialZModPLiftedSmallIso p G).inv
  hom_inv_id := by
    exact (ContinuousCohomology.cochainsMap_comp
      (X := trivialZModPLifted p G) (Y := trivialZModP p G)
      (Z := trivialZModPLifted p G)
      (ContinuousMonoidHom.id G) (ContinuousMonoidHom.id G)
      (trivialZModPLiftedSmallIso p G).hom
      (trivialZModPLiftedSmallIso p G).inv).symm.trans
      (ContinuousCohomology.cochainsMap_id _)
  inv_hom_id := by
    exact (ContinuousCohomology.cochainsMap_comp
      (X := trivialZModP p G) (Y := trivialZModPLifted p G)
      (Z := trivialZModP p G)
      (ContinuousMonoidHom.id G) (ContinuousMonoidHom.id G)
      (trivialZModPLiftedSmallIso p G).inv
      (trivialZModPLiftedSmallIso p G).hom).symm.trans
      (ContinuousCohomology.cochainsMap_id _)

/-- The categorical continuous-cohomology comparison in every degree. -/
noncomputable def continuousCohomologyZModPLiftedSmallIso (n : ℕ) :
    continuousCohomologyZModPLifted p G n ≅
      continuousCohomologyZModP p G n :=
  (HomologicalComplex.homologyFunctor (TopModuleCat (ZMod p))
    (ComplexShape.up ℕ) n).mapIso (trivialZModPCochainsLiftedSmallIso p G)

/-- The `ZMod p`-linear continuous-cohomology comparison in every degree. -/
noncomputable def continuousCohomologyZModPLiftedSmallLinearEquiv (n : ℕ) :
    continuousCohomologyZModPLifted p G n ≃ₗ[ZMod p]
      continuousCohomologyZModP p G n :=
  (continuousCohomologyZModPLiftedSmallIso p G n).toContinuousLinearEquiv.toLinearEquiv

/-- Small and lifted trivial coefficients give the same cohomological dimension. -/
theorem continuousCohomologyZModPLiftedSmall_finrank_eq (n : ℕ) :
    Module.finrank (ZMod p) (continuousCohomologyZModPLifted p G n) =
      Module.finrank (ZMod p) (continuousCohomologyZModP p G n) :=
  (continuousCohomologyZModPLiftedSmallLinearEquiv p G n).finrank_eq

/-- Finite dimensionality can be checked using either coefficient model. -/
theorem continuousCohomologyZModP_finiteDimensional_iff_lifted
    [Fact p.Prime] (n : ℕ) :
    FiniteDimensional (ZMod p) (continuousCohomologyZModP p G n) ↔
      FiniteDimensional (ZMod p) (continuousCohomologyZModPLifted p G n) := by
  constructor
  · intro hSmall
    let := hSmall
    exact FiniteDimensional.of_injective
      (continuousCohomologyZModPLiftedSmallLinearEquiv p G n).toLinearMap
      (continuousCohomologyZModPLiftedSmallLinearEquiv p G n).injective
  · intro hLifted
    let := hLifted
    exact FiniteDimensional.of_injective
      (continuousCohomologyZModPLiftedSmallLinearEquiv p G n).symm.toLinearMap
      (continuousCohomologyZModPLiftedSmallLinearEquiv p G n).symm.injective

end


end ClassFieldTower.Cohomology
