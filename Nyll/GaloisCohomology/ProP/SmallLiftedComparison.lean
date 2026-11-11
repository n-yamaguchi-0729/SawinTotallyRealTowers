/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.ProP.TrivialZModP
public import Nyll.GaloisCohomology.ProP.ContinuousH1Bridge
public import Nyll.GaloisCohomology.Topology.HomogeneousContinuousCochainsFunctor
public import Mathlib.Algebra.Field.ZMod

/-!
# Comparison of small and lifted trivial coefficients

For a group in the base universe, the universe-lifted trivial `ZMod p`
coefficient and the benchmark's small coefficient are isomorphic.  Functoriality
of homogeneous cochains transports this coefficient isomorphism to every
continuous-cohomology degree.
-/

@[expose] public section

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

variable (p : ℕ) (G : Type)
variable [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The induced isomorphism between the homogeneous cochain complexes. -/
noncomputable def trivialZModPCochainsLiftedSmallIso :
    TopRep.homogeneousCochains (trivialZModPLifted p G) ≅
      TopRep.homogeneousCochains (trivialZModP p G) :=
  (TopRep.homogeneousContinuousCochainsFunctorOver (ZMod p) G).mapIso
    (trivialZModPLiftedSmallIso p G)

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

local instance continuousH1ZModModuleSmallComparison :
    Module (ZMod p) (ClassFieldTower.ProP.ContinuousH1ZMod (p := p) (G := G)) :=
  ClassFieldTower.ProP.continuousH1ZModModule

/-- The cochain comparison forgets only the actual coefficient universe lift. -/
@[simp]
theorem trivialZModPCochainsLiftedSmallIso_hom_f_one_apply
    (c : (trivialZModPCochainsLifted p G).X 1) (g h : G) :
    (((trivialZModPCochainsLiftedSmallIso p G).hom.f 1).hom c).1 g h =
      (c.1 g h).down :=
  rfl

/-- Forgetting the coefficient lift preserves the cocycle attached to the same character. -/
theorem trivialZModPLiftedSmallIso_cocyclesMap_cocycleOfH1Lifted
    (χ : ClassFieldTower.ProP.ContinuousH1ZMod (p := p) (G := G)) :
    ContinuousCohomology.cocyclesMap (ContinuousMonoidHom.id G)
        (trivialZModPLiftedSmallIso p G).hom 1 (cocycleOfH1Lifted χ) =
      cocycleOfH1 χ := by
  apply topModule_mono_injective ((trivialZModPCochains p G).iCycles 1)
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i]
  change ((trivialZModPCochainsLiftedSmallIso p G).hom.f 1).hom
      (homogeneousOneCochainOfCocycleLifted (cocycleOfH1Lifted χ)) =
    homogeneousOneCochainOfCocycle (cocycleOfH1 χ)
  rw [homogeneousOneCochainOfCocycleLifted_cocycleOfH1Lifted,
    homogeneousOneCochainOfCocycle_cocycleOfH1]
  apply Subtype.ext
  ext g h
  rw [trivialZModPCochainsLiftedSmallIso_hom_f_one_apply,
    homogeneousOneCochainOfH1Lifted_apply, homogeneousOneCochainOfH1_apply]

/-- The small and lifted degree-one bridges represent the same continuous character. -/
theorem continuousCohomologyZModPLiftedSmallLinearEquiv_h1
    (χ : ClassFieldTower.ProP.ContinuousH1ZMod (p := p) (G := G)) :
    continuousCohomologyZModPLiftedSmallLinearEquiv p G 1
        (continuousH1ZModEquivContinuousCohomologyLifted χ) =
      continuousH1ZModEquivContinuousCohomology χ := by
  change ContinuousCohomology.map (ContinuousMonoidHom.id G)
      (trivialZModPLiftedSmallIso p G).hom 1
      (ContinuousCohomology.π (trivialZModPLifted p G) 1 (cocycleOfH1Lifted χ)) =
    ContinuousCohomology.π (trivialZModP p G) 1 (cocycleOfH1 χ)
  have hπ := congrArg
    (fun f : ContinuousCohomology.cocycles (trivialZModPLifted p G) 1 ⟶
        continuousCohomologyZModP p G 1 => f.hom (cocycleOfH1Lifted χ))
    (ContinuousCohomology.π_map (X := trivialZModPLifted p G) (Y := trivialZModP p G)
      (ContinuousMonoidHom.id G) (trivialZModPLiftedSmallIso p G).hom 1)
  change ContinuousCohomology.map (ContinuousMonoidHom.id G)
      (trivialZModPLiftedSmallIso p G).hom 1
      (ContinuousCohomology.π (trivialZModPLifted p G) 1 (cocycleOfH1Lifted χ)) =
    ContinuousCohomology.π (trivialZModP p G) 1
      (ContinuousCohomology.cocyclesMap (ContinuousMonoidHom.id G)
        (trivialZModPLiftedSmallIso p G).hom 1 (cocycleOfH1Lifted χ)) at hπ
  exact hπ.trans
    (congrArg
      (fun z : ContinuousCohomology.cocycles (trivialZModP p G) 1 =>
        (ContinuousCohomology.π (trivialZModP p G) 1).hom z)
      (trivialZModPLiftedSmallIso_cocyclesMap_cocycleOfH1Lifted p G χ))

/-- Recovering a character commutes with forgetting the coefficient universe lift. -/
theorem continuousH1ZModEquivContinuousCohomology_symm_liftedSmall
    (x : continuousCohomologyZModPLifted p G 1) :
    continuousH1ZModEquivContinuousCohomology.symm
        (continuousCohomologyZModPLiftedSmallLinearEquiv p G 1 x) =
      continuousH1ZModEquivContinuousCohomologyLifted.symm x := by
  apply continuousH1ZModEquivContinuousCohomology.injective
  rw [LinearEquiv.apply_symm_apply]
  simpa only [LinearEquiv.apply_symm_apply] using
    continuousCohomologyZModPLiftedSmallLinearEquiv_h1 p G
      (continuousH1ZModEquivContinuousCohomologyLifted.symm x)

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
