/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.ProP.ContinuousH1Bridge
public import Nyll.GaloisCohomology.ProP.SmallLiftedComparison
public import Nyll.GaloisCohomology.Topology.HomogeneousContinuousCochainsFunctor
public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteKummerH1Linear
public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPKummerLinear
public import Nyll.SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTrivialization
public import Nyll.GaloisCohomology.ProP.TrivialZModP

/-!
# Comparing natural and trivial-coefficient absolute Kummer H¹

Over a field containing a primitive `p`-th root of unity, the natural
`mu_p` representation is trivial.  This file transports its continuous
cohomology through that trivialization and proves that the natural
coefficient Kummer map becomes the usual `ZMod p`-character Kummer map.
The coefficient carrier is lifted to the universe of the field; at universe zero,
the original small-coefficient API is recovered by the existing coefficient comparison.
-/

@[expose] public section

open scoped Pointwise Topology

noncomputable section

universe u

namespace ClassFieldTower.Martinet.Shafarevich

open CategoryTheory KummerTheory TopRep ContRepresentation
open ClassFieldTower.ProP

local instance absoluteMuPComparisonH1Module
    {q : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := G)) :=
  continuousH1ZModModule

section GeneralUniverse

variable (K : Type u) [Field K] [CharZero K]
variable (p : ℕ) [Fact p.Prime]

/-- The actual coefficient trivialization induces an isomorphism of homogeneous cochains
with carrier lifted to the universe of the base field. -/
noncomputable def absoluteMuPCochainsIsoTrivialLifted
    (hmu : (primitiveRoots p K).Nonempty) :
    TopRep.homogeneousCochains (absoluteMuPTopRep K p) ≅
      TopRep.homogeneousCochains
        (ClassFieldTower.Cohomology.trivialZModPLifted p
          (Field.absoluteGaloisGroup K)) :=
  (TopRep.homogeneousContinuousCochainsFunctorOver (ZMod p)
    (Field.absoluteGaloisGroup K)).mapIso
      (absoluteMuPTopRepTrivialIsoLifted K p hmu)

/-- Natural `mu_p` cohomology transported to the actual lifted trivial coefficients. -/
noncomputable def absoluteMuPContinuousCohomologyIsoTrivialLifted
    (hmu : (primitiveRoots p K).Nonempty) (n : ℕ) :
    continuousCohomology n (absoluteMuPTopRep K p) ≅
      ClassFieldTower.Cohomology.continuousCohomologyZModPLifted p
        (Field.absoluteGaloisGroup K) n :=
  (HomologicalComplex.homologyFunctor (TopModuleCat.{u} (ZMod p))
    (ComplexShape.up ℕ) n).mapIso
      (absoluteMuPCochainsIsoTrivialLifted K p hmu)

/-- Linear form of the actual lifted coefficient transport. -/
noncomputable def absoluteMuPContinuousCohomologyLinearEquivTrivialLifted
    (hmu : (primitiveRoots p K).Nonempty) (n : ℕ) :
    continuousCohomology n (absoluteMuPTopRep K p) ≃ₗ[ZMod p]
      ClassFieldTower.Cohomology.continuousCohomologyZModPLifted p
        (Field.absoluteGaloisGroup K) n :=
  (absoluteMuPContinuousCohomologyIsoTrivialLifted K p hmu n)
    |>.toContinuousLinearEquiv.toLinearEquiv

omit [CharZero K] in
@[simp]
theorem absoluteMuPContinuousCohomologyLinearEquivTrivialLifted_apply
    (hmu : (primitiveRoots p K).Nonempty) (n : ℕ)
    (x : continuousCohomology n (absoluteMuPTopRep K p)) :
    absoluteMuPContinuousCohomologyLinearEquivTrivialLifted K p hmu n x =
      ContinuousCohomology.map
        (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
        (absoluteMuPTopRepTrivialIsoLifted K p hmu).hom n x :=
  rfl

omit [CharZero K] in
/-- On one-cochains the map is the original coefficient equivalence followed by `ULift.up`. -/
@[simp]
theorem absoluteMuPCochainsIsoTrivialLifted_hom_f_one_apply
    (hmu : (primitiveRoots p K).Nonempty)
    (c : (TopRep.homogeneousCochains (absoluteMuPTopRep K p)).X 1)
    (g h : Field.absoluteGaloisGroup K) :
    (((ContinuousCohomology.cochainsMap
      (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
      (absoluteMuPTopRepTrivialIsoLifted K p hmu).hom).f 1).hom c).1 g h =
      ULift.up.{u} (absoluteMuPLinearEquivZMod K p hmu (c.1 g h)) :=
  rfl

/-- In degree one, coefficient trivialization followed by the standard
cohomology-character bridge. -/
noncomputable def absoluteMuPH1EquivContinuousH1ZMod
    (hmu : (primitiveRoots p K).Nonempty) :
    continuousCohomology 1 (absoluteMuPTopRep K p) ≃ₗ[ZMod p]
      ContinuousH1ZMod
        (p := p) (G := Field.absoluteGaloisGroup K) :=
  (absoluteMuPContinuousCohomologyLinearEquivTrivialLifted K p hmu 1).trans
    ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomologyLifted.symm

/-- Continuous multiplicative `ZMod p` characters, reinterpreted as additive
continuous `H¹` classes. -/
noncomputable def absoluteContinuousZModCharacterH1LinearEquiv :
    absoluteContinuousZModCharacterModP K p ≃ₗ[ZMod p]
      ContinuousH1ZMod
        (p := p) (G := Field.absoluteGaloisGroup K) := by
  let G := Field.absoluteGaloisGroup K
  letI : Module (ZMod p)
      (Additive (G →ₜ* Multiplicative (ZMod p))) :=
    additiveZModModuleOfPowEqOne p
      (absoluteContinuousZModCharacter_pow_eq_one K p)
  let e : Additive (G →ₜ* Multiplicative (ZMod p)) ≃+
      ContinuousH1ZMod (p := p) (G := G) :=
    { toFun := fun chi ↦ h1OfCharacter (Additive.toMul chi)
      invFun := fun chi ↦ Additive.ofMul (characterOfH1 chi)
      left_inv := fun chi ↦ by ext sigma; rfl
      right_inv := fun chi ↦ by ext sigma; rfl
      map_add' := fun chi psi ↦ by ext sigma; rfl }
  exact { e with map_smul' := ZMod.map_smul e }

omit [CharZero K] in
@[simp]
theorem absoluteContinuousZModCharacterH1LinearEquiv_apply
    (chi : absoluteContinuousZModCharacterModP K p)
    (sigma : Field.absoluteGaloisGroup K) :
    absoluteContinuousZModCharacterH1LinearEquiv K p chi
        (Additive.ofMul sigma) =
      (Additive.toMul
        (show Additive
            (Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod p))
          from chi) sigma).toAdd :=
  rfl

/-- The usual character-valued absolute Kummer equivalence, expressed in the
additive continuous-`H¹` convention. -/
noncomputable def absoluteKummerContinuousH1LinearEquiv
    (hmu : (primitiveRoots p K).Nonempty) :
    absolutePowerClassModP K p ≃ₗ[ZMod p]
      ContinuousH1ZMod
        (p := p) (G := Field.absoluteGaloisGroup K) :=
  (absoluteKummerContinuousZModCharacterLinearEquiv K p hmu).trans
    (absoluteContinuousZModCharacterH1LinearEquiv K p)

theorem absoluteKummerContinuousZModCharacterLinearEquiv_mk_apply
    (hmu : (primitiveRoots p K).Nonempty) (a : Kˣ)
    (sigma : Field.absoluteGaloisGroup K) :
    ((show Additive
        (Field.absoluteGaloisGroup K →ₜ* Multiplicative (ZMod p)) from
      absoluteKummerContinuousZModCharacterLinearEquiv K p hmu
        (Additive.ofMul
          (QuotientGroup.mk'
            (powMonoidHom p : Kˣ →* Kˣ).range a))).toMul sigma).toAdd =
      absoluteMuPLinearEquivZMod K p hmu
        (absoluteKummerMuPRootCocycle K p a sigma) := by
  rfl

@[simp]
theorem absoluteKummerContinuousH1LinearEquiv_mk_apply
    (hmu : (primitiveRoots p K).Nonempty) (a : Kˣ)
    (sigma : Field.absoluteGaloisGroup K) :
    absoluteKummerContinuousH1LinearEquiv K p hmu
        (Additive.ofMul
          (QuotientGroup.mk'
            (powMonoidHom p : Kˣ →* Kˣ).range a))
        (Additive.ofMul sigma) =
      absoluteMuPLinearEquivZMod K p hmu
        (absoluteKummerMuPRootCocycle K p a sigma) := by
  exact absoluteKummerContinuousZModCharacterLinearEquiv_mk_apply
    K p hmu a sigma

/-- Mapping the natural-coefficient Kummer cocycle through coefficient
trivialization gives the cocycle attached to the usual Kummer character. -/
theorem absoluteMuPCocyclesMap_kummer_eq_lifted
    (hmu : (primitiveRoots p K).Nonempty) (a : Kˣ) :
    ContinuousCohomology.cocyclesMap
        (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
        (absoluteMuPTopRepTrivialIsoLifted K p hmu).hom 1
        (absoluteKummerMuPHomogeneousOneCocycle K p a) =
      ClassFieldTower.Cohomology.cocycleOfH1Lifted
        (absoluteKummerContinuousH1LinearEquiv K p hmu
          (Additive.ofMul
            (QuotientGroup.mk'
              (powMonoidHom p : Kˣ →* Kˣ).range a))) := by
  let Czero := ClassFieldTower.Cohomology.trivialZModPCochainsLifted p
    (Field.absoluteGaloisGroup K)
  apply ClassFieldTower.Cohomology.topModule_mono_injective_lifted (Czero.iCycles 1)
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i]
  let chi := absoluteKummerContinuousH1LinearEquiv K p hmu
    (Additive.ofMul
      (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a))
  calc
    _ = ClassFieldTower.Cohomology.homogeneousOneCochainOfH1Lifted chi := by
      apply Subtype.ext
      ext g h
      rw [ConcreteCategory.comp_apply]
      rw [absoluteMuPCochainsIsoTrivialLifted_hom_f_one_apply]
      rw [iCycles_absoluteKummerMuPHomogeneousOneCocycle]
      rw [ClassFieldTower.Cohomology.homogeneousOneCochainOfH1Lifted_apply]
      rw [absoluteKummerMuPHomogeneousOneCochain_eq_action]
      rw [absoluteMuPAction_eq_self_of_primitiveRoots K p hmu]
      apply ULift.ext
      exact (absoluteKummerContinuousH1LinearEquiv_mk_apply
        K p hmu a (g⁻¹ * h)).symm
    _ = Czero.iCycles 1
        (ClassFieldTower.Cohomology.cocycleOfH1Lifted chi) :=
      (ClassFieldTower.Cohomology.homogeneousOneCochainOfCocycleLifted_cocycleOfH1Lifted
        chi).symm

/-- The natural `mu_p` Kummer class becomes the standard continuous
character-valued Kummer class after coefficient trivialization. -/
theorem absoluteMuPH1EquivContinuousH1ZMod_kummerClass
    (hmu : (primitiveRoots p K).Nonempty) (a : Kˣ) :
    absoluteMuPH1EquivContinuousH1ZMod K p hmu
        (absoluteKummerMuPH1Class K p a) =
      absoluteKummerContinuousH1LinearEquiv K p hmu
        (Additive.ofMul
          (QuotientGroup.mk'
            (powMonoidHom p : Kˣ →* Kˣ).range a)) := by
  change
    ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomologyLifted.symm
      (absoluteMuPContinuousCohomologyLinearEquivTrivialLifted K p hmu 1
        (absoluteKummerMuPH1Class K p a)) = _
  rw [absoluteMuPContinuousCohomologyLinearEquivTrivialLifted_apply]
  change
    ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomologyLifted.symm
      (ContinuousCohomology.map
        (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
        (absoluteMuPTopRepTrivialIsoLifted K p hmu).hom 1
        (ContinuousCohomology.π (absoluteMuPTopRep K p) 1
          (absoluteKummerMuPHomogeneousOneCocycle K p a))) = _
  have hπ :
      ContinuousCohomology.map
          (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
          (absoluteMuPTopRepTrivialIsoLifted K p hmu).hom 1
          (ContinuousCohomology.π (absoluteMuPTopRep K p) 1
            (absoluteKummerMuPHomogeneousOneCocycle K p a)) =
        ContinuousCohomology.π
          (ClassFieldTower.Cohomology.trivialZModPLifted p
            (Field.absoluteGaloisGroup K)) 1
          (ContinuousCohomology.cocyclesMap
            (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
            (absoluteMuPTopRepTrivialIsoLifted K p hmu).hom 1
            (absoluteKummerMuPHomogeneousOneCocycle K p a)) := by
    exact ConcreteCategory.congr_hom (ContinuousCohomology.π_map
      (X := absoluteMuPTopRep K p)
      (Y := ClassFieldTower.Cohomology.trivialZModPLifted p
        (Field.absoluteGaloisGroup K))
      (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
      (absoluteMuPTopRepTrivialIsoLifted K p hmu).hom 1)
      (absoluteKummerMuPHomogeneousOneCocycle K p a)
  rw [hπ]
  rw [absoluteMuPCocyclesMap_kummer_eq_lifted]
  exact
    ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomologyLifted.symm_apply_apply _

/-- Linear-map form of the absolute Kummer comparison. -/
theorem absoluteMuPKummerH1LinearMap_compare
    (hmu : (primitiveRoots p K).Nonempty) :
    (absoluteMuPH1EquivContinuousH1ZMod K p hmu).toLinearMap.comp
        (absoluteKummerMuPH1LinearMap K p) =
      (absoluteKummerContinuousH1LinearEquiv K p hmu).toLinearMap := by
  apply LinearMap.ext
  intro x
  let q :
      (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) :=
    Additive.toMul x
  change
    absoluteMuPH1EquivContinuousH1ZMod K p hmu
        (absoluteKummerMuPH1LinearMap K p (Additive.ofMul q)) =
      absoluteKummerContinuousH1LinearEquiv K p hmu (Additive.ofMul q)
  refine QuotientGroup.induction_on q ?_
  intro a
  erw [absoluteKummerMuPH1LinearMap_mk]
  exact absoluteMuPH1EquivContinuousH1ZMod_kummerClass K p hmu a

end GeneralUniverse

section SmallUniverse

variable (K : Type) [Field K] [CharZero K]
variable (p : ℕ) [Fact p.Prime]

/-- The coefficient trivialization induces an isomorphism on homogeneous
continuous cochain complexes. -/
noncomputable def absoluteMuPCochainsIsoTrivial
    (hmu : (primitiveRoots p K).Nonempty) :
    TopRep.homogeneousCochains (absoluteMuPTopRep K p) ≅
      TopRep.homogeneousCochains
        (ClassFieldTower.Cohomology.trivialZModP p
          (Field.absoluteGaloisGroup K)) :=
  (TopRep.homogeneousContinuousCochainsFunctorOver (ZMod p)
    (Field.absoluteGaloisGroup K)).mapIso
      (absoluteMuPTopRepTrivialIso K p hmu)

/-- Cohomology with natural `mu_p` coefficients transported to the standard
trivial `ZMod p` coefficient representation. -/
noncomputable def absoluteMuPContinuousCohomologyIsoTrivial
    (hmu : (primitiveRoots p K).Nonempty) (n : ℕ) :
    continuousCohomology n (absoluteMuPTopRep K p) ≅
      ClassFieldTower.Cohomology.continuousCohomologyZModP p
        (Field.absoluteGaloisGroup K) n :=
  (HomologicalComplex.homologyFunctor (TopModuleCat (ZMod p))
    (ComplexShape.up ℕ) n).mapIso
      (absoluteMuPCochainsIsoTrivial K p hmu)

/-- Linear form of the cohomology transport induced by coefficient
trivialization. -/
noncomputable def absoluteMuPContinuousCohomologyLinearEquivTrivial
    (hmu : (primitiveRoots p K).Nonempty) (n : ℕ) :
    continuousCohomology n (absoluteMuPTopRep K p) ≃ₗ[ZMod p]
      ClassFieldTower.Cohomology.continuousCohomologyZModP p
        (Field.absoluteGaloisGroup K) n :=
  (absoluteMuPContinuousCohomologyIsoTrivial K p hmu n)
    |>.toContinuousLinearEquiv.toLinearEquiv

omit [CharZero K] in
@[simp]
theorem absoluteMuPContinuousCohomologyLinearEquivTrivial_apply
    (hmu : (primitiveRoots p K).Nonempty) (n : ℕ)
    (x : continuousCohomology n (absoluteMuPTopRep K p)) :
    absoluteMuPContinuousCohomologyLinearEquivTrivial K p hmu n x =
      ContinuousCohomology.map
        (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
        (absoluteMuPTopRepTrivialIso K p hmu).hom n x := by
  rfl

omit [CharZero K] in
@[simp]
theorem absoluteMuPCochainsIsoTrivial_hom_f_one_apply
    (hmu : (primitiveRoots p K).Nonempty)
    (c : (TopRep.homogeneousCochains (absoluteMuPTopRep K p)).X 1)
    (g h : Field.absoluteGaloisGroup K) :
    (((ContinuousCohomology.cochainsMap
      (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
      (absoluteMuPTopRepTrivialIso K p hmu).hom).f 1).hom c).1 g h =
      absoluteMuPLinearEquivZMod K p hmu (c.1 g h) := by
  rfl

omit [CharZero K] in
/-- The old small cochain comparison is the lifted comparison followed by forgetting the lift. -/
theorem absoluteMuPCochainsIsoTrivial_eq_lifted_trans
    (hmu : (primitiveRoots p K).Nonempty) :
    absoluteMuPCochainsIsoTrivial K p hmu =
      absoluteMuPCochainsIsoTrivialLifted K p hmu ≪≫
        ClassFieldTower.Cohomology.trivialZModPCochainsLiftedSmallIso p
          (Field.absoluteGaloisGroup K) :=
  (TopRep.homogeneousContinuousCochainsFunctorOver (ZMod p)
    (Field.absoluteGaloisGroup K)).mapIso_trans
      (absoluteMuPTopRepTrivialIsoLifted K p hmu)
      (ClassFieldTower.Cohomology.trivialZModPLiftedSmallIso p
        (Field.absoluteGaloisGroup K))

omit [CharZero K] in
/-- The old small cohomology map is the same lifted map followed by the native small comparison. -/
theorem absoluteMuPContinuousCohomologyLinearEquivTrivial_apply_eq_lifted
    (hmu : (primitiveRoots p K).Nonempty) (n : ℕ)
    (x : continuousCohomology n (absoluteMuPTopRep K p)) :
    absoluteMuPContinuousCohomologyLinearEquivTrivial K p hmu n x =
      ClassFieldTower.Cohomology.continuousCohomologyZModPLiftedSmallLinearEquiv p
        (Field.absoluteGaloisGroup K) n
        (absoluteMuPContinuousCohomologyLinearEquivTrivialLifted K p hmu n x) := by
  let F := HomologicalComplex.homologyFunctor (TopModuleCat.{0} (ZMod p)) (ComplexShape.up ℕ) n
  let e := absoluteMuPCochainsIsoTrivialLifted K p hmu
  let f := ClassFieldTower.Cohomology.trivialZModPCochainsLiftedSmallIso p
    (Field.absoluteGaloisGroup K)
  have h : absoluteMuPContinuousCohomologyIsoTrivial K p hmu n =
      absoluteMuPContinuousCohomologyIsoTrivialLifted K p hmu n ≪≫
        ClassFieldTower.Cohomology.continuousCohomologyZModPLiftedSmallIso p
          (Field.absoluteGaloisGroup K) n := by
    change F.mapIso (absoluteMuPCochainsIsoTrivial K p hmu) = F.mapIso e ≪≫ F.mapIso f
    exact (congrArg F.mapIso
      (absoluteMuPCochainsIsoTrivial_eq_lifted_trans K p hmu)).trans (F.mapIso_trans e f)
  exact congrArg (fun i : continuousCohomology n (absoluteMuPTopRep K p) ≅
    ClassFieldTower.Cohomology.continuousCohomologyZModP p
      (Field.absoluteGaloisGroup K) n => i.hom.hom x) h

omit [CharZero K] in
/-- The universe-polymorphic character comparison agrees with the original small convention. -/
theorem absoluteMuPH1EquivContinuousH1ZMod_eq_original
    (hmu : (primitiveRoots p K).Nonempty) :
    absoluteMuPH1EquivContinuousH1ZMod K p hmu =
      (absoluteMuPContinuousCohomologyLinearEquivTrivial K p hmu 1).trans
        ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomology.symm := by
  apply LinearEquiv.ext
  intro x
  change ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomologyLifted.symm
      (absoluteMuPContinuousCohomologyLinearEquivTrivialLifted K p hmu 1 x) =
    ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomology.symm
      (absoluteMuPContinuousCohomologyLinearEquivTrivial K p hmu 1 x)
  rw [absoluteMuPContinuousCohomologyLinearEquivTrivial_apply_eq_lifted]
  exact (ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomology_symm_liftedSmall
    p (Field.absoluteGaloisGroup K)
      (absoluteMuPContinuousCohomologyLinearEquivTrivialLifted K p hmu 1 x)).symm

/-- Mapping the natural-coefficient Kummer cocycle through coefficient
trivialization gives the cocycle attached to the usual Kummer character. -/
theorem absoluteMuPCocyclesMap_kummer_eq
    (hmu : (primitiveRoots p K).Nonempty) (a : Kˣ) :
    ContinuousCohomology.cocyclesMap
        (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
        (absoluteMuPTopRepTrivialIso K p hmu).hom 1
        (absoluteKummerMuPHomogeneousOneCocycle K p a) =
      ClassFieldTower.Cohomology.cocycleOfH1
        (absoluteKummerContinuousH1LinearEquiv K p hmu
          (Additive.ofMul
            (QuotientGroup.mk'
              (powMonoidHom p : Kˣ →* Kˣ).range a))) := by
  let X := absoluteMuPTopRep K p
  let Y := ClassFieldTower.Cohomology.trivialZModP p (Field.absoluteGaloisGroup K)
  let z : ContinuousCohomology.cocycles X 1 := absoluteKummerMuPHomogeneousOneCocycle K p a
  have hc := congrArg (fun i : TopRep.homogeneousCochains X ≅ TopRep.homogeneousCochains Y =>
    (HomologicalComplex.cyclesMap i.hom 1).hom z)
    (absoluteMuPCochainsIsoTrivial_eq_lifted_trans K p hmu)
  rw [Iso.trans_hom, HomologicalComplex.cyclesMap_comp, ConcreteCategory.comp_apply] at hc
  refine hc.trans ?_
  change ContinuousCohomology.cocyclesMap
      (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
      (ClassFieldTower.Cohomology.trivialZModPLiftedSmallIso p
        (Field.absoluteGaloisGroup K)).hom 1
      (ContinuousCohomology.cocyclesMap
        (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
        (absoluteMuPTopRepTrivialIsoLifted K p hmu).hom 1
        (absoluteKummerMuPHomogeneousOneCocycle K p a)) = _
  rw [absoluteMuPCocyclesMap_kummer_eq_lifted]
  exact ClassFieldTower.Cohomology.trivialZModPLiftedSmallIso_cocyclesMap_cocycleOfH1Lifted
    p (Field.absoluteGaloisGroup K) _

end SmallUniverse

end ClassFieldTower.Martinet.Shafarevich
