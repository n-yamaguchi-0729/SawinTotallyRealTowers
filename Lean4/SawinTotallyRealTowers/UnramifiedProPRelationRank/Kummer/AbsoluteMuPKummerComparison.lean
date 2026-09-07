import GaloisCohomology.ProP.ContinuousH1Bridge
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteKummerH1Linear
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPKummerLinear
import SawinTotallyRealTowers.UnramifiedProPRelationRank.Kummer.AbsoluteMuPTrivialization

set_option autoImplicit false
/-!
# Comparing natural and trivial-coefficient absolute Kummer H¹

Over a field containing a primitive `p`-th root of unity, the natural
`mu_p` representation is trivial.  This file transports its continuous
cohomology through that trivialization and proves that the natural
coefficient Kummer map becomes the usual `ZMod p`-character Kummer map.
-/

open scoped Pointwise Topology

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open CategoryTheory KummerTheory TopRep ContRepresentation
open ClassFieldTower.ProP

local instance absoluteMuPComparisonH1Module
    {q : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Module (ZMod q) (ContinuousH1ZMod (p := q) (G := G)) :=
  continuousH1ZModModule

variable (K : Type) [Field K] [CharZero K]
variable (p : ℕ) [Fact p.Prime]

/-- The coefficient trivialization induces an isomorphism on homogeneous
continuous cochain complexes. -/
noncomputable def absoluteMuPCochainsIsoTrivial
    (hmu : (primitiveRoots p K).Nonempty) :
    TopRep.homogeneousCochains (absoluteMuPTopRep K p) ≅
      TopRep.homogeneousCochains
        (ClassFieldTower.Cohomology.trivialZModP p
          (Field.absoluteGaloisGroup K)) where
  hom := ContinuousCohomology.cochainsMap
    (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
    (absoluteMuPTopRepTrivialIso K p hmu).hom
  inv := ContinuousCohomology.cochainsMap
    (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
    (absoluteMuPTopRepTrivialIso K p hmu).inv
  hom_inv_id := by
    refine (ContinuousCohomology.cochainsMap_comp
      (X := absoluteMuPTopRep K p)
      (Y := ClassFieldTower.Cohomology.trivialZModP p
        (Field.absoluteGaloisGroup K))
      (Z := absoluteMuPTopRep K p)
      (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
      (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
      (absoluteMuPTopRepTrivialIso K p hmu).hom
      (absoluteMuPTopRepTrivialIso K p hmu).inv).symm.trans ?_
    have hcoeff :
        (TopRep.resFunctor
          ((ContinuousMonoidHom.id (Field.absoluteGaloisGroup K)) :
            Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup K)).map
            (absoluteMuPTopRepTrivialIso K p hmu).hom ≫
          (absoluteMuPTopRepTrivialIso K p hmu).inv =
        𝟙 (absoluteMuPTopRep K p) := by
      exact (absoluteMuPTopRepTrivialIso K p hmu).hom_inv_id
    exact (congrArg
      (fun f : absoluteMuPTopRep K p ⟶ absoluteMuPTopRep K p =>
        ContinuousCohomology.cochainsMap
          (X := absoluteMuPTopRep K p) (Y := absoluteMuPTopRep K p)
          (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K)) f) hcoeff).trans
      (ContinuousCohomology.cochainsMap_id (absoluteMuPTopRep K p))
  inv_hom_id := by
    refine (ContinuousCohomology.cochainsMap_comp
      (X := ClassFieldTower.Cohomology.trivialZModP p
        (Field.absoluteGaloisGroup K))
      (Y := absoluteMuPTopRep K p)
      (Z := ClassFieldTower.Cohomology.trivialZModP p
        (Field.absoluteGaloisGroup K))
      (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
      (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
      (absoluteMuPTopRepTrivialIso K p hmu).inv
      (absoluteMuPTopRepTrivialIso K p hmu).hom).symm.trans ?_
    have hcoeff :
        (TopRep.resFunctor
          ((ContinuousMonoidHom.id (Field.absoluteGaloisGroup K)) :
            Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup K)).map
            (absoluteMuPTopRepTrivialIso K p hmu).inv ≫
          (absoluteMuPTopRepTrivialIso K p hmu).hom =
        𝟙 (ClassFieldTower.Cohomology.trivialZModP p
          (Field.absoluteGaloisGroup K)) := by
      exact (absoluteMuPTopRepTrivialIso K p hmu).inv_hom_id
    exact (congrArg
      (fun f : ClassFieldTower.Cohomology.trivialZModP p
          (Field.absoluteGaloisGroup K) ⟶
          ClassFieldTower.Cohomology.trivialZModP p
            (Field.absoluteGaloisGroup K) =>
        ContinuousCohomology.cochainsMap
          (X := ClassFieldTower.Cohomology.trivialZModP p
            (Field.absoluteGaloisGroup K))
          (Y := ClassFieldTower.Cohomology.trivialZModP p
            (Field.absoluteGaloisGroup K))
          (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K)) f) hcoeff).trans
      (ContinuousCohomology.cochainsMap_id
        (ClassFieldTower.Cohomology.trivialZModP p
          (Field.absoluteGaloisGroup K)))

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

/-- In degree one, coefficient trivialization followed by the standard
cohomology-character bridge. -/
noncomputable def absoluteMuPH1EquivContinuousH1ZMod
    (hmu : (primitiveRoots p K).Nonempty) :
    continuousCohomology 1 (absoluteMuPTopRep K p) ≃ₗ[ZMod p]
      ContinuousH1ZMod
        (p := p) (G := Field.absoluteGaloisGroup K) :=
  (absoluteMuPContinuousCohomologyLinearEquivTrivial K p hmu 1).trans
    ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomology.symm

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
  let Czero := ClassFieldTower.Cohomology.trivialZModPCochains p
    (Field.absoluteGaloisGroup K)
  apply ClassFieldTower.Cohomology.topModule_mono_injective (Czero.iCycles 1)
  change Czero.iCycles 1
      (ContinuousCohomology.cocyclesMap
        (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
        (absoluteMuPTopRepTrivialIso K p hmu).hom 1
        (absoluteKummerMuPHomogeneousOneCocycle K p a)) =
    Czero.iCycles 1
      (ClassFieldTower.Cohomology.cocycleOfH1
        (absoluteKummerContinuousH1LinearEquiv K p hmu
          (Additive.ofMul
            (QuotientGroup.mk'
              (powMonoidHom p : Kˣ →* Kˣ).range a))))
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i]
  let chi := absoluteKummerContinuousH1LinearEquiv K p hmu
    (Additive.ofMul
      (QuotientGroup.mk' (powMonoidHom p : Kˣ →* Kˣ).range a))
  calc
    _ = ClassFieldTower.Cohomology.homogeneousOneCochainOfH1 chi := by
      apply Subtype.ext
      ext g h
      rw [ConcreteCategory.comp_apply]
      rw [absoluteMuPCochainsIsoTrivial_hom_f_one_apply]
      rw [iCycles_absoluteKummerMuPHomogeneousOneCocycle]
      rw [ClassFieldTower.Cohomology.homogeneousOneCochainOfH1_apply]
      rw [absoluteKummerMuPHomogeneousOneCochain_eq_action]
      rw [absoluteMuPAction_eq_self_of_primitiveRoots K p hmu]
      exact absoluteKummerContinuousH1LinearEquiv_mk_apply
        K p hmu a (g⁻¹ * h)
    _ = Czero.iCycles 1
        (ClassFieldTower.Cohomology.cocycleOfH1 chi) :=
      (ClassFieldTower.Cohomology.homogeneousOneCochainOfCocycle_cocycleOfH1
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
    ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomology.symm
      (absoluteMuPContinuousCohomologyLinearEquivTrivial K p hmu 1
        (absoluteKummerMuPH1Class K p a)) = _
  rw [absoluteMuPContinuousCohomologyLinearEquivTrivial_apply]
  change
    ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomology.symm
      (ContinuousCohomology.map
        (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
        (absoluteMuPTopRepTrivialIso K p hmu).hom 1
        (ContinuousCohomology.π (absoluteMuPTopRep K p) 1
          (absoluteKummerMuPHomogeneousOneCocycle K p a))) = _
  have hπ :
      ContinuousCohomology.map
          (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
          (absoluteMuPTopRepTrivialIso K p hmu).hom 1
          (ContinuousCohomology.π (absoluteMuPTopRep K p) 1
            (absoluteKummerMuPHomogeneousOneCocycle K p a)) =
        ContinuousCohomology.π
          (ClassFieldTower.Cohomology.trivialZModP p
            (Field.absoluteGaloisGroup K)) 1
          (ContinuousCohomology.cocyclesMap
            (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
            (absoluteMuPTopRepTrivialIso K p hmu).hom 1
            (absoluteKummerMuPHomogeneousOneCocycle K p a)) := by
    exact ConcreteCategory.congr_hom (ContinuousCohomology.π_map
      (X := absoluteMuPTopRep K p)
      (Y := ClassFieldTower.Cohomology.trivialZModP p
        (Field.absoluteGaloisGroup K))
      (ContinuousMonoidHom.id (Field.absoluteGaloisGroup K))
      (absoluteMuPTopRepTrivialIso K p hmu).hom 1)
      (absoluteKummerMuPHomogeneousOneCocycle K p a)
  rw [hπ]
  rw [absoluteMuPCocyclesMap_kummer_eq]
  exact
    ClassFieldTower.Cohomology.continuousH1ZModEquivContinuousCohomology.symm_apply_apply _

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

end ClassFieldTower.Martinet.Shafarevich
