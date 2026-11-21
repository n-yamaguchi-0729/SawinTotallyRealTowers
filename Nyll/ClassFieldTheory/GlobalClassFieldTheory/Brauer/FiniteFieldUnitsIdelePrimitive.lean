/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Brauer.FiniteIdeleH2Injection
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.AdeleBaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Principal
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
public import Nyll.GaloisCohomology.GroupTheory.H2FiniteIndexTrace

/-!
# Recovering a field-unit primitive from an idele primitive

The actual field-unit embedding factors through the principal-idele
representation isomorphism.  Its degree-two map is therefore injective in
a finite Galois p-extension.  An explicit idele primitive of a field-unit
cocycle consequently supplies a field-unit primitive, the input needed for
the subsequent Hilbert-90 and Kummer correction.
-/

@[expose] public section

open CategoryTheory NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology RelativeIdeleGroup.Cohomology LocalClassFieldTheory
open AlgebraicNumberTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [Algebra K L]

local instance : MulDistribMulAction (Gal(L/K)) Lˣ :=
  galoisGroupFieldUnitsMulDistribMulAction K L

local instance : MulDistribMulAction (Gal(L/K)) (RelativeIdeleGroup K L) :=
  RelativeIdeleGroup.relativeIdeleMulDistribMulAction K L

local instance : MulDistribMulAction (Gal(L/K))
    (RelativeIdeleGroup.principalSubgroup K L) :=
  principalIdeleMulDistribMulAction K L

/-- The actual diagonal embedding of field units as a representation map. -/
def finiteFieldUnitsIdeleRepHom :
    Rep.ofMulDistribMulAction (Gal(L/K)) Lˣ ⟶
      (finiteIdeleShortComplex K L).X₂ :=
  equivariantRepHom (RelativeIdeleGroup.principalIdele K L)
    (fun g x => (RelativeIdeleGroup.smul_principalIdele K L g x).symm)

/-- The original field-unit representation identifies with the principal idèle subgroup. -/
def fieldUnitsPrincipalIdeleRepIso :
    Rep.ofMulDistribMulAction (Gal(L/K)) Lˣ ≅ (finiteIdeleShortComplex K L).X₁ :=
  Rep.mkIso (Representation.Equiv.mk
    (fieldUnitsEquivPrincipalIdeles K L).toAdditive.toIntLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro x
      exact congrArg Additive.ofMul (fieldUnitsEquivPrincipalIdeles_smul K L g x.toMul)))

/-- The field-unit diagonal factors through the original principal idèle inclusion. -/
theorem finiteFieldUnitsIdeleRepHom_factor :
    finiteFieldUnitsIdeleRepHom K L =
      (fieldUnitsPrincipalIdeleRepIso K L).hom ≫ (finiteIdeleShortComplex K L).f := by
  ext x
  rfl

/-- The field-unit-to-idele map is injective in degree two for a finite
Galois p-extension, by the proved idele-class degree-one vanishing. -/
theorem finiteFieldUnitsIdeleH2Map_injective_of_isPGroup
    [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p (Gal(L/K))) :
    Function.Injective
      (groupCohomology.map
        (A := Rep.ofMulDistribMulAction (Gal(L/K)) Lˣ)
        (B := (finiteIdeleShortComplex K L).X₂)
        (MonoidHom.id (Gal(L/K))) (finiteFieldUnitsIdeleRepHom K L) 2).hom := by
  change Function.Injective
    ((groupCohomology.functor ℤ (Gal(L/K)) 2).map (finiteFieldUnitsIdeleRepHom K L)).hom
  rw [finiteFieldUnitsIdeleRepHom_factor, Functor.map_comp]
  exact (finitePrincipalIdeleH2Map_injective_of_isPGroup K L hP).comp
    ((groupCohomology.functor ℤ (Gal(L/K)) 2).mapIso
      (fieldUnitsPrincipalIdeleRepIso K L)).toLinearEquiv.injective

/-- The actual field-unit-to-idele map is injective in degree two for any
finite Galois extension. Each Sylow restriction uses the same top-field
units and ideles over the actual Sylow fixed field. -/
theorem finiteFieldUnitsIdeleH2Map_injective
    [NumberField L] [FiniteDimensional K L] [IsGalois K L] :
    Function.Injective (groupCohomology.map
      (A := Rep.ofMulDistribMulAction Gal(L/K) Lˣ) (B := (finiteIdeleShortComplex K L).X₂)
      (MonoidHom.id (Gal(L/K))) (finiteFieldUnitsIdeleRepHom K L) 2).hom := by
  apply H2_map_injective_of_sylow
  intro p hp P S
  let E := IntermediateField.fixedField S
  let : NumberField E := NumberField.of_module_finite K E
  let : FiniteDimensional E L := FiniteDimensional.right K E L
  let : IsGalois E L := IsGalois.of_fixed_field L S
  let eG := IntermediateField.subgroupEquivAlgEquiv S
  let : MulDistribMulAction (Gal(L/E)) Lˣ := galoisGroupFieldUnitsMulDistribMulAction E L
  let A := Rep.ofMulDistribMulAction (Gal(L/K)) Lˣ
  let B := (finiteIdeleShortComplex K L).X₂
  let A' := Rep.ofMulDistribMulAction (Gal(L/E)) Lˣ
  let B' := (finiteIdeleShortComplex E L).X₂
  let bK := relativeIdeleBaseChangeMulEquiv (K := K) (L := L)
  let bE := relativeIdeleBaseChangeMulEquiv (K := E) (L := L)
  let b := bK.trans bE.symm
  have hb (x : RelativeIdeleGroup K L) : bE (b x) = bK x := bE.apply_symm_apply _
  have hprincipal (x : Lˣ) : b (RelativeIdeleGroup.principalIdele K L x) =
      RelativeIdeleGroup.principalIdele E L x := by
    apply bE.injective
    rw [hb]
    exact (relativeIdeleBaseChangeMulEquiv_principalIdele (K := K) x).trans
      (relativeIdeleBaseChangeMulEquiv_principalIdele (K := E) x).symm
  let eA : (Rep.res S.subtype A).V ≃ₗ[ℤ] A'.V := LinearEquiv.refl ℤ (Additive Lˣ)
  let eB : (Rep.res S.subtype B).V ≃ₗ[ℤ] B'.V := b.toAdditive.toIntLinearEquiv
  have hA (σ : S) : eA ∘ₗ (Rep.res S.subtype A).ρ σ = A'.ρ (eG σ) ∘ₗ eA := by
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply Units.ext
    rfl
  have hB (σ : S) : eB ∘ₗ (Rep.res S.subtype B).ρ σ = B'.ρ (eG σ) ∘ₗ eB := by
    apply LinearMap.ext
    intro x
    apply Additive.toMul.injective
    apply bE.injective
    change bE (b (σ.val • (show Additive (RelativeIdeleGroup K L) from x).toMul)) =
      bE (eG σ • b (show Additive (RelativeIdeleGroup K L) from x).toMul)
    rw [hb, NumberField.IdeleClassGroup.relativeIdeleBaseChange_smul K L,
      NumberField.IdeleClassGroup.relativeIdeleBaseChange_smul E L, hb]
    have hσ : σ.val.restrictScalars ℚ = (eG σ).restrictScalars ℚ := by
      apply AlgEquiv.ext
      intro y
      rfl
    rw [hσ]
  let HA := groupCohomology.mapIso eG eA hA 2
  let HB := groupCohomology.mapIso eG eB hB 2
  let f := (Rep.resFunctor S.subtype).map (finiteFieldUnitsIdeleRepHom K L)
  let f' := finiteFieldUnitsIdeleRepHom E L
  let F := groupCohomology.map
    (A := (Rep.resFunctor S.subtype).obj (Rep.ofMulDistribMulAction Gal(L/K) Lˣ))
    (B := (Rep.resFunctor S.subtype).obj (finiteIdeleShortComplex K L).X₂) (MonoidHom.id S) f 2
  let F' := groupCohomology.map
    (A := Rep.ofMulDistribMulAction Gal(L/E) Lˣ) (B := (finiteIdeleShortComplex E L).X₂)
    (MonoidHom.id (Gal(L/E))) f' 2
  have hmap : F ≫ HB.hom = HA.hom ≫ F' := by
    dsimp only [F, F', HA, HB, groupCohomology.mapIso]
    rw [← groupCohomology.map_comp, ← groupCohomology.map_comp]
    refine groupCohomology.map_congr (by ext σ; rfl) ?_ 2
    apply LinearMap.ext
    intro x
    exact congrArg Additive.ofMul (hprincipal (show Additive Lˣ from x).toMul)
  have hp' : IsPGroup p Gal(L/E) := P.isPGroup.of_equiv eG
  have hinj' := finiteFieldUnitsIdeleH2Map_injective_of_isPGroup E L hp'
  intro x y hxy
  apply HA.toLinearEquiv.injective
  apply hinj'
  change F' (HA.hom x) = F' (HA.hom y)
  have hx := ConcreteCategory.congr_hom hmap x
  have hy := ConcreteCategory.congr_hom hmap y
  change HB.hom (F x) = F' (HA.hom x) at hx
  change HB.hom (F y) = F' (HA.hom y) at hy
  exact hx.symm.trans ((congrArg HB.hom hxy).trans hy)

/-- An explicit idele primitive of a field-unit cocycle yields an actual
field-unit primitive.  The idele primitive is the one constructed by the
unramified local-unit and restricted-product argument. -/
theorem finiteFieldUnitsTwoCocycle_isCoboundary_of_idelePrimitive
    [NumberField L] [FiniteDimensional K L] [IsGalois K L]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p (Gal(L/K)))
    (c : groupCohomology.cocycles₂ (Rep.ofMulDistribMulAction (Gal(L/K)) Lˣ))
    (b : Gal(L/K) → Additive (RelativeIdeleGroup K L))
    (hb : (groupCohomology.d₁₂
        (Rep.ofMulDistribMulAction (Gal(L/K)) (RelativeIdeleGroup K L))).hom b =
      (groupCohomology.mapCocycles₂ (MonoidHom.id (Gal(L/K)))
        (finiteFieldUnitsIdeleRepHom K L) c).1) :
    ∃ a : Gal(L/K) → Additive Lˣ,
      (groupCohomology.d₁₂ (Rep.ofMulDistribMulAction (Gal(L/K)) Lˣ)).hom a = c.1 := by
  let f : groupCohomology.H2 (Rep.ofMulDistribMulAction (Gal(L/K)) Lˣ) →ₗ[ℤ]
      groupCohomology.H2 (finiteIdeleShortComplex K L).X₂ :=
    (groupCohomology.map (MonoidHom.id (Gal(L/K))) (finiteFieldUnitsIdeleRepHom K L) 2).hom
  let cI := groupCohomology.mapCocycles₂ (MonoidHom.id (Gal(L/K)))
    (finiteFieldUnitsIdeleRepHom K L) c
  have hzero : groupCohomology.H2π (finiteIdeleShortComplex K L).X₂ cI = 0 :=
    (groupCohomology.H2π_eq_zero_iff cI).mpr ⟨b, hb⟩
  have hnat := groupCohomology.H2π_comp_map
    (A := Rep.ofMulDistribMulAction (Gal(L/K)) Lˣ)
    (B := (finiteIdeleShortComplex K L).X₂) (MonoidHom.id (Gal(L/K)))
    (finiteFieldUnitsIdeleRepHom K L)
  have heq := congrArg (fun f => f c) hnat
  change f (groupCohomology.H2π _ c) = groupCohomology.H2π _ cI at heq
  exact (groupCohomology.H2π_eq_zero_iff c).mp
    (finiteFieldUnitsIdeleH2Map_injective_of_isPGroup K L hP
      (heq.trans (hzero.trans f.map_zero.symm)))

end ClassFieldTower.Martinet.Shafarevich

end
