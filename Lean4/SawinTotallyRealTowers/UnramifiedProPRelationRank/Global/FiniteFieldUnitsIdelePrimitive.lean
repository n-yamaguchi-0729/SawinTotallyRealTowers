import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.FiniteIdeleH2Injection
import ClassFieldTheory.AlgebraicNumberTheory.Idele.Principal

set_option autoImplicit false
/-!
# Recovering a field-unit primitive from an idele primitive

The actual field-unit embedding factors through the principal-idele
representation isomorphism.  Its degree-two map is therefore injective in
a finite Galois p-extension.  An explicit idele primitive of a field-unit
cocycle consequently supplies a field-unit primitive, the input needed for
the subsequent Hilbert-90 and Kummer correction.
-/

open CategoryTheory NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open RelativeIdeleGroup.Cohomology LocalClassFieldTheory
open CyclicCohomology.ProfiniteCohomology.Herbrand

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [Algebra K L]

local instance : MulDistribMulAction (Gal(L/K)) Lˣ :=
  galoisGroupFieldUnitsMulDistribMulAction K L

local instance : MulDistribMulAction (Gal(L/K)) (RelativeIdeleGroup K L) :=
  relativeIdeleMulDistribMulAction K L

local instance : MulDistribMulAction (Gal(L/K))
    (RelativeIdeleGroup.principalSubgroup K L) :=
  principalIdeleMulDistribMulAction K L

/-- The actual diagonal embedding of field units as a representation map. -/
def finiteFieldUnitsIdeleRepHom :
    Rep.ofMulDistribMulAction (Gal(L/K)) Lˣ ⟶
      (finiteIdeleShortComplex K L).X₂ :=
  equivariantRepHom (RelativeIdeleGroup.principalIdele K L)
    (fun g x => (RelativeIdeleGroup.smul_principalIdele K L g x).symm)

private def fieldUnitsPrincipalIdeleRepIso :
    Rep.ofMulDistribMulAction (Gal(L/K)) Lˣ ≅ (finiteIdeleShortComplex K L).X₁ :=
  Rep.mkIso (Representation.Equiv.mk
    (fieldUnitsEquivPrincipalIdeles K L).toAdditive.toIntLinearEquiv (by
      intro g
      apply LinearMap.ext
      intro x
      exact congrArg Additive.ofMul (fieldUnitsEquivPrincipalIdeles_smul K L g x.toMul)))

private theorem finiteFieldUnitsIdeleRepHom_factor :
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
