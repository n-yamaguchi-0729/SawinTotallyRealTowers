/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Local.FiniteCyclicBaseUnitCarry
import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.HasseNormPrinciple

set_option autoImplicit false
/-!
# Hasse localization of finite-cyclic unit H²

For a cyclic extension of number fields, periodicity identifies degree-two
cohomology of the unit representation with the global field-norm quotient.
Composing this comparison with the concrete Hasse norm diagonal gives an
injective all-place localization map.  This is the cyclic global-duality
input used by the Shafarevich obstruction calculation.
-/

open CategoryTheory
open scoped NumberField

noncomputable section

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology
open CyclicCohomology LocalFieldTheory
open GlobalClassFieldTheory.ClassFieldAxiom

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L]
variable [FiniteDimensional K L] [IsGalois K L]

omit [NumberField K] [NumberField L] [IsGalois K L] in
private theorem localNormSubgroup_eq_globalFieldNormSubgroup :
    localNormSubgroup K L = globalFieldNormSubgroup K L :=
  rfl

/-- The global norm quotient used by cyclic unit cohomology, identified with
the source of the concrete Hasse norm diagonal. -/
noncomputable def finiteCyclicNormQuotientEquivGlobalNormQuotient :
    NormQuotient K L ≃*
      Kˣ ⧸ globalFieldNormSubgroup K L :=
  normQuotientEquivOfSubgroupEq K L
    (globalFieldNormSubgroup K L)
    (localNormSubgroup_eq_globalFieldNormSubgroup K L)

omit [NumberField K] [NumberField L] [IsGalois K L] in
@[simp]
theorem finiteCyclicNormQuotientEquivGlobalNormQuotient_normClass
    (a : Kˣ) :
    finiteCyclicNormQuotientEquivGlobalNormQuotient K L
        (normClass K L a) =
      QuotientGroup.mk' (globalFieldNormSubgroup K L) a := by
  exact normQuotientEquivOfSubgroupEq_normClass K L
    (globalFieldNormSubgroup K L)
    (localNormSubgroup_eq_globalFieldNormSubgroup K L) a

/-- Degree-two cyclic unit cohomology localized at all places through the
concrete Hasse norm diagonal. -/
noncomputable def finiteCyclicUnitsH2HasseLocalization
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 →+
      Additive
        (IdeleGroup K ⧸
          allPlaceLocalNormCondition (K := K) (L := L)) :=
  (hasseNormDiagonal K L).toAdditive.comp
    ((MulEquiv.toAdditive
      (finiteCyclicNormQuotientEquivGlobalNormQuotient K L)).toAddMonoidHom.comp
        (finiteCyclicUnitsH2IsoNormQuotient K L g hg).hom.hom.toAddMonoidHom)

/-- On a normalized carry class with base-field coefficient, Hasse
localization is represented by the corresponding principal idele. -/
@[simp]
theorem finiteCyclicUnitsH2HasseLocalization_carry_baseUnit
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g)
    (a : Kˣ) :
    letI := AlgEquiv.fintype K L
    let : IsCyclic (Gal(L / K)) :=
      isCyclic_of_generator g hg
    letI : CommGroup (Gal(L / K)) := IsCyclic.commGroup
    finiteCyclicUnitsH2HasseLocalization K L g hg
        (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
          (finiteCyclicCarryTwoCocycle (Rep.ofAlgebraAutOnUnits K L)
            g hg (finiteCyclicBaseUnitFixed K L g a))) =
      Additive.ofMul
        (QuotientGroup.mk'
          (allPlaceLocalNormCondition (K := K) (L := L))
          (IdeleGroup.principalIdele K a)) := by
  dsimp only
  let := AlgEquiv.fintype K L
  let : IsCyclic (Gal(L / K)) :=
    isCyclic_of_generator g hg
  let : CommGroup (Gal(L / K)) := IsCyclic.commGroup
  apply Additive.toMul.injective
  change
    hasseNormDiagonal K L
        (finiteCyclicNormQuotientEquivGlobalNormQuotient K L
          (Additive.toMul
            ((finiteCyclicUnitsH2IsoNormQuotient K L g hg).hom
              (groupCohomology.H2π (Rep.ofAlgebraAutOnUnits K L)
                (finiteCyclicCarryTwoCocycle
                  (Rep.ofAlgebraAutOnUnits K L) g hg
                  (finiteCyclicBaseUnitFixed K L g a)))))) =
      QuotientGroup.mk'
        (allPlaceLocalNormCondition (K := K) (L := L))
        (IdeleGroup.principalIdele K a)
  rw [finiteCyclicUnitsH2IsoNormQuotient_carry_baseUnit]
  change
    hasseNormDiagonal K L
        (finiteCyclicNormQuotientEquivGlobalNormQuotient K L
          (normClass K L a)) = _
  rw [finiteCyclicNormQuotientEquivGlobalNormQuotient_normClass]
  exact hasseNormDiagonal_mk a

/-- Hasse's norm theorem makes the cyclic unit-H² localization map
injective. -/
theorem finiteCyclicUnitsH2HasseLocalization_injective
    (g : Gal(L / K))
    (hg : ∀ sigma : Gal(L / K), sigma ∈ Subgroup.zpowers g) :
    Function.Injective
      (finiteCyclicUnitsH2HasseLocalization K L g hg) := by
  let : IsCyclic (Gal(L / K)) :=
    isCyclic_of_generator g hg
  exact (hasseNormDiagonal_injective_cyclic K L).comp
    ((finiteCyclicNormQuotientEquivGlobalNormQuotient K L).injective.comp
      (ConcreteCategory.bijective_of_isIso
        (finiteCyclicUnitsH2IsoNormQuotient K L g hg).hom).1)

end ClassFieldTower.Martinet.Shafarevich
