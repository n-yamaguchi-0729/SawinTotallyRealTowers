/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import GaloisCohomology.Kummer.FiniteGaloisUnitsH2Inflation
import GaloisCohomology.Kummer.QuotientTwoCocycle
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Group.Units.Hom
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.FieldTheory.IntermediateField.Basic
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.Normal.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90

set_option autoImplicit false

open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

variable (K L : Type) [Field K] [Field L] [Algebra K L]
variable (E : IntermediateField K L)

/-- Restriction to the fixing subgroup uses the actual relative automorphism
 action on the same field units. -/
def finiteGaloisUnitsRelativeCohomologyIso (n : ℕ) :
    groupCohomology (Rep.res E.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K L)) n ≅
      groupCohomology (Rep.ofAlgebraAutOnUnits E L) n :=
  groupCohomology.mapIso E.fixingSubgroupEquiv
    (LinearEquiv.refl ℤ (Additive Lˣ)) (fun _ => rfl) n

variable [FiniteDimensional K L]

/-- Hilbert 90 for the actual fixing-subgroup representation. -/
theorem finiteGaloisUnitsFixingSubgroupH1_subsingleton :
    Subsingleton (groupCohomology
      (Rep.res E.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K L)) 1) := by
  apply (finiteGaloisUnitsRelativeCohomologyIso K L E 1).toLinearEquiv.injective.subsingleton

private def unitsToInvariants :
    Rep.ofAlgebraAutOnUnits K E →ₗ[ℤ]
      (Rep.res E.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K L)).ρ.invariants :=
  ((Units.map E.val.toMonoidHom).toAdditive.toIntLinearMap).codRestrict _ (by
    intro a τ
    apply Units.ext
    exact τ.property ((show Additive Eˣ from a).toMul : E))

variable [IsGalois K L]

private theorem unitsToInvariants_bijective : Function.Bijective (unitsToInvariants K L E) := by
  refine ⟨?_, ?_⟩
  · intro a b h
    exact Units.map_injective E.val.injective (congrArg Subtype.val h)
  · intro a
    have hfix (τ : Gal(L/E)) :
        τ ((show Additive Lˣ from a.val).toMul : L) =
          ((show Additive Lˣ from a.val).toMul : L) :=
      congrArg Units.val (a.property (E.fixingSubgroupEquiv.symm τ))
    obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
      (F := E) (E := L) ((show Additive Lˣ from a.val).toMul : L)).mpr hfix
    have hb0 : b ≠ 0 := by
      intro h
      apply Units.ne_zero (show Additive Lˣ from a.val).toMul
      rw [← hb, h, map_zero]
    refine ⟨Additive.ofMul (Units.mk0 b hb0), ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact hb

/-- The lower-field units are precisely the upper-field units fixed by the
actual relative automorphisms. -/
def finiteGaloisUnitsInvariantsEquiv :
    (Rep.ofAlgebraAutOnUnits K E).V ≃ₗ[ℤ]
      (Rep.res E.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K L)).ρ.invariants :=
  LinearEquiv.ofBijective (unitsToInvariants K L E) (unitsToInvariants_bijective K L E)

variable [Normal K E]

private def restrictionQuotientEquiv :
    Gal(L/K) ⧸ (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker ≃* Gal(E/K) :=
  QuotientGroup.quotientKerEquivOfSurjective (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
    (AlgEquiv.restrictNormalHom_surjective L (F := K) (K₁ := E))

private def unitsToKernelInvariantsEquiv :
    (Rep.ofAlgebraAutOnUnits K E).V ≃ₗ[ℤ]
      ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker).V :=
  (finiteGaloisUnitsInvariantsEquiv K L E).trans
    (LinearEquiv.ofEq _ _ (by rw [E.restrictNormalHom_ker]))

private theorem unitsInvariants_equivariant (g : Gal(E/K)) :
    (unitsToKernelInvariantsEquiv K L E).toLinearMap ∘ₗ
        (Rep.ofAlgebraAutOnUnits K E).ρ g =
      ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker).ρ
          ((restrictionQuotientEquiv K L E).symm g) ∘ₗ
        (unitsToKernelInvariantsEquiv K L E).toLinearMap := by
  obtain ⟨q, rfl⟩ := (restrictionQuotientEquiv K L E).surjective g
  rw [MulEquiv.symm_apply_apply]
  induction q using QuotientGroup.induction_on with
  | H σ =>
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    apply Units.ext
    exact σ.restrictNormal_commutes E ((show Additive Eˣ from a).toMul : E)

private def unitsInvariantsRepHom :
    Rep.res (restrictionQuotientEquiv K L E).toMonoidHom (Rep.ofAlgebraAutOnUnits K E) ⟶
      (Rep.ofAlgebraAutOnUnits K L).quotientToInvariants
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker := by
  apply Rep.ofHom
  refine ⟨(unitsToKernelInvariantsEquiv K L E).toLinearMap, ?_⟩
  intro q
  induction q using QuotientGroup.induction_on with
  | H σ =>
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    apply Units.ext
    exact σ.restrictNormal_commutes E ((show Additive Eˣ from a).toMul : E)

/-- Transport from actual lower-field cohomology to quotient-group cohomology
with fixed unit coefficients, using restriction and the fixed-field equality. -/
def finiteGaloisUnitsQuotientCohomologyIso (n : ℕ) :
    groupCohomology (Rep.ofAlgebraAutOnUnits K E) n ≅
      groupCohomology
        ((Rep.ofAlgebraAutOnUnits K L).quotientToInvariants (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker) n :=
  groupCohomology.mapIso (restrictionQuotientEquiv K L E).symm
    (unitsToKernelInvariantsEquiv K L E) (unitsInvariants_equivariant K L E) n

/-- The fixed-coefficient comparison intertwines quotient inflation with the
actual field-unit inflation, including its coefficient map. -/
theorem finiteGaloisUnitsQuotientCohomologyIso_inflation :
    (finiteGaloisUnitsQuotientCohomologyIso K L E 2).hom ≫
      (groupCohomology.infNatTrans ℤ (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker 2).app
        (Rep.ofAlgebraAutOnUnits K L) = finiteGaloisUnitsH2Inflation K L E := by
  change groupCohomology.map (restrictionQuotientEquiv K L E).toMonoidHom
      (unitsInvariantsRepHom K L E) 2 ≫
    groupCohomology.map (QuotientGroup.mk' (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker)
      (Rep.ofHom ((Rep.ofAlgebraAutOnUnits K L).ρ.quotientToInvariants_lift
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker)) 2 =
    groupCohomology.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
      (finiteGaloisUnitsInflationRepHom K L E) 2
  refine (groupCohomology.map_comp
    (restrictionQuotientEquiv K L E).toMonoidHom
    (QuotientGroup.mk' (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker)
    (unitsInvariantsRepHom K L E)
    (Rep.ofHom ((Rep.ofAlgebraAutOnUnits K L).ρ.quotientToInvariants_lift
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker)) 2).symm.trans ?_
  apply groupCohomology.map_congr
  · ext σ
    rfl
  · apply LinearMap.ext
    intro a
    apply Units.ext
    rfl

/-- Actual restriction to the relative Galois group, with the field units
unchanged. -/
def finiteGaloisUnitsH2Restriction :
    groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits E L) 2 :=
  groupCohomology.map E.fixingSubgroup.subtype
    (𝟙 (Rep.res E.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K L))) 2 ≫
      (finiteGaloisUnitsRelativeCohomologyIso K L E 2).hom

/-- Middle exactness for actual field-unit H² in a finite Galois tower.
Hilbert 90 supplies the subgroup H¹ vanishing; the quotient comparison
identifies the constructed class with lower-field cohomology. -/
theorem finiteGaloisUnitsH2Restriction_ker_le_inflation_range :
    (finiteGaloisUnitsH2Restriction K L E).hom.ker ≤
      (finiteGaloisUnitsH2Inflation K L E).hom.range := by
  have hker : (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker = E.fixingSubgroup :=
    E.restrictNormalHom_ker
  have : Subsingleton (groupCohomology
      (Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker.subtype (Rep.ofAlgebraAutOnUnits K L)) 1) := by
    rw [hker]
    exact finiteGaloisUnitsFixingSubgroupH1_subsingleton K L E
  intro x hx
  have hx' : (groupCohomology.map E.fixingSubgroup.subtype
      (𝟙 (Rep.res E.fixingSubgroup.subtype (Rep.ofAlgebraAutOnUnits K L))) 2).hom x = 0 := by
    apply (finiteGaloisUnitsRelativeCohomologyIso K L E 2).toLinearEquiv.injective
    rw [map_zero]
    exact hx
  have hxKer : (groupCohomology.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker.subtype
      (𝟙 (Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker.subtype
        (Rep.ofAlgebraAutOnUnits K L))) 2).hom x = 0 := by
    rw [hker]
    exact hx'
  obtain ⟨y, hy⟩ := degreeTwo_restriction_ker_le_inflation_range
    (Rep.ofAlgebraAutOnUnits K L) (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker hxKer
  obtain ⟨a, ha⟩ := (finiteGaloisUnitsQuotientCohomologyIso K L E 2).toLinearEquiv.surjective y
  refine ⟨a, ?_⟩
  have he := congrArg (fun (f : groupCohomology (Rep.ofAlgebraAutOnUnits K E) 2 ⟶
      groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) => f.hom a)
    (finiteGaloisUnitsQuotientCohomologyIso_inflation K L E)
  rw [← he]
  change (groupCohomology.infNatTrans ℤ (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker 2).app
    (Rep.ofAlgebraAutOnUnits K L) ((finiteGaloisUnitsQuotientCohomologyIso K L E 2).hom a) = x
  rw [← CategoryTheory.Iso.toLinearEquiv_apply, ha]
  exact hy

end
end ClassFieldTower.Cohomology
