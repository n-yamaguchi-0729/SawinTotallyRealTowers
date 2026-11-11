/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.GaloisCohomology.GroupTheory.CoefficientRingEquivalence
public import Nyll.GaloisCohomology.Cyclic.IntegralCoefficientCohomology
public import Nyll.GaloisCohomology.Kummer.QuotientTwoCocycle
public import Nyll.GaloisCohomology.ProP.FiniteCyclicH2CoefficientNorm
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.FieldTheory.Normal.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Field-unit cohomology in the field's universe

Restriction of scalars along the actual ring equivalence from lifted integers
preserves the field units and their Galois action. Hilbert 90, fixed-field descent,
and the periodic norm calculation therefore apply to fields in every universe.
The coefficient category follows the upper field; the base field has an independent
universe because it changes only the linearity condition on automorphisms.
The existing integer-coefficient APIs retain their original owners.
-/

@[expose] public section

universe u v
open CategoryTheory

namespace ClassFieldTower.Cohomology

noncomputable section

/-- The actual field-unit action, with integers lifted to the field's universe. -/
def liftedGaloisUnitsRep (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L] :
    Rep.{u} (ULift.{u} ℤ) Gal(L/K) :=
  (IntegralGroupCohomology.coefficientFunctor Gal(L/K)).obj (Rep.ofAlgebraAutOnUnits K L)

/-- Hilbert 90 for the transported representation, proved from the actual
multiplicative cocycle and its field-unit primitive. -/
theorem liftedGaloisUnitsH1_subsingleton
    (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
    Subsingleton (groupCohomology (liftedGaloisUnitsRep K L) 1) := by
  have hz (x : groupCohomology (liftedGaloisUnitsRep K L) 1) : x = 0 := by
    refine groupCohomology.H1_induction_on x ?_
    intro c
    apply (groupCohomology.H1π_eq_zero_iff c).mpr
    have hc : groupCohomology.IsMulCocycle₁
        (fun σ : Gal(L/K) => (show Additive Lˣ from c σ).toMul) := by
      intro σ τ
      exact congrArg (fun z : Additive Lˣ => z.toMul)
        ((groupCohomology.mem_cocycles₁_iff c).mp c.property σ τ)
    obtain ⟨b, hb⟩ :=
      groupCohomology.isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units
        (fun σ : Gal(L/K) => (show Additive Lˣ from c σ).toMul) hc
    refine ⟨Additive.ofMul b, ?_⟩
    funext σ
    apply Additive.toMul.injective
    exact hb σ
  exact ⟨fun x y => (hz x).trans (hz y).symm⟩

/-- Inclusion of intermediate-field units with the transported integer scalar action. -/
def liftedUnitsInclusionLinear
    (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) :
    liftedGaloisUnitsRep K E →ₗ[ULift.{u} ℤ] liftedGaloisUnitsRep K L :=
  (ModuleCat.coefficientRingAddHom
    (ULift.ringEquiv : ULift.{u} ℤ ≃+* ℤ)
    (M := ModuleCat.of ℤ (Additive Eˣ))
    (N := ModuleCat.of ℤ (Additive Lˣ))
    (Units.map E.val.toMonoidHom).toAdditive).hom

/-- Inclusion of actual intermediate-field units is equivariant for restriction. -/
def liftedFiniteGaloisUnitsInflationRepHom
    (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [Normal K E] :
    Rep.res (AlgEquiv.restrictNormalHom E) (liftedGaloisUnitsRep K E) ⟶
      liftedGaloisUnitsRep K L := by
  apply Rep.ofHom
  refine ⟨liftedUnitsInclusionLinear K L E, ?_⟩
  intro σ
  apply LinearMap.ext
  intro a
  apply Units.ext
  exact σ.restrictNormal_commutes E ((show Additive Eˣ from a).toMul : E)

/-- Inflation uses actual restriction of automorphisms and inclusion of units. -/
def liftedFiniteGaloisUnitsH2Inflation
    (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [Normal K E] :
    groupCohomology (liftedGaloisUnitsRep K E) 2 ⟶
      groupCohomology (liftedGaloisUnitsRep K L) 2 :=
  groupCohomology.map (AlgEquiv.restrictNormalHom E)
    (liftedFiniteGaloisUnitsInflationRepHom K L E) 2

variable (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
variable (E : IntermediateField K L)

/-- Restriction to the fixing subgroup uses the actual relative automorphism
 action on the same field units. -/
def liftedFiniteGaloisUnitsRelativeCohomologyIso (n : ℕ) :
    groupCohomology (Rep.res E.fixingSubgroup.subtype (liftedGaloisUnitsRep K L)) n ≅
      groupCohomology (liftedGaloisUnitsRep E L) n :=
  groupCohomology.mapIso E.fixingSubgroupEquiv
    (LinearEquiv.refl (ULift.{u} ℤ) (liftedGaloisUnitsRep K L)) (fun _ => rfl) n

variable [FiniteDimensional K L]

/-- Hilbert 90 for the actual fixing-subgroup representation. -/
theorem liftedFiniteGaloisUnitsFixingSubgroupH1_subsingleton :
    Subsingleton (groupCohomology
      (Rep.res E.fixingSubgroup.subtype (liftedGaloisUnitsRep K L)) 1) := by
  have : Subsingleton (groupCohomology (liftedGaloisUnitsRep E L) 1) :=
    liftedGaloisUnitsH1_subsingleton E L
  exact (liftedFiniteGaloisUnitsRelativeCohomologyIso K L E 1).toLinearEquiv.injective.subsingleton

/-- Intermediate-field units embedded into the units fixed by relative automorphisms. -/
def liftedUnitsToInvariants :
    liftedGaloisUnitsRep K E →ₗ[ULift.{u} ℤ]
      (Rep.res E.fixingSubgroup.subtype (liftedGaloisUnitsRep K L)).ρ.invariants :=
  (liftedUnitsInclusionLinear K L E).codRestrict _ (by
    intro a τ
    apply Units.ext
    exact τ.property ((show Additive Eˣ from a).toMul : E))

variable [IsGalois K L]

/-- Fixed upper-field units descend uniquely to the intermediate field, with lifted scalars. -/
theorem liftedUnitsToInvariants_bijective : Function.Bijective (liftedUnitsToInvariants K L E) := by
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
def liftedFiniteGaloisUnitsInvariantsEquiv :
    (liftedGaloisUnitsRep K E).V ≃ₗ[ULift.{u} ℤ]
      (Rep.res E.fixingSubgroup.subtype (liftedGaloisUnitsRep K L)).ρ.invariants :=
  LinearEquiv.ofBijective (liftedUnitsToInvariants K L E) (liftedUnitsToInvariants_bijective K L E)

variable [Normal K E]

/-- The actual restriction quotient identified with the lower-field Galois group. -/
def liftedRestrictionQuotientEquiv :
    Gal(L/K) ⧸ (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker ≃* Gal(E/K) :=
  QuotientGroup.quotientKerEquivOfSurjective (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
    (AlgEquiv.restrictNormalHom_surjective L (F := K) (K₁ := E))

/-- Lower-field units identified with units fixed by the kernel of restriction. -/
def liftedUnitsToKernelInvariantsEquiv :
    (liftedGaloisUnitsRep K E).V ≃ₗ[ULift.{u} ℤ]
      ((liftedGaloisUnitsRep K L).quotientToInvariants
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker).V :=
  (liftedFiniteGaloisUnitsInvariantsEquiv K L E).trans
    (LinearEquiv.ofEq _ _ (by rw [E.restrictNormalHom_ker]))

/-- The lifted invariant-unit equivalence respects the original quotient Galois action. -/
theorem liftedUnitsInvariants_equivariant (g : Gal(E/K)) :
    (liftedUnitsToKernelInvariantsEquiv K L E).toLinearMap ∘ₗ
        (liftedGaloisUnitsRep K E).ρ g =
      ((liftedGaloisUnitsRep K L).quotientToInvariants
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker).ρ
          ((liftedRestrictionQuotientEquiv K L E).symm g) ∘ₗ
        (liftedUnitsToKernelInvariantsEquiv K L E).toLinearMap := by
  obtain ⟨q, rfl⟩ := (liftedRestrictionQuotientEquiv K L E).surjective g
  rw [MulEquiv.symm_apply_apply]
  induction q using QuotientGroup.induction_on with
  | H σ =>
    apply LinearMap.ext
    intro a
    apply Subtype.ext
    apply Units.ext
    exact σ.restrictNormal_commutes E ((show Additive Eˣ from a).toMul : E)

private def liftedUnitsInvariantsRepHom :
    Rep.res (liftedRestrictionQuotientEquiv K L E).toMonoidHom (liftedGaloisUnitsRep K E) ⟶
      (liftedGaloisUnitsRep K L).quotientToInvariants
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker := by
  apply Rep.ofHom
  refine ⟨(liftedUnitsToKernelInvariantsEquiv K L E).toLinearMap, ?_⟩
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
def liftedFiniteGaloisUnitsQuotientCohomologyIso (n : ℕ) :
    groupCohomology (liftedGaloisUnitsRep K E) n ≅
      groupCohomology
        ((liftedGaloisUnitsRep K L).quotientToInvariants
          (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker) n :=
  groupCohomology.mapIso (liftedRestrictionQuotientEquiv K L E).symm
    (liftedUnitsToKernelInvariantsEquiv K L E) (liftedUnitsInvariants_equivariant K L E) n

/-- The fixed-coefficient comparison intertwines quotient inflation with the
actual field-unit inflation, including its coefficient map. -/
theorem liftedFiniteGaloisUnitsQuotientCohomologyIso_inflation :
    (liftedFiniteGaloisUnitsQuotientCohomologyIso K L E 2).hom ≫
      (groupCohomology.infNatTrans (ULift.{u} ℤ)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker 2).app
        (liftedGaloisUnitsRep K L) = liftedFiniteGaloisUnitsH2Inflation K L E := by
  change groupCohomology.map (liftedRestrictionQuotientEquiv K L E).toMonoidHom
      (liftedUnitsInvariantsRepHom K L E) 2 ≫
    groupCohomology.map (QuotientGroup.mk' (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker)
      (Rep.ofHom ((liftedGaloisUnitsRep K L).ρ.quotientToInvariants_lift
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker)) 2 =
    groupCohomology.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E)
      (liftedFiniteGaloisUnitsInflationRepHom K L E) 2
  refine (groupCohomology.map_comp
    (liftedRestrictionQuotientEquiv K L E).toMonoidHom
    (QuotientGroup.mk' (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker)
    (liftedUnitsInvariantsRepHom K L E)
    (Rep.ofHom ((liftedGaloisUnitsRep K L).ρ.quotientToInvariants_lift
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
def liftedFiniteGaloisUnitsH2Restriction :
    groupCohomology (liftedGaloisUnitsRep K L) 2 ⟶
      groupCohomology (liftedGaloisUnitsRep E L) 2 :=
  groupCohomology.map E.fixingSubgroup.subtype
    (𝟙 (Rep.res E.fixingSubgroup.subtype (liftedGaloisUnitsRep K L))) 2 ≫
      (liftedFiniteGaloisUnitsRelativeCohomologyIso K L E 2).hom

/-- Middle exactness for actual field-unit H² in a finite Galois tower.
Hilbert 90 supplies the subgroup H¹ vanishing; the quotient comparison
identifies the constructed class with lower-field cohomology. -/
theorem liftedFiniteGaloisUnitsH2Restriction_ker_le_inflation_range :
    (liftedFiniteGaloisUnitsH2Restriction K L E).hom.ker ≤
      (liftedFiniteGaloisUnitsH2Inflation K L E).hom.range := by
  have hker : (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker = E.fixingSubgroup :=
    E.restrictNormalHom_ker
  have : Subsingleton (groupCohomology
      (Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker.subtype
        (liftedGaloisUnitsRep K L)) 1) := by
    rw [hker]
    exact liftedFiniteGaloisUnitsFixingSubgroupH1_subsingleton K L E
  intro x hx
  have hx' : (groupCohomology.map E.fixingSubgroup.subtype
      (𝟙 (Rep.res E.fixingSubgroup.subtype (liftedGaloisUnitsRep K L))) 2).hom x = 0 := by
    apply (liftedFiniteGaloisUnitsRelativeCohomologyIso K L E 2).toLinearEquiv.injective
    rw [map_zero]
    exact hx
  have hxKer : (groupCohomology.map (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker.subtype
      (𝟙 (Rep.res (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker.subtype
        (liftedGaloisUnitsRep K L))) 2).hom x = 0 := by
    rw [hker]
    exact hx'
  obtain ⟨y, hy⟩ := degreeTwo_restriction_ker_le_inflation_range
    (liftedGaloisUnitsRep K L) (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker hxKer
  obtain ⟨a, ha⟩ :=
    (liftedFiniteGaloisUnitsQuotientCohomologyIso K L E 2).toLinearEquiv.surjective y
  refine ⟨a, ?_⟩
  have he := congrArg (fun (f : groupCohomology (liftedGaloisUnitsRep K E) 2 ⟶
      groupCohomology (liftedGaloisUnitsRep K L) 2) => f.hom a)
    (liftedFiniteGaloisUnitsQuotientCohomologyIso_inflation K L E)
  rw [← he]
  change (groupCohomology.infNatTrans (ULift.{u} ℤ)
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := L) E).ker 2).app
    (liftedGaloisUnitsRep K L) ((liftedFiniteGaloisUnitsQuotientCohomologyIso K L E 2).hom a) = x
  rw [← CategoryTheory.Iso.toLinearEquiv_apply, ha]
  exact hy

end
end ClassFieldTower.Cohomology

namespace ClassFieldTower.Cohomology

/-- The representation norm is the actual field norm, on the unchanged units. -/
theorem liftedGaloisUnits_norm_eq
    (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (x : Lˣ) :
    ((Additive.toMul ((liftedGaloisUnitsRep K L).norm.asHom.hom
      (Additive.ofMul x)) : Lˣ) : L) = algebraMap K L (Algebra.norm K (x : L)) := by
  erw [Rep.norm_apply, Representation.norm, LinearMap.sum_apply]
  change ((Additive.toMul (∑ σ : Gal(L/K), Additive.ofMul (Units.map σ x)) : Lˣ) : L) = _
  rw [_root_.toMul_sum, Units.coe_prod]
  exact (Algebra.norm_eq_prod_automorphisms (K := K) (x : L)).symm

/-- Surjectivity of the field norm kills native degree-two unit cohomology.
The invariant coefficient of a periodic representative descends to the base;
its norm preimage is then an actual periodic coboundary. -/
theorem liftedCyclicUnitsH2_eq_zero_of_norm_surjective
    (K : Type v) (L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [IsCyclic Gal(L/K)]
    (hN : Function.Surjective (Algebra.norm K : L →* K))
    (c : groupCohomology (liftedGaloisUnitsRep K L) 2) : c = 0 := by
  classical
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Gal(L/K))
  obtain ⟨a, ha⟩ := finiteCyclicGroupH2_piEven_surjective
    (liftedGaloisUnitsRep K L) g hg c
  have hag : (liftedGaloisUnitsRep K L).ρ g a.val = a.val := by
    have hzero := a.property
    change (liftedGaloisUnitsRep K L).ρ g a.val - a.val = 0 at hzero
    exact sub_eq_zero.mp hzero
  have hfixed : ∀ σ : Gal(L/K), (liftedGaloisUnitsRep K L).ρ σ a.val = a.val :=
    (Representation.mem_invariants_iff_of_forall_mem_zpowers
      (liftedGaloisUnitsRep K L).ρ g hg a.val).mpr hag
  obtain ⟨b, hb⟩ := (IsGalois.mem_range_algebraMap_iff_fixed
    (F := K) (E := L) ((show Additive Lˣ from a.val).toMul : L)).mpr
      (fun σ => congrArg Units.val (hfixed σ))
  obtain ⟨v, hv⟩ := hN b
  have hv0 : v ≠ 0 := by
    intro hzero
    have hb0 : b = 0 := by
      rw [hzero, Algebra.norm_zero] at hv
      exact hv.symm
    apply Units.ne_zero (show Additive Lˣ from a.val).toMul
    rw [← hb, hb0, map_zero]
  rw [← ha]
  apply (Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff
    (liftedGaloisUnitsRep K L) g hg 2 (by decide) a).mpr
  refine ⟨Additive.ofMul (Units.mk0 v hv0), ?_⟩
  apply Units.ext
  exact (liftedGaloisUnits_norm_eq K L (Units.mk0 v hv0)).trans
    ((congrArg (algebraMap K L) hv).trans hb)

end ClassFieldTower.Cohomology
