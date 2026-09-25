/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import SawinTotallyRealTowers.UnramifiedProPRelationRank.Global.ClassFormationPGroupH1
import ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
import ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealizationSubextension
import ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerAlgEquivNaturality

set_option autoImplicit false
/-!
# Degree-one vanishing for actual finite p-extensions of number fields

The rational idele-class formation satisfies the cyclic class-field axiom.
The abstract p-group induction therefore gives degree-one vanishing.  Here
we transport that source theorem to the actual relative idele-class
representation of `Gal(L/K)`.

The transport is explicit: relative ideles are sent to absolute ideles,
then to the chosen image of `L` in the rational separable closure.  The
coefficient equivalence is checked against the actual Galois action before
using functoriality of group cohomology.

Instance audit: no global instances are introduced.  The relative class
action is fixed once locally.  The only auxiliary tower setup is the
quotient-restriction lemma (four canonical data instances and one normality
proof); no setup is repeated in the cohomology transport.
-/

open CategoryTheory NumberField
open scoped NumberField TensorProduct

namespace ClassFieldTower.Martinet.Shafarevich

open ClassFieldTower.Cohomology ClassFormation CyclicCohomology
open AlgebraicNumberTheory LocalClassFieldTheory GlobalClassFieldTheory.Reciprocity

noncomputable section

private theorem adeleCongr_refl_apply
    (K : Type) [Field K] [NumberField K]
    (a : NumberField.AdeleRing (𝓞 K) K) :
    adeleCongr (AlgEquiv.refl : K ≃ₐ[ℚ] K) a = a := by
  let e := relativeAdeleBaseChangeRingEquiv (K := ℚ) (L := K)
  have hc (z : RelativeAdeleRing ℚ K) :
      relativeAdeleCongr (K := ℚ) (AlgEquiv.refl : K ≃ₐ[ℚ] K) z = z := by
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    | tmul a x => rw [relativeAdeleCongr_tmul]; rfl
  change e (relativeAdeleCongr (K := ℚ) (AlgEquiv.refl : K ≃ₐ[ℚ] K) (e.symm a)) = a
  rw [hc, e.apply_symm_apply]

variable (K L : Type) [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]

local instance : MulDistribMulAction (L ≃ₐ[K] L) (RelativeIdeleGroup.ClassGroup K L) :=
  RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction K L

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem relativeClassCongr_refl_base_eq_smul
    (sigma : L ≃ₐ[K] L) (c : RelativeIdeleGroup.ClassGroup K L) :
    relativeIdeleClassCongrOfAlgEquiv
      (AlgEquiv.refl : K ≃ₐ[ℚ] K) (sigma.restrictScalars ℚ)
      (fun x => sigma.commutes x) c = sigma • c := by
  let tau : L ≃ₐ[ℚ] L := sigma.restrictScalars ℚ
  have h : ∀ x : K, tau (algebraMap K L x) = algebraMap K L
      ((AlgEquiv.refl : K ≃ₐ[ℚ] K) x) := fun x => sigma.commutes x
  change relativeIdeleClassCongrOfAlgEquiv (AlgEquiv.refl : K ≃ₐ[ℚ] K) tau h c = _
  refine QuotientGroup.induction_on c ?_
  intro a
  change relativeIdeleClassCongrOfAlgEquiv (AlgEquiv.refl : K ≃ₐ[ℚ] K) tau h
      (QuotientGroup.mk' (RelativeIdeleGroup.principalSubgroup K L) a) =
    sigma • (QuotientGroup.mk' (RelativeIdeleGroup.principalSubgroup K L) a)
  rw [relativeIdeleClassCongrOfAlgEquiv_mk, RelativeIdeleGroup.Cohomology.ideleClass_smul_mk]
  congr 1
  apply Units.ext
  change relativeAdeleCongrOfAlgEquiv
    (AlgEquiv.refl : K ≃ₐ[ℚ] K) tau h a =
      RelativeIdeleGroup.conjugation K L sigma a
  induction (a : RelativeAdeleRing K L) using TensorProduct.inductionOn with
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  | tmul b x =>
      rw [relativeAdeleCongrOfAlgEquiv_tmul
        (AlgEquiv.refl : K ≃ₐ[ℚ] K) tau h b x,
        RelativeIdeleGroup.conjugation_tmul K L sigma b x,
        adeleCongr_refl_apply K b]
      exact congrArg (fun y : L => b ⊗ₜ[K] y)
        (AlgEquiv.restrictScalars_apply (R := ℚ) sigma x)

omit [IsGalois K L] in
/-- Relative-to-absolute idele-class base change intertwines the Galois action. -/
theorem relativeIdeleClassBaseChange_smul
    (sigma : L ≃ₐ[K] L) (c : RelativeIdeleGroup.ClassGroup K L) :
    relativeIdeleClassBaseChangeMulEquiv (K := K) (L := L) (sigma • c) =
      ideleClassCongr (sigma.restrictScalars ℚ)
        (relativeIdeleClassBaseChangeMulEquiv (K := K) (L := L) c) := by
  rw [← relativeClassCongr_refl_base_eq_smul K L sigma c]
  exact relativeIdeleClassBaseChangeMulEquiv_congrOfAlgEquiv
    (AlgEquiv.refl : K ≃ₐ[ℚ] K) (sigma.restrictScalars ℚ)
    (fun x => sigma.commutes x) c

/-- Actual relative idele classes are the fixed coefficients in the rational
idele-class formation at the chosen copy of the top field. -/
def relativeIdeleClassEquivRationalFixed :
    Additive (RelativeIdeleGroup.ClassGroup K L) ≃+
      KummerTheory.ambientFixedAddSubgroup rationalIdeleClassRepresentation
        (numberFieldTowerTopSubgroup L) := by
  let E := numberFieldInRationalSeparableClosure L
  let e : L ≃ₐ[ℚ] E := (numberFieldSeparableClosureEmbedding L).equivFieldRange
  exact (relativeIdeleClassBaseChangeMulEquiv (K := K) (L := L)).toAdditive.trans
    ((ideleClassCongr e).toAdditive.trans (rationalIdeleClassEquivFixed E))

private theorem towerQuotientGalois_mk_apply
    (sigma : (numberFieldTowerBaseSubgroup K L).toSubgroup) (x : L) :
    numberFieldSeparableClosureEmbedding L
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L
          ((numberFieldTowerFiniteGaloisSubextension K L).extensionQuotientMk sigma) x) =
      sigma.1 (numberFieldSeparableClosureEmbedding L x) := by
  let _ : Algebra K (SeparableClosure ℚ) := numberFieldTowerSeparableClosureBaseAlgebra K L
  let _ : Algebra L (SeparableClosure ℚ) := numberFieldTowerSeparableClosureTopAlgebra L
  let _ : IsScalarTower K L (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureScalarTower K L
  let _ : IsScalarTower ℚ K (SeparableClosure ℚ) :=
    numberFieldTowerSeparableClosureBaseScalarTower K L
  let j := numberFieldSeparableClosureEmbedding L
  let e := numberFieldTowerSeparableClosureEquiv K L
  let _ := numberFieldTowerExtensionSubgroup_normal K L
  convert ambientEmbeddedExtensionQuotientEquivGaloisGroup_mk_apply
    ℚ K L j e sigma x using 1; rfl

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem ideleClassCongr_conjugate
    {E : Type} [Field E] [NumberField E]
    (e : L ≃ₐ[ℚ] E) (tau : L ≃ₐ[ℚ] L) (c : IdeleClassGroup L) :
    ideleClassCongr ((e.symm.trans tau).trans e) (ideleClassCongr e c) =
      ideleClassCongr e (ideleClassCongr tau c) := by
  rw [ideleClassCongr_trans, ideleClassCongr_trans]
  have heq : e.trans ((e.symm.trans tau).trans e) = tau.trans e := by
    ext x
    simp only [AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply]
  rw [heq]

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem rationalFixed_conjugate_action
    (sigma : Gal(SeparableClosure ℚ / ℚ)) (tau : L ≃ₐ[K] L)
    (h : ∀ y : L, numberFieldSeparableClosureEmbedding L (tau y) =
      sigma (numberFieldSeparableClosureEmbedding L y))
    (c : IdeleClassGroup L) :
    let E := numberFieldInRationalSeparableClosure L
    let e : L ≃ₐ[ℚ] E := (numberFieldSeparableClosureEmbedding L).equivFieldRange
    rationalIdeleClassRepresentation.ρ sigma
        (rationalIdeleClassEquivFixed E (Additive.ofMul (ideleClassCongr e c))).1 =
      (rationalIdeleClassEquivFixed E
        (Additive.ofMul (ideleClassCongr e
          (ideleClassCongr (tau.restrictScalars ℚ) c)))).1 := by
  dsimp only
  let E := numberFieldInRationalSeparableClosure L
  let e : L ≃ₐ[ℚ] E := (numberFieldSeparableClosureEmbedding L).equivFieldRange
  let eta : E ≃ₐ[ℚ] E := (e.symm.trans (tau.restrictScalars ℚ)).trans e
  have hse : ∀ x : E, (eta x).1 = sigma x.1 := by
    intro x
    obtain ⟨y, rfl⟩ := e.surjective x
    change numberFieldSeparableClosureEmbedding L (tau (e.symm (e y))) =
      sigma (numberFieldSeparableClosureEmbedding L y)
    rw [e.symm_apply_apply]
    exact h y
  have hn := rationalIdeleClassEquivFixed_ambientAlgEquiv sigma eta hse
    (ideleClassCongr e c)
  exact hn.trans (congrArg (fun d : IdeleClassGroup E =>
    (rationalIdeleClassEquivFixed E (Additive.ofMul d)).1)
      (ideleClassCongr_conjugate L e (tau.restrictScalars ℚ) c))

omit [IsGalois K L] in
private theorem relativeIdeleClassEquivRationalFixed_action_core
    (sigma : Gal(SeparableClosure ℚ / ℚ)) (tau : L ≃ₐ[K] L)
    (h : ∀ y : L, numberFieldSeparableClosureEmbedding L (tau y) =
      sigma (numberFieldSeparableClosureEmbedding L y))
    (c : RelativeIdeleGroup.ClassGroup K L) :
    rationalIdeleClassRepresentation.ρ sigma
        (relativeIdeleClassEquivRationalFixed K L (Additive.ofMul c)).1 =
      (relativeIdeleClassEquivRationalFixed K L
        (Additive.ofMul (tau • c))).1 := by
  let E := numberFieldInRationalSeparableClosure L
  let e : L ≃ₐ[ℚ] E := (numberFieldSeparableClosureEmbedding L).equivFieldRange
  let cL := relativeIdeleClassBaseChangeMulEquiv (K := K) (L := L) c
  change rationalIdeleClassRepresentation.ρ sigma
      (rationalIdeleClassEquivFixed E (Additive.ofMul (ideleClassCongr e cL))).1 =
    (rationalIdeleClassEquivFixed E
      (Additive.ofMul (ideleClassCongr e
        (relativeIdeleClassBaseChangeMulEquiv (K := K) (L := L) (tau • c))))).1
  exact (rationalFixed_conjugate_action K L sigma tau h cL).trans
    (congrArg (fun d : IdeleClassGroup L =>
      (rationalIdeleClassEquivFixed E (Additive.ofMul (ideleClassCongr e d))).1)
      (relativeIdeleClassBaseChange_smul K L tau c).symm)

/-- The fixed-coefficient equivalence respects restriction from the actual
ambient Galois group to the finite extension quotient. -/
theorem relativeIdeleClassEquivRationalFixed_action
    (sigma : (numberFieldTowerBaseSubgroup K L).toSubgroup)
    (c : RelativeIdeleGroup.ClassGroup K L) :
    rationalIdeleClassRepresentation.ρ sigma.1
        (relativeIdeleClassEquivRationalFixed K L (Additive.ofMul c)).1 =
      (relativeIdeleClassEquivRationalFixed K L
        (Additive.ofMul
          (numberFieldTowerExtensionQuotientEquivGaloisGroup K L
            ((numberFieldTowerFiniteGaloisSubextension K L).extensionQuotientMk sigma) • c))).1 :=
  relativeIdeleClassEquivRationalFixed_action_core K L sigma.1
    (numberFieldTowerExtensionQuotientEquivGaloisGroup K L
      ((numberFieldTowerFiniteGaloisSubextension K L).extensionQuotientMk sigma))
    (towerQuotientGalois_mk_apply K L sigma) c

/-- Coefficient equivalence with the representation descended to the finite
abstract extension quotient. -/
def relativeIdeleClassFixedRepresentationEquiv :
    Additive (RelativeIdeleGroup.ClassGroup K L) ≃+
      (extensionFixedRepresentation rationalIdeleClassRepresentation
        (numberFieldTowerFiniteAbstractField K L).field
        (numberFieldTowerFiniteGaloisSubextension K L).field
        (numberFieldTowerFiniteGaloisSubextension K L).below
        (numberFieldTowerFiniteGaloisSubextension K L).normal).V :=
  (relativeIdeleClassEquivRationalFixed K L).trans
    (extensionFixedRepresentationEquiv rationalIdeleClassRepresentation
      (numberFieldTowerFiniteAbstractField K L).field
      (numberFieldTowerFiniteGaloisSubextension K L).field
      (numberFieldTowerFiniteGaloisSubextension K L).below
      (numberFieldTowerFiniteGaloisSubextension K L).normal).symm

/-- The coefficient equivalence is equivariant for the concrete identification
of the abstract extension quotient with `Gal(L/K)`. -/
theorem relativeIdeleClassFixedRepresentationEquiv_action
    (q : (numberFieldTowerFiniteGaloisSubextension K L).extensionQuotient)
    (c : Additive (RelativeIdeleGroup.ClassGroup K L)) :
    (extensionFixedRepresentation rationalIdeleClassRepresentation
      (numberFieldTowerFiniteAbstractField K L).field
      (numberFieldTowerFiniteGaloisSubextension K L).field
      (numberFieldTowerFiniteGaloisSubextension K L).below
      (numberFieldTowerFiniteGaloisSubextension K L).normal).ρ q
        (relativeIdeleClassFixedRepresentationEquiv K L c) =
      relativeIdeleClassFixedRepresentationEquiv K L
        ((Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
          (RelativeIdeleGroup.ClassGroup K L)).ρ
          (numberFieldTowerExtensionQuotientEquivGaloisGroup K L q) c) := by
  refine QuotientGroup.induction_on q (fun sigma => ?_)
  apply Subtype.ext
  exact relativeIdeleClassEquivRationalFixed_action K L sigma c.toMul

/-- The actual relative idele-class representation has vanishing `H¹` for
every finite Galois `p`-extension of number fields.  The only arithmetic input
is the existing rational idele-class class-field axiom. -/
theorem ideleClassH1_subsingleton_of_isPGroup
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p (L ≃ₐ[K] L)) :
    Subsingleton (groupCohomology.H1
      (Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
        (RelativeIdeleGroup.ClassGroup K L))) := by
  let KB := numberFieldTowerFiniteAbstractField K L
  let LB := numberFieldTowerFiniteGaloisSubextension K L
  let B := extensionFixedRepresentation rationalIdeleClassRepresentation
    KB.field LB.field LB.below LB.normal
  let C := Rep.ofMulDistribMulAction (L ≃ₐ[K] L)
    (RelativeIdeleGroup.ClassGroup K L)
  let eG := numberFieldTowerExtensionQuotientEquivGaloisGroup K L
  let eC : B.V ≃ₗ[ℤ] C.V :=
    (relativeIdeleClassFixedRepresentationEquiv K L).symm.toIntLinearEquiv
  have he (q : LB.extensionQuotient) :
      eC.toLinearMap ∘ₗ B.ρ q = C.ρ (eG q) ∘ₗ eC.toLinearMap := by
    ext x
    apply (relativeIdeleClassFixedRepresentationEquiv K L).injective
    change (relativeIdeleClassFixedRepresentationEquiv K L)
        ((relativeIdeleClassFixedRepresentationEquiv K L).symm (B.ρ q x)) =
      relativeIdeleClassFixedRepresentationEquiv K L
        (C.ρ (eG q) ((relativeIdeleClassFixedRepresentationEquiv K L).symm x))
    rw [AddEquiv.apply_symm_apply,
      ← relativeIdeleClassFixedRepresentationEquiv_action K L,
      AddEquiv.apply_symm_apply]
  let eH := groupCohomology.mapIso (A := C) (B := B) eG eC he 1
  have hB : Subsingleton (groupCohomology.H1 B) :=
    pClassFormationH1_subsingleton rationalIdeleClassRepresentation
      rationalIdeleClassRepresentation_satisfiesClassFieldAxiom
      KB LB (hP.of_equiv eG.symm)
  refine ⟨fun x y => eH.symm.toLinearEquiv.injective ?_⟩
  exact @Subsingleton.elim _ hB _ _

end

end ClassFieldTower.Martinet.Shafarevich
