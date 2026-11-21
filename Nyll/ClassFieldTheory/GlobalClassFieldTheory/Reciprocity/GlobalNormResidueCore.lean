/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.GlobalNormResidueCommon
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.CyclotomicIdeleClassValuation
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteGaloisRealization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.NumberFieldArtinTransport
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassFormation
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Main
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.MaximalUnramifiedReciprocity
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.FiniteGaloisSubextension
public import Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.MaximalUnramifiedSymbol
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore
public import Nyll.GaloisCohomology.Cyclic.NormKernelVanishing

/-!
# The global norm-residue symbol for finite Galois extensions

For an arbitrary finite Galois extension of number fields, the global
norm-residue quotient is the abelianization of the genuine Galois group:

`C_K / N_{L/K} C_L ≃ Gal(L / K)ᵃᵇ`.

The abelian specialization in `GlobalNormResidue` identifies this target
further with `Gal(L / K)`.  This file retains the abelianization and therefore
states global reciprocity at its full finite-Galois generality.
-/



@[expose] public section

open scoped IsMulCommutative NumberField
open NumberField

noncomputable section

universe u v

namespace GlobalClassFieldTheory
namespace Reciprocity

open ClassFormation
open KummerTheory

variable
    (K : Type u) (L : Type v) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]


/-- The abelianization of the compatible abstract extension quotient is the
abelianization of the actual Galois group. -/
noncomputable def
    numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization :
    Additive
        (Group.Abelianization
          (ClassFormation.FiniteGaloisSubextension.extensionQuotient
            (numberFieldTowerFiniteGaloisSubextension K L))) ≃+
      Additive (Group.Abelianization (Gal(L / K))) :=
  MulEquiv.toAdditive
    (MulEquiv.abelianizationCongr
      (numberFieldTowerExtensionQuotientEquivGaloisGroup K L))

private theorem numberFieldTowerAbelianizationCongr_of
    (q :
      ClassFormation.FiniteGaloisSubextension.extensionQuotient
        (numberFieldTowerFiniteGaloisSubextension K L)) :
    MulEquiv.abelianizationCongr
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L)
        (Group.Abelianization.of q) =
      Group.Abelianization.of
        (numberFieldTowerExtensionQuotientEquivGaloisGroup K L q) :=
  Group.abelianizationCongr_of
    (numberFieldTowerExtensionQuotientEquivGaloisGroup K L) q

/-- The comparison on abelianizations sends the class of an abstract
automorphism to the class of its actual restriction to `L`. -/
@[simp]
theorem
    numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization_of
    (q :
      ClassFormation.FiniteGaloisSubextension.extensionQuotient
        (numberFieldTowerFiniteGaloisSubextension K L)) :
    numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization
        K L (Additive.ofMul (Group.Abelianization.of q)) =
      Additive.ofMul
        (Group.Abelianization.of
          (numberFieldTowerExtensionQuotientEquivGaloisGroup K L q)) := by
  exact
    congrArg Additive.ofMul
      (numberFieldTowerAbelianizationCongr_of K L q)

/-- The abstract norm-residue symbol followed by the concrete Galois
comparison.  This declaration boundary keeps the dependent quotient indices
and their instance packages from being reconstructed at each evaluation. -/
noncomputable def
    numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv :
    FiniteNormQuotient (ideleClassRepresentation ℚ)
          (numberFieldTowerBaseSubgroup K L)
          (numberFieldTowerTopSubgroup L)
          (numberFieldTowerTopSubgroup_le_baseSubgroup K L) ≃+
      Additive (Group.Abelianization (Gal(L / K))) := by
  let _ : Finite _ :=
    (numberFieldTowerReciprocityFiniteAbstractField K L).finite
  let _ :
      (CyclicCohomology.extensionSubgroup
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)).Normal :=
    numberFieldTowerExtensionSubgroup_normal K L
  let _ : Finite _ :=
    (numberFieldTowerFiniteGaloisSubextension K L).finite
  letI : AddCommGroup
      (FiniteNormQuotient (ideleClassRepresentation ℚ)
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :=
    finiteNormQuotientAddCommGroup (ideleClassRepresentation ℚ)
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
  exact
    @AddEquiv.trans
      (FiniteNormQuotient (ideleClassRepresentation ℚ)
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L))
      (Additive
        (Group.Abelianization
          (ClassFormation.FiniteGaloisSubextension.extensionQuotient
            (numberFieldTowerFiniteGaloisSubextension K L))))
      (Additive (Group.Abelianization (Gal(L / K))))
      inferInstance inferInstance inferInstance
      ((numberFieldCyclotomicDegreeData ℚ).normResidueSymbol
        (ideleClassRepresentation ℚ)
        (numberFieldCyclotomicIdeleClassValuationData ℚ)
        (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ)
        (numberFieldTowerReciprocityFiniteAbstractField K L)
        (numberFieldTowerFiniteGaloisSubextension K L))
      (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization
        K L)

/-- The actual global norm-residue equivalence for a finite Galois
number-field extension:

`C_K / N_{L/K} C_L ≃ Gal(L / K)ᵃᵇ`. -/
noncomputable def globalNormResidueAbelianizationEquiv :
    Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) ≃+
      Additive (Group.Abelianization (Gal(L / K))) :=
  MulEquiv.toAdditive (standardNumberFieldNormResidueEquivOfEmbedding K L
    (AlgebraicNumberTheory.separableEmbeddingIntoSeparableClosure K L))

/-- Evaluation of the common abstract norm-residue comparison. -/
theorem
    numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv_apply
    (x :
      FiniteNormQuotient (ideleClassRepresentation ℚ)
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :
    let :=
      (numberFieldTowerReciprocityFiniteAbstractField K L).finite
    let :=
      numberFieldTowerExtensionSubgroup_normal K L
    let :=
      (numberFieldTowerFiniteGaloisSubextension K L).finite
    numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv K L x =
      numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization
        K L
        (rationalCyclotomicDegreeData.normResidueSymbol
          (ideleClassRepresentation ℚ)
          rationalCyclotomicIdeleClassValuationData
          (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ)
          (numberFieldTowerReciprocityFiniteAbstractField K L)
          (numberFieldTowerFiniteGaloisSubextension K L) x) := by
  intro hBaseFinite hExtensionNormal hRelativeFinite
  simp only [numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv,
    numberFieldCyclotomicNormResidueSymbol_rat]
  rfl

/-- Transporting a finite norm class cancels the ordinary quotient comparison. -/
theorem globalNormResidueAbelianizationEquiv_transport_apply
    (x :
      FiniteNormQuotient (ideleClassRepresentation ℚ)
        (numberFieldTowerBaseSubgroup K L)
        (numberFieldTowerTopSubgroup L)
        (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :
    globalNormResidueAbelianizationEquiv K L
        (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
          K L x) =
      numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv K L x := by
  obtain ⟨a, rfl⟩ := finiteNormClass_surjective (ideleClassRepresentation ℚ)
    (numberFieldTowerBaseSubgroup K L) (numberFieldTowerTopSubgroup L)
    (numberFieldTowerTopSubgroup_le_baseSubgroup K L) x
  obtain ⟨c, rfl⟩ := (numberFieldTowerIdeleClassEquivAmbientFixed K L).surjective a
  let x := finiteNormClass (ideleClassRepresentation ℚ) (numberFieldTowerBaseSubgroup K L)
    (numberFieldTowerTopSubgroup L) (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
    (numberFieldTowerIdeleClassEquivAmbientFixed K L c)
  have h := numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass K L c.toMul
  change globalNormResidueAbelianizationEquiv K L
      (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient K L x) =
    numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv K L x
  rw [show numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient K L x =
    Additive.ofMul (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c.toMul) from h]
  apply Additive.toMul.injective
  rw [numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv_apply]
  exact standardNumberFieldArtin_transport K L c.toMul

/-- The abelianized global norm-residue equivalence on a finite norm class. -/
theorem globalNormResidueAbelianizationEquiv_finiteNormClass
    (x : FiniteNormQuotient (ideleClassRepresentation ℚ)
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)) :
    letI := (numberFieldTowerReciprocityFiniteAbstractField K L).finite
    letI := numberFieldTowerExtensionSubgroup_normal K L
    letI := (numberFieldTowerFiniteGaloisSubextension K L).finite
    globalNormResidueAbelianizationEquiv K L
        (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
          K L x) =
      numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization
        K L
        (rationalCyclotomicDegreeData.normResidueSymbol
          (ideleClassRepresentation ℚ)
          rationalCyclotomicIdeleClassValuationData
          (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ)
          (numberFieldTowerReciprocityFiniteAbstractField K L)
          (numberFieldTowerFiniteGaloisSubextension K L) x) := by
  exact (globalNormResidueAbelianizationEquiv_transport_apply K L x).trans
    (numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv_apply K L x)

/-- On the genuine finite-reciprocity class of an abstract extension
automorphism, the finite-Galois norm-residue equivalence gives the class of
the corresponding actual automorphism in the Galois abelianization. -/
@[simp]
theorem globalNormResidueAbelianizationEquiv_finiteReciprocityHom
    (q :
      ClassFormation.FiniteGaloisSubextension.extensionQuotient
        (numberFieldTowerFiniteGaloisSubextension K L)) :
    let :=
      (numberFieldTowerReciprocityFiniteAbstractField K L).finite
    let :=
      numberFieldTowerExtensionSubgroup_normal K L
    let :=
      (numberFieldTowerFiniteGaloisSubextension K L).finite
    globalNormResidueAbelianizationEquiv K L
        (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
          K L
          (rationalCyclotomicDegreeData.finiteReciprocityHom
            (ideleClassRepresentation ℚ)
            rationalCyclotomicIdeleClassValuationData
            (
          rationalCyclotomicIdeleClassValuationData.classFieldAxiom_implies_unramifiedUnitCohomology
                (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ))
            (numberFieldTowerReciprocityFiniteAbstractField K L)
            (numberFieldTowerFiniteGaloisSubextension K L).field
            (numberFieldTowerFiniteGaloisSubextension K L).below
            (hLnormal :=
              (numberFieldTowerFiniteGaloisSubextension K L).normal)
            (hLfinite :=
              (numberFieldTowerFiniteGaloisSubextension K L).finite)
            (Additive.ofMul q))) =
      Additive.ofMul
        (Group.Abelianization.of
          (numberFieldTowerExtensionQuotientEquivGaloisGroup K L q)) := by
  intro hBaseFinite hExtensionNormal hRelativeFinite
  let x :=
    rationalCyclotomicDegreeData.finiteReciprocityHom
      (ideleClassRepresentation ℚ)
      rationalCyclotomicIdeleClassValuationData
      (rationalCyclotomicIdeleClassValuationData.classFieldAxiom_implies_unramifiedUnitCohomology
        (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ))
      (numberFieldTowerReciprocityFiniteAbstractField K L)
      (numberFieldTowerFiniteGaloisSubextension K L).field
      (numberFieldTowerFiniteGaloisSubextension K L).below
      (hLnormal :=
        (numberFieldTowerFiniteGaloisSubextension K L).normal)
      (hLfinite :=
        (numberFieldTowerFiniteGaloisSubextension K L).finite)
      (Additive.ofMul q)
  have hxNorm :
      rationalCyclotomicDegreeData.normResidueSymbol
          (ideleClassRepresentation ℚ)
          rationalCyclotomicIdeleClassValuationData
          (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ)
          (numberFieldTowerReciprocityFiniteAbstractField K L)
          (numberFieldTowerFiniteGaloisSubextension K L) x =
        Additive.ofMul (Group.Abelianization.of q) :=
    rationalCyclotomicDegreeData.normResidueSymbol_finiteReciprocityHom
      (ideleClassRepresentation ℚ)
      rationalCyclotomicIdeleClassValuationData
      (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ)
      (numberFieldTowerReciprocityFiniteAbstractField K L)
      (numberFieldTowerFiniteGaloisSubextension K L) q
  exact
    (globalNormResidueAbelianizationEquiv_transport_apply K L x).trans
      ((numberFieldTowerAbstractNormResidueGaloisAbelianizationEquiv_apply
          K L x).trans
        ((congrArg
            (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization
              K L)
            hxNorm).trans
          (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization_of
            K L q)))

/-- The inverse global reciprocity equivalence for an arbitrary finite Galois
extension. -/
noncomputable def globalReciprocityAbelianizationEquiv :
    Additive (Group.Abelianization (Gal(L / K))) ≃+
      Additive
        (IdeleClassGroup K ⧸
          (_root_.ideleClassNorm K L).range) :=
  (globalNormResidueAbelianizationEquiv K L).symm

/-- The genuine global norm-residue homomorphism with target the
abelianization of the actual Galois group. -/
noncomputable abbrev globalNormResidueAbelianizationMonoidHom :
    IdeleClassGroup K →* Group.Abelianization (Gal(L / K)) :=
  standardNumberFieldArtin K L

/-- Evaluation of the finite-Galois global norm-residue homomorphism is the
global equivalence applied to the genuine norm quotient class. -/
@[simp]
theorem globalNormResidueAbelianizationMonoidHom_apply
    (c : IdeleClassGroup K) :
    globalNormResidueAbelianizationMonoidHom K L c =
      Additive.toMul
        (globalNormResidueAbelianizationEquiv K L
          (Additive.ofMul
            (QuotientGroup.mk'
              (_root_.ideleClassNorm K L).range c))) :=
  rfl

/-- Evaluate the finite-Galois symbol on the norm class of an idèle class. -/
theorem globalNormResidueAbelianizationMonoidHom_finiteNormClass
    (c : IdeleClassGroup K) :
    letI := (numberFieldTowerReciprocityFiniteAbstractField K L).finite
    letI := numberFieldTowerExtensionSubgroup_normal K L
    letI := (numberFieldTowerFiniteGaloisSubextension K L).finite
    globalNormResidueAbelianizationMonoidHom K L c =
      Additive.toMul
        (numberFieldTowerAbelianizedExtensionQuotientEquivGaloisAbelianization
          K L
          (rationalCyclotomicDegreeData.normResidueSymbol
            (ideleClassRepresentation ℚ)
            rationalCyclotomicIdeleClassValuationData
            (ideleClassRepresentation_satisfiesClassFieldAxiom ℚ)
            (numberFieldTowerReciprocityFiniteAbstractField K L)
            (numberFieldTowerFiniteGaloisSubextension K L)
            (finiteNormClass (ideleClassRepresentation ℚ)
              (numberFieldTowerBaseSubgroup K L)
              (numberFieldTowerTopSubgroup L)
              (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
              (numberFieldTowerIdeleClassEquivAmbientFixed K L
                (Additive.ofMul c))))) := by
  let x : FiniteNormQuotient (ideleClassRepresentation ℚ)
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L) :=
    finiteNormClass (ideleClassRepresentation ℚ)
      (numberFieldTowerBaseSubgroup K L)
      (numberFieldTowerTopSubgroup L)
      (numberFieldTowerTopSubgroup_le_baseSubgroup K L)
      (numberFieldTowerIdeleClassEquivAmbientFixed K L (Additive.ofMul c))
  have hclass :=
    numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient_ideleClass
      K L c
  calc
    _ = Additive.toMul
        (globalNormResidueAbelianizationEquiv K L
          (Additive.ofMul
            (QuotientGroup.mk' (_root_.ideleClassNorm K L).range c))) :=
      globalNormResidueAbelianizationMonoidHom_apply K L c
    _ = Additive.toMul
        (globalNormResidueAbelianizationEquiv K L
          (numberFieldTowerFiniteNormQuotientEquivIdeleClassNormQuotient
            K L x)) :=
      congrArg (fun q => Additive.toMul
        (globalNormResidueAbelianizationEquiv K L q)) hclass.symm
    _ = _ := congrArg Additive.toMul
      (globalNormResidueAbelianizationEquiv_finiteNormClass K L x)

/-- An idele class has trivial finite-Galois norm-residue symbol exactly when
it is an actual idele-class norm from `L`. -/
@[simp]
theorem globalNormResidueAbelianizationMonoidHom_eq_one_iff
    (c : IdeleClassGroup K) :
    globalNormResidueAbelianizationMonoidHom K L c = 1 ↔
      c ∈ (_root_.ideleClassNorm K L).range := by
  change c ∈ (standardNumberFieldArtin K L).ker ↔ _
  rw [standardNumberFieldArtin_ker]

/-- The finite-Galois global norm-residue homomorphism is surjective onto the
actual Galois abelianization. -/
theorem globalNormResidueAbelianizationMonoidHom_surjective :
    Function.Surjective (globalNormResidueAbelianizationMonoidHom K L) :=
  standardNumberFieldArtin_surjective K L

/-- The finite-Galois global norm-residue symbol viewed on the idele group.

This is the genuine idele-class symbol pulled back along
`I_K → C_K`; in particular it is not a separately chosen map. -/
noncomputable def globalNormResidueAbelianizationIdeleMonoidHom :
    IdeleGroup K →*
      Group.Abelianization (Gal(L / K)) :=
  (globalNormResidueAbelianizationMonoidHom K L).comp
    (IdeleGroup.toStandardClass K)

/-- Evaluation of the finite-Galois norm-residue symbol on an idele is
evaluation of the class symbol on its genuine idele class. -/
@[simp]
theorem globalNormResidueAbelianizationIdeleMonoidHom_apply
    (a : IdeleGroup K) :
    globalNormResidueAbelianizationIdeleMonoidHom K L a =
      globalNormResidueAbelianizationMonoidHom K L
        (IdeleGroup.toStandardClass K a) :=
  rfl

/-- The finite-Galois norm-residue symbol on ideles is trivial on every
principal idele. -/
@[simp]
theorem globalNormResidueAbelianizationIdeleMonoidHom_principalIdele
    (x : Kˣ) :
    globalNormResidueAbelianizationIdeleMonoidHom K L
        (IdeleGroup.principalIdele K x) =
      1 := by
  have hclass :
      IdeleGroup.toStandardClass K
          (IdeleGroup.principalIdele K x) =
        1 :=
    (QuotientGroup.eq_one_iff
      (IdeleGroup.principalIdele K x)).2
      ⟨x, rfl⟩
  calc
    globalNormResidueAbelianizationIdeleMonoidHom K L
          (IdeleGroup.principalIdele K x) =
        globalNormResidueAbelianizationMonoidHom K L
          (IdeleGroup.toStandardClass K
            (IdeleGroup.principalIdele K x)) :=
      globalNormResidueAbelianizationIdeleMonoidHom_apply K L _
    _ = globalNormResidueAbelianizationMonoidHom K L 1 :=
      congrArg
        (globalNormResidueAbelianizationMonoidHom K L)
        hclass
    _ = 1 := map_one _

/-- The finite-Galois norm-residue symbol remains surjective when viewed
on ideles. -/
theorem globalNormResidueAbelianizationIdeleMonoidHom_surjective :
    Function.Surjective
      (globalNormResidueAbelianizationIdeleMonoidHom K L) :=
  (globalNormResidueAbelianizationMonoidHom_surjective K L).comp
    (IdeleGroup.toStandardClass_surjective K)

/-- An idele has trivial finite-Galois norm-residue symbol exactly when
its idele class is an actual norm from `L`. -/
@[simp]
theorem globalNormResidueAbelianizationIdeleMonoidHom_eq_one_iff
    (a : IdeleGroup K) :
    globalNormResidueAbelianizationIdeleMonoidHom K L a = 1 ↔
      IdeleGroup.toStandardClass K a ∈
        (_root_.ideleClassNorm K L).range := by
  simpa only [
    globalNormResidueAbelianizationIdeleMonoidHom_apply] using
      globalNormResidueAbelianizationMonoidHom_eq_one_iff K L
        (IdeleGroup.toStandardClass K a)

/-- The kernel of the idele-level finite-Galois norm-residue symbol is the
full inverse image of the genuine idele-class norm range. -/
@[simp]
theorem globalNormResidueAbelianizationIdeleMonoidHom_ker :
    (globalNormResidueAbelianizationIdeleMonoidHom K L).ker =
      (_root_.ideleClassNorm K L).range.comap
        (IdeleGroup.toStandardClass K) := by
  ext a
  change
    globalNormResidueAbelianizationIdeleMonoidHom K L a = 1 ↔
      IdeleGroup.toStandardClass K a ∈
        (_root_.ideleClassNorm K L).range
  exact
    globalNormResidueAbelianizationIdeleMonoidHom_eq_one_iff
      K L a

/-- The kernel of the finite-Galois norm-residue homomorphism is exactly the
range of the ordinary idele-class norm. -/
@[simp]
theorem globalNormResidueAbelianizationMonoidHom_ker :
    (globalNormResidueAbelianizationMonoidHom K L).ker =
      (_root_.ideleClassNorm K L).range := by
  ext c
  change
    globalNormResidueAbelianizationMonoidHom K L c = 1 ↔
      c ∈ (_root_.ideleClassNorm K L).range
  exact
    globalNormResidueAbelianizationMonoidHom_eq_one_iff
      K L c

/-- The index of the actual norm subgroup is the order of the
abelianization of the genuine finite Galois group. -/
theorem ideleClassNorm_index_eq_galoisAbelianization_card :
    (_root_.ideleClassNorm K L).range.index =
      Nat.card (Group.Abelianization (Gal(L / K))) := by
  calc
    (_root_.ideleClassNorm K L).range.index =
        Nat.card
          (IdeleClassGroup K ⧸
            (_root_.ideleClassNorm K L).range) :=
      Subgroup.index_eq_card
        ((_root_.ideleClassNorm K L).range)
    _ =
        Nat.card
          (Additive
            (IdeleClassGroup K ⧸
              (_root_.ideleClassNorm K L).range)) :=
      (Nat.card_congr Additive.toMul).symm
    _ =
        Nat.card
          (Additive
            (Group.Abelianization (Gal(L / K)))) :=
      Nat.card_congr
        (globalNormResidueAbelianizationEquiv K L).toEquiv
    _ =
        Nat.card
          (Group.Abelianization (Gal(L / K))) :=
      Nat.card_congr Additive.toMul

end Reciprocity
end GlobalClassFieldTheory
