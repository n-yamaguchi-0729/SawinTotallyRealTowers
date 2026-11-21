/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquiv
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.FiniteIdeleClassSystem
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimit
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassEmbeddingBaseChange
public import Nyll.GaloisCohomology.Cyclic.NormKernelVanishing
public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.FieldTheory.Galois.Profinite
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.EmbeddingNorm

/-!
# The rational absolute idele-class direct limit

The number-field direct limit specialized at `ℚ`, with the finite-level
tensor comparisons used by arithmetic descent.
-/



@[expose] public section

open scoped NumberField TensorProduct
open NumberField

noncomputable section

namespace GlobalClassFieldTheory
namespace Reciprocity

open CyclicCohomology

universe u

/-- A finite quotient of nested closed rational absolute Galois
subgroups carries its canonical finite type. -/
noncomputable instance rationalClosedSubgroupQuotientFintype
    (K L : ClosedSubgroup
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ))
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite
      (K.toSubgroup ⧸ extensionSubgroup K L hLK)] :
    Fintype (K.toSubgroup ⧸ extensionSubgroup K L hLK) :=
  Fintype.ofFinite _

/-- Extending the diagonal rational idele class through two nested
intermediate fields is the diagonal class at the larger field. -/
theorem rationalRelativeIdeleClassEmbedding_classInclusion
    {E F : IntermediateField ℚ (SeparableClosure ℚ)}
    [NumberField E] [NumberField F]
    (h : E ≤ F)
    (c : IdeleClassGroup ℚ) :
    RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h)
        (RelativeIdeleGroup.classInclusion ℚ E c) =
      RelativeIdeleGroup.classInclusion ℚ F c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  rfl

/-- The action of the rational absolute Galois group on one finite
relative idele class group, obtained by restricting automorphisms. -/
@[reducible]
noncomputable def rationalRelativeAbsoluteGaloisIdeleClassAction
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)) :
    MulDistribMulAction
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      (RelativeIdeleGroup.ClassGroup ℚ E) := by
  letI :
      MulDistribMulAction (E ≃ₐ[ℚ] E)
        (RelativeIdeleGroup.ClassGroup ℚ E) :=
    RelativeIdeleGroup.Cohomology.ideleClassMulDistribMulAction ℚ E
  exact
    MulDistribMulAction.compHom
      (RelativeIdeleGroup.ClassGroup ℚ E)
      (AlgEquiv.restrictNormalHom E)

/-- The rational absolute Galois action on every finite-Galois
relative idele class group. -/
noncomputable instance rationalFiniteGaloisRelativeIdeleClassMulDistribMulAction
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)) :
    MulDistribMulAction
      (SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
      (RelativeIdeleGroup.ClassGroup ℚ E) :=
  rationalRelativeAbsoluteGaloisIdeleClassAction E

@[simp]
theorem rationalRelativeAbsoluteGaloisIdeleClass_smul_mk
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (a : RelativeIdeleGroup ℚ E) :
    σ • QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup ℚ E) a =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup ℚ E)
        ((AlgEquiv.restrictNormalHom E σ) • a) :=
  rfl

/-- Relative-adele scalar extension intertwines conjugation with the
restriction of an absolute Galois automorphism. -/
theorem rationalRelativeAdeleEmbedding_conjugation_of_restrict
    {E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E]
    {F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ (F : IntermediateField ℚ (SeparableClosure ℚ)))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (τ : E ≃ₐ[ℚ] E)
    (hστ : ∀ x : E,
      ((τ x : E) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (z : RelativeAdeleRing ℚ E) :
    RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion h)
        (RelativeIdeleGroup.conjugation ℚ E τ z) =
      RelativeIdeleGroup.conjugation ℚ F
        (AlgEquiv.restrictNormalHom F σ)
        (RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion h) z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
      simp only [RelativeIdeleGroup.conjugation_tmul,
        RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul]
      congr 1
      apply Subtype.ext
      calc
        ((IntermediateField.inclusion h (τ x) : F) :
            SeparableClosure ℚ) =
            ((τ x : E) : SeparableClosure ℚ) := rfl
        _ = σ (x : SeparableClosure ℚ) := hστ x
        _ = σ ((IntermediateField.inclusion h x : F) :
            SeparableClosure ℚ) := rfl
        _ = (((AlgEquiv.restrictNormalHom F σ)
              (IntermediateField.inclusion h x) : F) :
            SeparableClosure ℚ) :=
          (AlgEquiv.restrictNormal_commutes σ F
            (IntermediateField.inclusion h x)).symm
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Relative-idele scalar extension intertwines conjugation with the
restriction of an absolute Galois automorphism. -/
theorem rationalRelativeIdeleEmbedding_conjugation_of_restrict
    {E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E]
    {F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ (F : IntermediateField ℚ (SeparableClosure ℚ)))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (τ : E ≃ₐ[ℚ] E)
    (hστ : ∀ x : E,
      ((τ x : E) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (a : RelativeIdeleGroup ℚ E) :
    RelativeIdeleGroup.ideleEmbedding (IntermediateField.inclusion h)
        (τ • a) =
      (AlgEquiv.restrictNormalHom F σ) •
        RelativeIdeleGroup.ideleEmbedding (IntermediateField.inclusion h) a := by
  apply Units.ext
  exact
    rationalRelativeAdeleEmbedding_conjugation_of_restrict
      h σ τ hστ
      (a : RelativeAdeleRing ℚ E)

/-- Relative idele-class scalar extension intertwines conjugation with
the restriction of an absolute Galois automorphism. -/
theorem
    rationalRelativeIdeleClassEmbedding_conjugation_of_restrict
    {E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E]
    {F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ (F : IntermediateField ℚ (SeparableClosure ℚ)))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (τ : E ≃ₐ[ℚ] E)
    (hστ : ∀ x : E,
      ((τ x : E) : SeparableClosure ℚ) =
        σ (x : SeparableClosure ℚ))
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) (τ • c) =
      σ • RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup ℚ F))
    (rationalRelativeIdeleEmbedding_conjugation_of_restrict
      h σ τ hστ a)

/-- The transition map between finite Galois relative idele class groups
is equivariant for the rational absolute Galois action. -/
theorem rationalRelativeIdeleClassEmbedding_smul
    {E F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ F)
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) (σ • c) =
      σ • RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c := by
  apply rationalRelativeIdeleClassEmbedding_conjugation_of_restrict
    h σ (AlgEquiv.restrictNormalHom E σ)
  intro x
  simp only [AlgEquiv.restrictNormalHom_apply]

/-- Acting after scalar extension agrees with the class embedding induced
by the resulting restricted field embedding. -/
theorem
    rationalRelativeIdeleClassEmbedding_smul_eq_classEmbedding
    {E : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E]
    {F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (h : E ≤ F)
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    (AlgEquiv.restrictNormalHom F σ) •
        RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c =
      RelativeIdeleGroup.classEmbedding
        ((AlgEquiv.restrictNormalHom F σ).toAlgHom.comp
          (IntermediateField.inclusion h)) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  apply congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup ℚ F))
  apply Units.ext
  change
    RelativeIdeleGroup.conjugation ℚ F
        (AlgEquiv.restrictNormalHom F σ)
        (RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion h)
          (a : RelativeAdeleRing ℚ E)) =
      RelativeIdeleGroup.adeleEmbedding
        ((AlgEquiv.restrictNormalHom F σ).toAlgHom.comp
          (IntermediateField.inclusion h))
        (a : RelativeAdeleRing ℚ E)
  induction (a : RelativeAdeleRing ℚ E) using
      TensorProduct.inductionOn with
  | tmul y x =>
      simp only [RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul,
        RelativeIdeleGroup.conjugation_tmul]
      congr 1
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Scalar extension of relative adeles along the identity inclusion is
the identity. -/
theorem rationalRelativeAdeleEmbedding_self
    (E : IntermediateField ℚ (SeparableClosure ℚ))
    [NumberField E]
    (z : RelativeAdeleRing ℚ E) :
    RelativeIdeleGroup.adeleEmbedding
      (IntermediateField.inclusion (show E ≤ E from le_rfl)) z = z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
      simp only [RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul]
      congr 1
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Scalar extension of relative adeles is transitive in a tower of
intermediate fields. -/
theorem rationalRelativeAdeleEmbedding_comp
    {E F H : IntermediateField ℚ (SeparableClosure ℚ)}
    [NumberField E] [NumberField F] [NumberField H]
    (hEF : E ≤ F) (hFH : F ≤ H)
    (z : RelativeAdeleRing ℚ E) :
    RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion hFH)
        (RelativeIdeleGroup.adeleEmbedding (IntermediateField.inclusion hEF) z) =
      RelativeIdeleGroup.adeleEmbedding
        (IntermediateField.inclusion (hEF.trans hFH)) z := by
  induction z using TensorProduct.inductionOn with
  | tmul a x =>
      simp only [RelativeIdeleGroup.adeleEmbedding,
        RelativeIdeleGroup.scalarEmbedding_tmul]
      congr 1
  | add x y hx hy =>
      simp only [map_add, hx, hy]

/-- Scalar extension of relative idele classes along the identity
inclusion is the identity. -/
theorem rationalRelativeIdeleClassEmbedding_self
    (E : IntermediateField ℚ (SeparableClosure ℚ))
    [NumberField E]
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    RelativeIdeleGroup.classEmbedding
      (IntermediateField.inclusion (show E ≤ E from le_rfl)) c = c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup ℚ E))
    (Units.ext
      (rationalRelativeAdeleEmbedding_self E
        (a : RelativeAdeleRing ℚ E)))

/-- Scalar extension of relative idele classes is transitive in a tower
of intermediate fields. -/
theorem rationalRelativeIdeleClassEmbedding_comp
    {E F H : IntermediateField ℚ (SeparableClosure ℚ)}
    [NumberField E] [NumberField F] [NumberField H]
    (hEF : E ≤ F) (hFH : F ≤ H)
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hFH)
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion hEF) c) =
      RelativeIdeleGroup.classEmbedding
        (IntermediateField.inclusion (hEF.trans hFH)) c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  exact congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup ℚ H))
    (Units.ext
      (rationalRelativeAdeleEmbedding_comp hEF hFH
        (a : RelativeAdeleRing ℚ E)))

/-- The existing tensor presentation compared with the standard finite level.
This is used only at the boundary of the tensor descent calculations. -/
def rationalRelativeIdeleClassEquivStandard
    (E : IntermediateField ℚ (SeparableClosure ℚ)) [FiniteDimensional ℚ E] :
    RelativeIdeleGroup.ClassGroup ℚ E ≃* NumberField.IdeleClassGroup (𝓞 E) E :=
  relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := E)

/-- The tensor-to-standard comparison carries the actual restricted action
to canonical field-equivalence transport. -/
theorem rationalRelativeIdeleClassEquivStandard_smul
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    rationalRelativeIdeleClassEquivStandard E (σ • c) =
      σ • rationalRelativeIdeleClassEquivStandard E c := by
  change relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := E)
      ((AlgEquiv.restrictNormalHom E σ) • c) =
    NumberField.IdeleClassGroup.congr (AlgEquiv.restrictNormalHom E σ)
      (rationalRelativeIdeleClassEquivStandard E c)
  exact relativeIdeleClassBaseChangeMulEquiv_smul_congr _ _

/-- The standard transition square is proved from the existing tensor
base-change theorem and the canonical standard scalar-inclusion comparison. -/
theorem rationalRelativeIdeleClassEquivStandard_embedding
    {E F : IntermediateField ℚ (SeparableClosure ℚ)}
    [FiniteDimensional ℚ E] [FiniteDimensional ℚ F] (h : E ≤ F)
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    rationalRelativeIdeleClassEquivStandard F
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c) =
      finiteIdeleClassEmbedding ℚ h (rationalRelativeIdeleClassEquivStandard E c) := by
  let : Algebra E F := (IntermediateField.inclusion h).toRingHom.toAlgebra
  let : IsScalarTower ℚ E F := IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)
  let : FiniteDimensional E F := FiniteDimensional.right ℚ E F
  have hi : IntermediateField.inclusion h = IsScalarTower.toAlgHom ℚ E F := by
    apply AlgHom.ext
    intro x
    rfl
  let eF := relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := F)
  let a := relativeIdeleClassBaseChangeMulEquiv (K := ℚ) (L := E) c
  have he : eF (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c) =
      ideleClassExtension E F a :=
    (congrArg (fun f : E →ₐ[ℚ] F => eF (RelativeIdeleGroup.classEmbedding f c)) hi).trans
      (FiniteTowerNormCore.relativeIdeleClassBaseChange_classEmbedding_toAlgHom
        (K := ℚ) (M := E) (L := F) c)
  exact he

attribute [local instance] ideleClassDirectLimitSMul

/-- Tensor descent enters the standard direct limit through the existing
finite-level comparison. No second direct limit is constructed. -/
def rationalRelativeIdeleClassToDirectLimit
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)) :
    RelativeIdeleGroup.ClassGroup ℚ E →* (ideleClassDirectLimit ℚ) :=
  (finiteIdeleClassToDirectLimit ℚ E).comp
    (rationalRelativeIdeleClassEquivStandard E).toMonoidHom

/-- The tensor comparison is compatible with the standard transition relation. -/
theorem rationalIdeleClassDirectLimit_mk_apply
    {E F : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)}
    (c : RelativeIdeleGroup.ClassGroup ℚ E) (h : E ≤ F) :
    rationalRelativeIdeleClassToDirectLimit F
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c) =
      rationalRelativeIdeleClassToDirectLimit E c := by
  change finiteIdeleClassToDirectLimit ℚ F
      (rationalRelativeIdeleClassEquivStandard F
        (RelativeIdeleGroup.classEmbedding (IntermediateField.inclusion h) c)) = _
  rw [rationalRelativeIdeleClassEquivStandard_embedding]
  exact ideleClassDirectLimit_mk_apply ℚ
    (rationalRelativeIdeleClassEquivStandard E c) h

/-- Tensor representatives retain the exact action through their standard
finite-level comparison. -/
theorem rationalRelativeIdeleClassToDirectLimit_smul
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ))
    (σ : SeparableClosure ℚ ≃ₐ[ℚ] SeparableClosure ℚ)
    (c : RelativeIdeleGroup.ClassGroup ℚ E) :
    σ • rationalRelativeIdeleClassToDirectLimit E c =
      rationalRelativeIdeleClassToDirectLimit E (σ • c) := by
  change σ • finiteIdeleClassToDirectLimit ℚ E (rationalRelativeIdeleClassEquivStandard E c) =
    finiteIdeleClassToDirectLimit ℚ E (rationalRelativeIdeleClassEquivStandard E (σ • c))
  rw [rationalRelativeIdeleClassEquivStandard_smul]
  exact finiteIdeleClassToDirectLimit_smul ℚ E σ _

/-- The tensor comparison followed by the canonical standard inclusion is
injective, as required by the finite-level descent calculations. -/
theorem rationalRelativeIdeleClassToDirectLimit_injective
    (E : FiniteGaloisIntermediateField ℚ (SeparableClosure ℚ)) :
    Function.Injective (rationalRelativeIdeleClassToDirectLimit E) :=
  (finiteIdeleClassToDirectLimit_injective ℚ E).comp
    (rationalRelativeIdeleClassEquivStandard E).injective

end Reciprocity
end GlobalClassFieldTheory
