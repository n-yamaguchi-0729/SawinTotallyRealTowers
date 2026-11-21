/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.AlgEquivIdeleClassTopology
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.ConnectedComponentQuotientCongr
public import Nyll.ProCGroups.Abelian.TopologicalAbelianization
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.MathlibTopologicalGlobalReciprocity
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.NumberFieldNormResidue
public import Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.InfiniteGlobalArtinBaseEquiv
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Galois.MaximalAbelianBaseEquiv

/-!
# Finite projections and model independence of the public global Artin map

The native map has the same value in each compatible number-field model.
Its finite projections recover the Artin maps on the actual extensions.
-/

@[expose] public section

open scoped NumberField

noncomputable section

namespace GlobalClassFieldTheory.Reciprocity

open ClassFieldTheory

universe u v w

variable {K : Type u} {M : Type v} [Field K] [NumberField K] [Field M] [NumberField M]

/-- Native quotient reciprocity retains the actual maximal-abelian Artin
value on the corresponding ordinary idèle class. -/
theorem mathlibIdeleClassConnectedQuotientEquivAbelianization_value
    (a : NumberField.IdeleClassGroup (𝓞 K) K) :
    mathlibAbelianizationToMaximal K
        (mathlibIdeleClassConnectedQuotientEquivAbelianization K
          (QuotientGroup.mk'
            (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K)) a)) =
      maximalAbelianGlobalArtin K a := by
  let e := absoluteTopologicalAbelianizationEquivMaximalAbelianGalois K
  let b := absoluteGaloisGroupAbelianizationEquivSeparable K
  let f := ideleClassComponentQuotientEquivMaximalAbelianGalois K
  let g := f (QuotientGroup.mk' (ideleClassIdentityComponent K) a)
  change e (b (b.symm (e.symm g))) = maximalAbelianGlobalArtin K a
  calc
    _ = e (e.symm g) := congrArg e (b.apply_symm_apply _)
    _ = g := e.apply_symm_apply g
    _ = _ := ideleClassComponentQuotientEquivMaximalAbelianGalois_mk K a

/-- Native global reciprocity commutes pointwise with the given base-field
isomorphism and its actual absolute Galois map. -/
theorem mathlibIdeleClassConnectedQuotientEquivAbelianization_natural_mk
    (e : K ≃ₐ[ℚ] M) (a : NumberField.IdeleClassGroup (𝓞 K) K) :
    absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv
        (mathlibIdeleClassConnectedQuotientEquivAbelianization K
          (QuotientGroup.mk'
            (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K)) a)) =
      mathlibIdeleClassConnectedQuotientEquivAbelianization M
        (QuotientGroup.mk'
          (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 M) M))
          (NumberField.IdeleClassGroup.congrContinuousMulEquiv e a)) := by
  apply (mathlibAbelianizationToMaximal M).injective
  rw [mathlibAbelianizationToMaximal_baseEquiv,
    mathlibIdeleClassConnectedQuotientEquivAbelianization_value,
    mathlibIdeleClassConnectedQuotientEquivAbelianization_value]
  exact infiniteGlobalIdeleClassArtinMonoidHom_semilinear
    (Ω := maximalAbelianExtension K) (Ψ := maximalAbelianExtension M)
    e (maximalAbelianExtensionBaseEquiv e.toRingEquiv)
    (maximalAbelianExtensionBaseEquiv_commutes e.toRingEquiv) a

/-- Naturality holds on the connected-component quotient itself. -/
theorem mathlibIdeleClassConnectedQuotientEquivAbelianization_natural
    (e : K ≃ₐ[ℚ] M) (a : IdeleClassConnectedQuotient K) :
    absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv
        (mathlibIdeleClassConnectedQuotientEquivAbelianization K a) =
      mathlibIdeleClassConnectedQuotientEquivAbelianization M
        (connectedComponentQuotientCongr
          (NumberField.IdeleClassGroup.congrContinuousMulEquiv e) a) := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective
    (Subgroup.connectedComponentOfOne (NumberField.IdeleClassGroup (𝓞 K) K)) a
  rw [connectedComponentQuotientCongr_mk]
  exact mathlibIdeleClassConnectedQuotientEquivAbelianization_natural_mk e b

/-- Every equivalent number-field model gives the same specified public
reciprocity map on the original number field. -/
theorem mathlibIdeleClassConnectedQuotientEquivAbelianization_model
    (e : M ≃ₐ[ℚ] K) :
    mathlibIdeleClassConnectedQuotientEquivAbelianization K =
      (connectedComponentQuotientCongr
        (NumberField.IdeleClassGroup.congrContinuousMulEquiv e)).symm.trans
        ((mathlibIdeleClassConnectedQuotientEquivAbelianization M).trans
          (absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv)) := by
  apply ContinuousMulEquiv.ext
  intro a
  change mathlibIdeleClassConnectedQuotientEquivAbelianization K a =
    absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv
      (mathlibIdeleClassConnectedQuotientEquivAbelianization M
        ((connectedComponentQuotientCongr
          (NumberField.IdeleClassGroup.congrContinuousMulEquiv e)).symm a))
  rw [mathlibIdeleClassConnectedQuotientEquivAbelianization_natural,
    ContinuousMulEquiv.apply_symm_apply]

/-- The model comparison is independent of the chosen compatible algebraic
closure equivalence as well as of the chosen equivalent base field. -/
theorem mathlibIdeleClassConnectedQuotientEquivAbelianization_model_of_closure
    (e : M ≃ₐ[ℚ] K) (c : AlgebraicClosure M ≃+* AlgebraicClosure K)
    (hc : ∀ a : M, c (algebraMap M (AlgebraicClosure M) a) =
      algebraMap K (AlgebraicClosure K) (e a)) :
    mathlibIdeleClassConnectedQuotientEquivAbelianization K =
      (connectedComponentQuotientCongr
        (NumberField.IdeleClassGroup.congrContinuousMulEquiv e)).symm.trans
        ((mathlibIdeleClassConnectedQuotientEquivAbelianization M).trans
          (ProCGroups.Abelian.TopologicalAbelianization.congr
            (semilinearGaloisContinuousEquiv e.toRingEquiv c hc))) := by
  have hg : ProCGroups.Abelian.TopologicalAbelianization.congr
      (semilinearGaloisContinuousEquiv e.toRingEquiv c hc) =
      absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv :=
    semilinearGaloisAbelianizationEquiv_independent e.toRingEquiv c
      (IsAlgClosure.equivOfEquiv (AlgebraicClosure M) (AlgebraicClosure K) e.toRingEquiv)
      hc (IsAlgClosure.equivOfEquiv_algebraMap
        (AlgebraicClosure M) (AlgebraicClosure K) e.toRingEquiv)
  exact (mathlibIdeleClassConnectedQuotientEquivAbelianization_model e).trans
    (congrArg (fun g =>
      (connectedComponentQuotientCongr
        (NumberField.IdeleClassGroup.congrContinuousMulEquiv e)).symm.trans
        ((mathlibIdeleClassConnectedQuotientEquivAbelianization M).trans g)) hg.symm)

/-- The named public map has the original maximal-abelian value on each
ordinary class, with its original geometric normalization unchanged. -/
theorem mathlibGlobalArtin_toMaximal (a : NumberField.IdeleClassGroup (𝓞 K) K) :
    mathlibAbelianizationToMaximal K (mathlibGlobalArtin K a) =
      maximalAbelianGlobalArtin K a := by
  rw [mathlibGlobalArtin_apply]
  exact mathlibIdeleClassConnectedQuotientEquivAbelianization_value a

/-- A finite coordinate of the absolute standard Artin map evaluates the
original-field finite Artin homomorphism on the same standard class. -/
theorem mathlibGlobalArtin_finiteProjection_standard
    (a : NumberField.IdeleClassGroup (𝓞 K) K)
    (E : FiniteGaloisIntermediateField K (maximalAbelianExtension K)) :
    let : NumberField E := NumberField.of_module_finite K E
    AlgEquiv.restrictNormalHom E (mathlibAbelianizationToMaximal K (mathlibGlobalArtin K a)) =
      standardNumberFieldArtinContinuousMonoidHom K E a := by
  intro hE
  rw [mathlibGlobalArtin_toMaximal]
  exact infiniteGlobalIdeleClassArtinMonoidHom_finiteProjection a E

/-- The original-field finite coordinate also applies through a given
embedding into the maximal abelian extension. -/
theorem mathlibGlobalArtin_finiteProjection_standard_of_scalarTower
    (L : Type w) [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [Algebra L (maximalAbelianExtension K)] [IsScalarTower K L (maximalAbelianExtension K)]
    (a : NumberField.IdeleClassGroup (𝓞 K) K) :
    AlgEquiv.restrictNormalHom L (mathlibAbelianizationToMaximal K (mathlibGlobalArtin K a)) =
      standardNumberFieldArtinContinuousMonoidHom K L a := by
  rw [mathlibGlobalArtin_toMaximal]
  obtain ⟨b, rfl⟩ := IdeleGroup.toStandardClass_surjective K a
  rw [maximalAbelianGlobalArtin_mk]
  change _ = globalNormResidueMonoidHom K L (IdeleGroup.toStandardClass K b)
  rw [globalNormResidueMonoidHom_mk]
  exact restrictNormalHom_infiniteGlobalArtinMonoidHom_of_scalarTower K L
    (maximalAbelianExtension K) b

/-- Base-field equivalences intertwine the named public Artin maps on each
idèle class. -/
theorem mathlibGlobalArtin_baseEquiv
    (e : K ≃ₐ[ℚ] M) (a : NumberField.IdeleClassGroup (𝓞 K) K) :
    absoluteGaloisGroupAbelianizationEquivOfRingEquiv e.toRingEquiv
        (mathlibGlobalArtin K a) =
      mathlibGlobalArtin M (NumberField.IdeleClassGroup.congrContinuousMulEquiv e a) := by
  rw [mathlibGlobalArtin_apply, mathlibGlobalArtin_apply]
  exact mathlibIdeleClassConnectedQuotientEquivAbelianization_natural_mk e a

end GlobalClassFieldTheory.Reciprocity
