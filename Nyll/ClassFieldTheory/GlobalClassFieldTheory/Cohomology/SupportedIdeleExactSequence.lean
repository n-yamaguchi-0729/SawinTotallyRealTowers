/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/


module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.SupportedBridge
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand

/-!
# The supported idele short exact sequence
-/

@[expose] public section

open scoped NumberField TensorProduct
open NumberField IsDedekindDomain

noncomputable section

open RelativeIdeleGroup.Cohomology

namespace GlobalClassFieldTheory
namespace Cohomology


variable
    {K L : Type}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]


/-- The diagonal map from extension-field `S`-units directly into the
supported relative ideles. -/
noncomputable def sUnitToRelativeIdeleSupported
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    SUnitGroup (K := L)
        (finitePlacesAbove (K := K) (L := L) S) →*
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S :=
  ((RelativeIdeleGroup.principalSubgroup K L).subgroupOf
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S)).subtype.comp
    (sUnitToRelativePrincipalSupportedIntersection
      (K := K) (L := L) S)

/-- The restriction of the idele-class quotient map to the supported
relative ideles. -/
noncomputable def relativeIdeleSupportedToClass
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S →*
      RelativeIdeleGroup.ClassGroup K L :=
  (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K L)).comp
    (relativeIdeleLocalTensorDecompositionSupportedSubgroup
      (K := K) (L := L) S).subtype

omit [IsGalois K L] in
/-- Equivariance of the diagonal `S`-unit map into supported relative
ideles. -/
theorem sUnitToRelativeIdeleSupported_equivariant
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let :=
      sUnitMulDistribMulAction K L
        (finitePlacesAbove (K := K) (L := L) S)
        (finitePlacesAbove_isGaloisStable
          (K := K) (L := L) S)
    let :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    ∀ (σ : L ≃ₐ[K] L)
      (x :
        SUnitGroup (K := L)
          (finitePlacesAbove (K := K) (L := L) S)),
      sUnitToRelativeIdeleSupported
          (K := K) (L := L) S (σ • x) =
        σ •
          sUnitToRelativeIdeleSupported
            (K := K) (L := L) S x := by
  intro sUnitAction supportedAction σ x
  apply Subtype.ext
  change
    RelativeIdeleGroup.principalIdele K L
        (((σ • x :
          SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S)) :
          Lˣ)) =
      σ • RelativeIdeleGroup.principalIdele K L (x : Lˣ)
  rw [sUnit_smul_coe]
  exact
    (RelativeIdeleGroup.smul_principalIdele
      K L σ (x : Lˣ)).symm

omit [NumberField L] [IsGalois K L] in
/-- Equivariance of the supported-idele quotient map. -/
theorem relativeIdeleSupportedToClass_equivariant
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    let :=
      relativeIdeleLocalTensorDecompositionSupportedSubgroupAction
        (K := K) (L := L) S
    let := ideleClassMulDistribMulAction K L
    ∀ (σ : L ≃ₐ[K] L)
      (z :
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
          (K := K) (L := L) S),
      relativeIdeleSupportedToClass
          (K := K) (L := L) S (σ • z) =
        σ •
          relativeIdeleSupportedToClass
            (K := K) (L := L) S z := by
  intro supportedAction classAction σ z
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L)
        ((σ • z :
          relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) :
          RelativeIdeleGroup K L) =
      σ •
        QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L)
          (z : RelativeIdeleGroup K L)
  rw [
    relativeIdeleLocalTensorDecompositionSupportedSubgroupAction_coe]
  exact ideleClassQuotientMap_equivariant K L σ z

omit [IsGalois K L] in
/-- The diagonal `S`-unit map into supported relative ideles is
injective. -/
theorem sUnitToRelativeIdeleSupported_injective
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective
      (sUnitToRelativeIdeleSupported
        (K := K) (L := L) S) := by
  intro x y hxy
  apply
    (sUnitEquivRelativePrincipalSupportedIntersection
      (K := K) (L := L) S).injective
  apply
    ((RelativeIdeleGroup.principalSubgroup K L).subgroupOf
      (relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S)).subtype_injective
  exact hxy

omit [NumberField L] [IsGalois K L] in
/-- If the supported and principal relative ideles generate all
relative ideles, the restricted map to idele classes is surjective. -/
theorem relativeIdeleSupportedToClass_surjective
    (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hSP :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S ⊔
          RelativeIdeleGroup.principalSubgroup K L =
        ⊤) :
    Function.Surjective
      (relativeIdeleSupportedToClass
        (K := K) (L := L) S) := by
  intro q
  refine q.inductionOn' ?_
  intro g
  have hg :
      g ∈
        relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S ⊔
            RelativeIdeleGroup.principalSubgroup K L := by
    rw [hSP]
    exact Subgroup.mem_top g
  rw [Subgroup.mem_sup] at hg
  obtain ⟨s, hs, p, hp, hsp⟩ := hg
  refine ⟨⟨s, hs⟩, ?_⟩
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L) s =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L) g
  rw [← hsp, map_mul]
  have hpone :
      QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) p =
        1 :=
    (QuotientGroup.eq_one_iff
      (N := RelativeIdeleGroup.principalSubgroup K L)
      (x := p)).2 hp
  rw [hpone]
  exact
    (mul_one
      (QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K L) s)).symm

omit [IsGalois K L] in
/-- Exactness at the supported relative ideles of
`S`-units → supported ideles → idele classes. -/
theorem sUnit_supportedIdele_ideleClass_exact
    (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ∀ z :
      relativeIdeleLocalTensorDecompositionSupportedSubgroup
        (K := K) (L := L) S,
      relativeIdeleSupportedToClass
          (K := K) (L := L) S z = 1 ↔
        ∃ x :
          SUnitGroup (K := L)
            (finitePlacesAbove (K := K) (L := L) S),
          sUnitToRelativeIdeleSupported
              (K := K) (L := L) S x =
            z := by
  intro z
  constructor
  · intro hz
    have hzPrincipal :
        (z : RelativeIdeleGroup K L) ∈
          RelativeIdeleGroup.principalSubgroup K L := by
      exact
        (QuotientGroup.eq_one_iff
          (N := RelativeIdeleGroup.principalSubgroup K L)
          (x := (z : RelativeIdeleGroup K L))).1 hz
    let y :
        (RelativeIdeleGroup.principalSubgroup K L).subgroupOf
          (relativeIdeleLocalTensorDecompositionSupportedSubgroup
            (K := K) (L := L) S) :=
      ⟨z, hzPrincipal⟩
    obtain ⟨x, hx⟩ :=
      (sUnitEquivRelativePrincipalSupportedIntersection
        (K := K) (L := L) S).surjective y
    refine ⟨x, ?_⟩
    apply Subtype.ext
    have hcoerce :=
      congrArg
        (fun a :
          (RelativeIdeleGroup.principalSubgroup K L).subgroupOf
            (relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S) =>
          (a :
            relativeIdeleLocalTensorDecompositionSupportedSubgroup
              (K := K) (L := L) S))
        hx
    exact congrArg Subtype.val hcoerce
  · rintro ⟨x, rfl⟩
    change
      QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L)
          (RelativeIdeleGroup.principalIdele K L (x : Lˣ)) =
        1
    exact
      (QuotientGroup.eq_one_iff
        (N := RelativeIdeleGroup.principalSubgroup K L)
        (x :=
          RelativeIdeleGroup.principalIdele K L (x : Lˣ))).2
        ⟨(x : Lˣ), rfl⟩

end Cohomology
end GlobalClassFieldTheory
