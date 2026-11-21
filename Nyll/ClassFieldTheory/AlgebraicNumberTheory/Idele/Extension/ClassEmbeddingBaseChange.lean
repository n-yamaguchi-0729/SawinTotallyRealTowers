/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.Tower
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.TowerBaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.ClassGroup.NormComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleClassBaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.EmbeddingNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.BaseChange

/-!
# Tensor base change and class embeddings

The same extension map on relative idele classes is compatible with changing
from a fixed bottom-field tensor presentation to the intermediate field.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace GlobalClassFieldTheory.Reciprocity.FiniteTowerNormCore

universe u v w

private theorem relativeAdeleEmbedding_toAlgHom_unflatten
    {K : Type u} {M : Type v} {L : Type w}
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    (a : RelativeAdeleRing K M) :
    towerRelativeAdeleUnflatten K M L
        (RelativeIdeleGroup.adeleEmbedding
          (IsScalarTower.toAlgHom K M L) a) =
      a ⊗ₜ[M] (1 : L) := by
  have hflatten :
      towerRelativeAdeleFlatten K M L
          (towerRelativeAdeleUnflatten K M L
            (RelativeIdeleGroup.adeleEmbedding
              (IsScalarTower.toAlgHom K M L) a)) =
        RelativeIdeleGroup.adeleEmbedding
          (IsScalarTower.toAlgHom K M L) a :=
    (towerRelativeAdeleRingEquiv K M L).apply_symm_apply _
  apply (towerRelativeAdeleRingEquiv K M L).injective
  change
    towerRelativeAdeleFlatten K M L
        (towerRelativeAdeleUnflatten K M L
          (RelativeIdeleGroup.adeleEmbedding
            (IsScalarTower.toAlgHom K M L) a)) =
      towerRelativeAdeleFlatten K M L
        (a ⊗ₜ[M] (1 : L))
  rw [hflatten, towerRelativeAdeleFlatten_tmul]
  simp only [map_one, mul_one]
  rfl

private theorem relativeIdeleEmbedding_toAlgHom_unflatten
    {K : Type u} {M : Type v} {L : Type w}
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    (a : RelativeIdeleGroup K M) :
    let : Algebra M (RelativeAdeleRing K M) :=
      relativeAdeleRingIntermediateAlgebra K M
    (towerRelativeIdeleEquiv K M L).symm
        (RelativeIdeleGroup.ideleEmbedding
          (IsScalarTower.toAlgHom K M L) a) =
      (Units.map
        (@Algebra.TensorProduct.includeLeft
          M M (RelativeAdeleRing K M) L
          inferInstance inferInstance
          (relativeAdeleRingIntermediateAlgebra K M)
          inferInstance inferInstance inferInstance
          (relativeAdeleRingIntermediateAlgebra K M)
          (smulCommClass_self M (RelativeAdeleRing K M))).toRingHom a :
        TowerRelativeIdeleGroup K M L) := by
  intro sharedOwner1
  apply Units.ext
  exact relativeAdeleEmbedding_toAlgHom_unflatten
    (K := K) (M := M) (L := L) (a : RelativeAdeleRing K M)

/-- The tensor tower comparison sends class inclusion to relative class inclusion. -/
theorem
    relativeIdeleClassEmbedding_toAlgHom_towerBaseChange
    {K : Type u} {M : Type v} {L : Type w}
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    (c : RelativeIdeleGroup.ClassGroup K M) :
    towerRelativeIdeleClassBaseChangeMulEquiv K M L
        ((TowerRelativeIdeleGroup.classGroupEquiv K M L).symm
          (RelativeIdeleGroup.classEmbedding
            (IsScalarTower.toAlgHom K M L) c)) =
      RelativeIdeleGroup.classInclusion M L
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M) c) := by
  let _ : Algebra M (RelativeAdeleRing K M) :=
    relativeAdeleRingIntermediateAlgebra K M
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (RelativeIdeleGroup.principalSubgroup K M) c
  rw [relativeIdeleClassBaseChangeMulEquiv_mk, RelativeIdeleGroup.classInclusion_mk]
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup M L)
        (towerRelativeIdeleBaseChangeMulEquiv K M L
          ((towerRelativeIdeleEquiv K M L).symm
            (RelativeIdeleGroup.ideleEmbedding
              (IsScalarTower.toAlgHom K M L) a))) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup M L)
        (RelativeIdeleGroup.inclusion M L
          (relativeIdeleBaseChangeMulEquiv
            (K := K) (L := M) a))
  apply congrArg
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup M L))
  rw [relativeIdeleEmbedding_toAlgHom_unflatten
    (K := K) (M := M) (L := L) a]
  exact towerRelativeIdeleBaseChangeMulEquiv_includeLeft K M L a

theorem
    relativeIdeleClassBaseChange_classEmbedding_toAlgHom
    {K : Type u} {M : Type v} {L : Type w}
    [Field K] [NumberField K]
    [Field M] [NumberField M]
    [Field L] [NumberField L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L]
    (c : RelativeIdeleGroup.ClassGroup K M) :
    _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.classEmbedding
          (IsScalarTower.toAlgHom K M L) c) =
      _root_.ideleClassExtension M L
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M) c) := by
  calc
    _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := K) (L := L)
        (RelativeIdeleGroup.classEmbedding
          (IsScalarTower.toAlgHom K M L) c) =
      _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := M) (L := L)
        (towerRelativeIdeleClassBaseChangeMulEquiv K M L
          ((TowerRelativeIdeleGroup.classGroupEquiv K M L).symm
            (RelativeIdeleGroup.classEmbedding
              (IsScalarTower.toAlgHom K M L) c))) :=
      (relativeIdeleClassBaseChangeMulEquiv_tower K M L _).symm
    _ = _root_.relativeIdeleClassBaseChangeMulEquiv
        (K := M) (L := L)
        (RelativeIdeleGroup.classInclusion M L
          (_root_.relativeIdeleClassBaseChangeMulEquiv
            (K := K) (L := M) c)) := by
      rw [relativeIdeleClassEmbedding_toAlgHom_towerBaseChange
        (K := K) (M := M) (L := L) c]
    _ = _root_.ideleClassExtension M L
        (_root_.relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := M) c) :=
      relativeIdeleClassBaseChangeMulEquiv_classInclusion _

end GlobalClassFieldTheory.Reciprocity.FiniteTowerNormCore
