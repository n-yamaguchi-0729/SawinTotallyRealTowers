/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleClassBaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.EmbeddingNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.IdeleNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.BaseChange
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.ClassGroup
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisClassNorm
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.RelativeNormComparison
public import Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalCore

/-!
# Relative and ordinary idele-class norms

The determinant norm on relative ideles and the ordinary idele norm give
the same map after the canonical scalar-extension equivalence
`C(𝔸_K ⊗_K L) ≃ C_L`.  This comparison lets the cohomological results
proved in relative coordinates be stated with the usual norm
`N_{L/K} : C_L → C_K`.
-/



@[expose] public section

open scoped NumberField
open NumberField

noncomputable section

namespace RelativeIdeleGroup

universe u v w

variable
    {K : Type u} {L : Type v} {M : Type w}
    [Field K] [NumberField K]
    [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]

/-- A field embedding into an ambient finite extension, descended from
relative ideles to the existing relative idele class groups. -/
noncomputable def classEmbedding
    (f : L →ₐ[K] M) :
    RelativeIdeleGroup.ClassGroup K L →*
      RelativeIdeleGroup.ClassGroup K M :=
  QuotientGroup.map
    (RelativeIdeleGroup.principalSubgroup K L)
    (RelativeIdeleGroup.principalSubgroup K M)
    (RelativeIdeleGroup.ideleEmbedding f)
    (by
      rintro _ ⟨x, rfl⟩
      refine ⟨Units.map f x, ?_⟩
      apply Units.ext
      rfl)

omit [FiniteDimensional K L] [FiniteDimensional K M] in
@[simp]
theorem classEmbedding_mk
    (f : L →ₐ[K] M)
    (a : RelativeIdeleGroup K L) :
    classEmbedding f
        (QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K L) a) =
      QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M)
        (RelativeIdeleGroup.ideleEmbedding f a) :=
  rfl

variable [Algebra L M] [IsScalarTower K L M] [IsGalois K M]

local instance fixingSubextensionQuotientFintype :
    Fintype
      ((M ≃ₐ[K] M) ⧸
        RelativeIdeleGroup.fixingSubextension
          (K := K) (L := L) (M := M)) :=
  Fintype.ofFinite _

/-- The embedded-subextension norm formula after descent to relative
idele classes.  No normality of `L / K` is assumed. -/
theorem classInclusion_ideleClassNorm_eq_prod_embeddings
    (c : RelativeIdeleGroup.ClassGroup K L) :
    RelativeIdeleGroup.classInclusion K M
        (RelativeIdeleGroup.classNorm K L c) =
      ∏ f : L →ₐ[K] M,
        RelativeIdeleGroup.classEmbedding f c := by
  refine QuotientGroup.induction_on c ?_
  intro a
  rw [← QuotientGroup.mk'_apply (RelativeIdeleGroup.principalSubgroup K L) a,
    RelativeIdeleGroup.classNorm_mk, RelativeIdeleGroup.classInclusion_mk]
  change
    QuotientGroup.mk'
        (RelativeIdeleGroup.principalSubgroup K M)
        (RelativeIdeleGroup.inclusion K M
          (RelativeIdeleGroup.norm K L a)) =
      ∏ f : L →ₐ[K] M,
        QuotientGroup.mk'
          (RelativeIdeleGroup.principalSubgroup K M)
          (RelativeIdeleGroup.ideleEmbedding f a)
  rw [RelativeIdeleGroup.inclusion_norm_eq_prod_embeddings]
  exact map_prod
    (QuotientGroup.mk'
      (RelativeIdeleGroup.principalSubgroup K M))
    (fun f : L →ₐ[K] M =>
      RelativeIdeleGroup.ideleEmbedding f a)
    Finset.univ

/-- Coset form of the embedded-subextension norm formula on relative
idele classes. -/
theorem classInclusion_ideleClassNorm_eq_prod_galoisCosets
    (c : RelativeIdeleGroup.ClassGroup K L) :
    RelativeIdeleGroup.classInclusion K M
        (RelativeIdeleGroup.classNorm K L c) =
      ∏ q :
          (M ≃ₐ[K] M) ⧸
            RelativeIdeleGroup.fixingSubextension
              (K := K) (L := L) (M := M),
        RelativeIdeleGroup.classEmbedding
          (RelativeIdeleGroup.cosetEquivEmbedding q) c := by
  calc
    RelativeIdeleGroup.classInclusion K M
        (RelativeIdeleGroup.classNorm K L c) =
        ∏ f : L →ₐ[K] M,
          RelativeIdeleGroup.classEmbedding f c :=
      RelativeIdeleGroup.classInclusion_ideleClassNorm_eq_prod_embeddings c
    _ =
        ∏ q :
            (M ≃ₐ[K] M) ⧸
              RelativeIdeleGroup.fixingSubextension
                (K := K) (L := L) (M := M),
          RelativeIdeleGroup.classEmbedding
            (RelativeIdeleGroup.cosetEquivEmbedding q) c := by
      exact
        ((RelativeIdeleGroup.cosetEquivEmbedding
          (K := K) (L := L) (M := M)).prod_comp
            (fun f ↦ RelativeIdeleGroup.classEmbedding f c)).symm

end RelativeIdeleGroup

variable
    {K L : Type*}
    [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L]

omit [IsGalois K L] in
/-- The ordinary and relative presentations define the same norm subgroup
of `C_K`. -/
theorem ordinaryIdeleClassNorm_range_eq_relative :
    (_root_.ideleClassNorm K L).range =
      (RelativeIdeleGroup.classNorm K L).range := by
  ext c
  constructor
  · rintro ⟨d, rfl⟩
    refine
      ⟨(relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L)).symm d, ?_⟩
    simpa using
      (ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
        (K := K) (L := L)
        ((relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L)).symm d)).symm
  · rintro ⟨d, rfl⟩
    exact
      ⟨relativeIdeleClassBaseChangeMulEquiv
          (K := K) (L := L) d,
        ordinaryIdeleClassNorm_relativeIdeleClassBaseChange
          (K := K) (L := L) d⟩
