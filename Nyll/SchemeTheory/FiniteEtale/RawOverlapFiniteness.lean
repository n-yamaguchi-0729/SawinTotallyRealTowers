/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Gluing.RecoveredPullback
import Nyll.SchemeTheory.Pi1.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Actual finiteness hypotheses for raw overlap Hom descent

The local models are finite etale over affine charts. Their raw overlaps
are open subschemes of affine models, and are compact because the original
base is quasi-separated. Their ambient maps are locally finitely presented.
No overlap is claimed finite over the whole ambient base.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Cover

variable {S : Scheme.{u}} (𝒰 : S.OpenCover)
    (M : ∀ i : 𝒰.I₀, Over (𝒰.X i))
    [∀ i : 𝒰.I₀, IsAffine (𝒰.X i)]
    [∀ i : 𝒰.I₀, IsFiniteEtale (M i).hom]

/-- Every actual local covering scheme is affine. -/
theorem rawLocalModel_isAffine (i : 𝒰.I₀) : IsAffine (M i).left :=
  isAffine_of_isAffineHom (M i).hom

/-- Raw overlaps are compact over a quasi-separated ambient base. -/
theorem rawOverlap_compactSpace [QuasiSeparatedSpace S] (i j : 𝒰.I₀) :
    CompactSpace (gluingOverlapOver 𝒰 M (i, j)).left := by
  have : IsAffine (M i).left := rawLocalModel_isAffine 𝒰 M i
  have : QuasiCompact (𝒰.f j) := inferInstance
  exact inferInstanceAs (CompactSpace
    (pullback ((M i).hom ≫ 𝒰.f i) (𝒰.f j) : Scheme.{u}))

/-- The raw overlap ambient morphism is quasi-compact. -/
theorem rawOverlap_quasiCompact [QuasiSeparatedSpace S] (i j : 𝒰.I₀) :
    QuasiCompact (gluingOverlapOver 𝒰 M (i, j)).hom := by
  have : CompactSpace (gluingOverlapOver 𝒰 M (i, j)).left :=
    rawOverlap_compactSpace 𝒰 M i j
  infer_instance

/-- A raw overlap is an open subscheme of an affine local model, so its
ambient structural map is quasi-separated. -/
theorem rawOverlap_quasiSeparated (i j : 𝒰.I₀) :
    QuasiSeparated (gluingOverlapOver 𝒰 M (i, j)).hom := by
  have : IsAffine (M i).left := rawLocalModel_isAffine 𝒰 M i
  let f : (gluingOverlapOver 𝒰 M (i, j)).left ⟶ (M i).left :=
    pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j)
  have hq : QuasiSeparated (𝒰.f j) := inferInstance
  have hf : QuasiSeparated f :=
    AlgebraicGeometry.quasiSeparated_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback ((M i).hom ≫ 𝒰.f i) (𝒰.f j)).flip hq
  have : QuasiSeparatedSpace (gluingOverlapOver 𝒰 M (i, j)).left :=
    @quasiSeparatedSpace_of_quasiSeparated _ _ f _ hf
  infer_instance

omit [∀ i : 𝒰.I₀, IsAffine (𝒰.X i)] in
/-- The raw overlap ambient map is locally finitely presented: it is an
open immersion followed by a finite-etale map and an open chart map. -/
theorem rawOverlap_locallyOfFinitePresentation (i j : 𝒰.I₀) :
    LocallyOfFinitePresentation (gluingOverlapOver 𝒰 M (i, j)).hom := by
  change LocallyOfFinitePresentation
    (pullback.fst ((M i).hom ≫ 𝒰.f i) (𝒰.f j) ≫ ((M i).hom ≫ 𝒰.f i))
  infer_instance

end AlgebraicGeometry.Scheme.Cover
