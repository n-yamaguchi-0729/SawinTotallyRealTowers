/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Gluing.RelativeOverlap
import Nyll.SchemeTheory.FiniteEtale.Basic
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-!
# Finiteness properties of actual gluing overlaps

Finite-etale models over compact open charts have compact pairwise and
triple overlap objects. Their maps to the ambient quasi-separated base
are quasi-compact and locally of finite type; they are not asserted to be
finite over that whole base.
-/

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Cover

variable {S : Scheme.{u}} (𝒰 : S.OpenCover)
variable (A : 𝒰.I₀ → Over S) (V : 𝒰.I₀ × 𝒰.I₀ → Over S)
variable (d : ∀ i j : 𝒰.I₀, V (i, j) ⟶ A i)
variable (y : ∀ i : 𝒰.I₀, (A i).left ⟶ 𝒰.X i)
variable (ℓ : ∀ i j : 𝒰.I₀, (V (i, j)).left ⟶ 𝒰.X j)
variable (hV : ∀ i j : 𝒰.I₀, IsPullback (d i j).left (ℓ i j) (y i ≫ 𝒰.f i) (𝒰.f j))

include hV in
/-- Actual pairwise overlaps of compact finite-etale chart models are compact. -/
theorem relativeOverlap_compactSpace [QuasiSeparatedSpace S]
    [∀ i : 𝒰.I₀, CompactSpace (𝒰.X i)] [∀ i : 𝒰.I₀, IsFiniteEtale (y i)]
    (i j : 𝒰.I₀) : CompactSpace (V (i, j)).left := by
  have : CompactSpace (A i).left := QuasiCompact.compactSpace_of_compactSpace (y i)
  have : QuasiCompact (y i ≫ 𝒰.f i) := inferInstance
  have : QuasiCompact (ℓ i j) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) (hV i j) inferInstance
  exact QuasiCompact.compactSpace_of_compactSpace (ℓ i j)

include hV in
/-- The actual overlap structural morphism is locally of finite type. -/
theorem relativeOverlap_locallyOfFiniteType
    [∀ i : 𝒰.I₀, IsFiniteEtale (y i)]
    (hy : ∀ i : 𝒰.I₀, y i ≫ 𝒰.f i = (A i).hom) (i j : 𝒰.I₀) :
    LocallyOfFiniteType (V (i, j)).hom := by
  have : IsOpenImmersion (d i j).left :=
    relativeOverlapInclusion_isOpenImmersion 𝒰 A V d y ℓ hV i j
  have : LocallyOfFiniteType (A i).hom := by rw [← hy i]; infer_instance
  rw [← Over.w (d i j)]
  infer_instance

include hV in
/-- Actual triple intersections are compact; only quasi-separatedness of
the ambient base is needed in addition to the compact local chart models. -/
theorem relativeTriple_compactSpace [QuasiSeparatedSpace S]
    [∀ i : 𝒰.I₀, CompactSpace (𝒰.X i)] [∀ i : 𝒰.I₀, IsFiniteEtale (y i)]
    (i j k : 𝒰.I₀) : CompactSpace (relativeTriple 𝒰 A V d i j k).left := by
  have : CompactSpace (V (i, j)).left := relativeOverlap_compactSpace 𝒰 A V d y ℓ hV i j
  have : CompactSpace (V (i, k)).left := relativeOverlap_compactSpace 𝒰 A V d y ℓ hV i k
  have : QuasiSeparatedSpace (𝒰.X i) := quasiSeparatedSpace_of_quasiSeparated (𝒰.f i)
  have : QuasiSeparatedSpace (A i).left := quasiSeparatedSpace_of_quasiSeparated (y i)
  have : QuasiCompact (d i k).left := inferInstance
  have hPB := (IsPullback.of_hasPullback (d i j) (d i k)).map (Over.forget S)
  have : QuasiCompact (pullback.fst (d i j) (d i k)).left :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hPB.flip
      (inferInstanceAs (QuasiCompact (d i k).left))
  exact QuasiCompact.compactSpace_of_compactSpace (pullback.fst (d i j) (d i k)).left

include hV in
/-- The actual triple-overlap structural morphism is locally of finite type. -/
theorem relativeTriple_locallyOfFiniteType
    [∀ i : 𝒰.I₀, IsFiniteEtale (y i)]
    (hy : ∀ i : 𝒰.I₀, y i ≫ 𝒰.f i = (A i).hom) (i j k : 𝒰.I₀) :
    LocallyOfFiniteType (relativeTriple 𝒰 A V d i j k).hom := by
  have : LocallyOfFiniteType (V (i, j)).hom :=
    relativeOverlap_locallyOfFiniteType 𝒰 A V d y ℓ hV hy i j
  have : IsOpenImmersion (d i k).left :=
    relativeOverlapInclusion_isOpenImmersion 𝒰 A V d y ℓ hV i k
  have hPB := (IsPullback.of_hasPullback (d i j) (d i k)).map (Over.forget S)
  have : IsOpenImmersion (pullback.fst (d i j) (d i k)).left :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) hPB.flip
      (inferInstanceAs (IsOpenImmersion (d i k).left))
  rw [← Over.w (pullback.fst (d i j) (d i k))]
  infer_instance

end AlgebraicGeometry.Scheme.Cover
