/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Cover.Open
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Nyll.SchemeTheory.FiniteEtale.Basic

/-!
# Pullback squares for coproducts of schemes

For an arbitrary small family of morphisms, the square formed by a component and
the corresponding coproduct inclusions is cartesian. The proof uses the open
cover of a coproduct and the equality criterion for points in its components.

Consequently, any property Zariski local on the target holds for the coproduct
map exactly when it holds on every component. In particular, a coproduct of
finite étale morphisms is finite étale, with no finiteness assumption on the
index type.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

variable {ι : Type v} [Small.{u} ι] {X Y : ι → Scheme.{u}}
  (f : ∀ i, X i ⟶ Y i)

/-- A coproduct map restricts to the given morphism on each target component. -/
lemma isPullback_sigmaι_sigmaMap (i : ι) :
    IsPullback (f i) (Sigma.ι X i) (Sigma.ι Y i) (Limits.Sigma.map f) := by
  refine IsOpenImmersion.isPullback _ _ _ _ (Sigma.ι_map f i) ?_
  ext x
  have hmap (j : ι) (z : X j) :
      Limits.Sigma.map f (Sigma.ι X j z) = Sigma.ι Y j (f j z) :=
    congrArg (fun (a : X j ⟶ ∐ Y) ↦ a z) (Sigma.ι_map f j)
  constructor
  · rintro ⟨y, hy⟩
    have hcover : ∃ (j : ι) (z : X j), Sigma.ι X j z = x :=
      (sigmaOpenCover X).exists_eq x
    obtain ⟨j, z, rfl⟩ := hcover
    have hij : i = j :=
      congrArg Sigma.fst ((sigmaι_eq_iff Y i j y (f j z)).mp (hy.trans (hmap j z)))
    subst j
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨f i z, (hmap i z).symm⟩

/-- Properties local on the target can be checked componentwise on a coproduct map. -/
lemma IsZariskiLocalAtTarget.sigmaMap_iff (P : MorphismProperty Scheme.{u})
    [IsZariskiLocalAtTarget P] : P (Limits.Sigma.map f) ↔ ∀ i, P (f i) := by
  constructor
  · intro h i
    exact IsZariskiLocalAtTarget.of_isPullback (isPullback_sigmaι_sigmaMap f i).flip h
  · intro h
    apply IsZariskiLocalAtTarget.of_openCover (sigmaOpenCover Y)
    intro i
    change P (pullback.snd (Limits.Sigma.map f) (Sigma.ι Y i))
    rw [← (isPullback_sigmaι_sigmaMap f i).flip.isoPullback_inv_snd]
    exact (P.cancel_left_of_respectsIso _ _).mpr (h i)

/-- An arbitrary small coproduct of finite étale morphisms is finite étale. -/
lemma IsFiniteEtale.sigmaMap [∀ i, IsFiniteEtale (f i)] :
    IsFiniteEtale (Limits.Sigma.map f) :=
  (IsZariskiLocalAtTarget.sigmaMap_iff f
    (show MorphismProperty Scheme.{u} from @IsFiniteEtale)).mpr fun _ ↦ inferInstance

end AlgebraicGeometry
