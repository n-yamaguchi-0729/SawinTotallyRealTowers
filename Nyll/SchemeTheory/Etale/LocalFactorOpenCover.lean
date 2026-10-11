/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.Etale.IntegralRefinement
import Mathlib.AlgebraicGeometry.Cover.Open
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Local factors on an actual open cover

Local lifts through a base-changed target map to lifts through the original
target by the pullback projection. Local lifts on open-cover charts become
local lifts on the glued source by taking their actual open images. No
agreement between the different local lifts is required.
-/

noncomputable section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- A local lift through a base-changed target gives a local lift through
the original target after composing the source map with the base change. -/
theorem Scheme.Hom.ZariskiLocallyFactorsThrough.of_pullback_snd
    {S U X Y : Scheme.{u}} (g : S ⟶ Y) (f : U ⟶ X) (k : Y ⟶ X)
    (hlocal : g.ZariskiLocallyFactorsThrough (pullback.snd f k)) :
    (g ≫ k).ZariskiLocallyFactorsThrough f := by
  intro x
  obtain ⟨W, hx, a, ha⟩ := hlocal x
  let p : pullback f k ⟶ U := pullback.fst f k
  let q : pullback f k ⟶ Y := pullback.snd f k
  refine ⟨W, hx, a ≫ p, ?_⟩
  calc
    (a ≫ p) ≫ f = a ≫ (p ≫ f) := Category.assoc a p f
    _ = a ≫ (q ≫ k) :=
      congrArg (fun z : pullback f k ⟶ X => a ≫ z) (pullback.condition (f := f) (g := k))
    _ = (a ≫ q) ≫ k := (Category.assoc a q k).symm
    _ = (W.ι ≫ g) ≫ k := congrArg (fun z : W.toScheme ⟶ Y => z ≫ k) ha
    _ = W.ι ≫ (g ≫ k) := Category.assoc W.ι g k

private theorem local_factor_on_open_image
    {A T U X : Scheme.{u}} (g : T ⟶ X) (f : U ⟶ X)
    (i : A ⟶ T) [IsOpenImmersion i] (a : A ⟶ U)
    (ha : a ≫ f = i ≫ g) (x : A) :
    ∃ V : T.Opens, i x ∈ V ∧ ∃ b : V.toScheme ⟶ U, b ≫ f = V.ι ≫ g := by
  let V : T.Opens := i.opensRange
  have hV : Set.range V.ι ⊆ Set.range i := by
    rw [Scheme.Opens.range_ι]
    exact Set.Subset.rfl
  let l : V.toScheme ⟶ A := IsOpenImmersion.lift i V.ι hV
  refine ⟨V, ⟨x, rfl⟩, l ≫ a, ?_⟩
  calc
    (l ≫ a) ≫ f = l ≫ (a ≫ f) := Category.assoc l a f
    _ = l ≫ (i ≫ g) := congrArg (fun z : A ⟶ X => l ≫ z) ha
    _ = (l ≫ i) ≫ g := (Category.assoc l i g).symm
    _ = V.ι ≫ g :=
      congrArg (fun z : V.toScheme ⟶ T => z ≫ g) (IsOpenImmersion.lift_fac i V.ι hV)

/-- Actual local factors on all charts of an open cover give actual local
factors on the source. The neighborhoods are their open images. -/
theorem Scheme.Hom.ZariskiLocallyFactorsThrough.of_openCover
    {T U X : Scheme.{u}} (g : T ⟶ X) (f : U ⟶ X)
    (𝒰 : Scheme.OpenCover.{v} T)
    (hlocal : ∀ i : 𝒰.I₀, (𝒰.f i ≫ g).ZariskiLocallyFactorsThrough f) :
    g.ZariskiLocallyFactorsThrough f := by
  intro y
  obtain ⟨i, x, rfl⟩ := 𝒰.exists_eq y
  obtain ⟨W, hx, a, ha⟩ := hlocal i x
  let j : W.toScheme ⟶ T := W.ι ≫ 𝒰.f i
  have hj : a ≫ f = j ≫ g := ha.trans (Category.assoc W.ι (𝒰.f i) g).symm
  have : IsOpenImmersion j := inferInstance
  obtain ⟨V, hV, b, hb⟩ := local_factor_on_open_image g f j a hj ⟨x, hx⟩
  have hpoint : j (⟨x, hx⟩ : W.toScheme) = 𝒰.f i x :=
    Scheme.Hom.comp_apply W.ι (𝒰.f i) ⟨x, hx⟩
  exact ⟨V, hpoint ▸ hV, b, hb⟩

/-- Local factorization through a disjoint union refines near each source
point to an actual factor through one member of the family. -/
theorem Scheme.Hom.ZariskiLocallyFactorsThrough.exists_sigma_factor
    {X Y : Scheme.{u}} {I : Type u} (V : I → Scheme.{u})
    (f : ∀ i : I, V i ⟶ X) (q : Y ⟶ X)
    (hq : q.ZariskiLocallyFactorsThrough (Sigma.desc f)) (y : Y) :
    ∃ (W : Y.Opens), y ∈ W ∧ ∃ (i : I) (b : W.toScheme ⟶ V i),
      b ≫ f i = W.ι ≫ q := by
  obtain ⟨U, hyU, a, ha⟩ := hq y
  let yU : U.toScheme := ⟨y, hyU⟩
  obtain ⟨i, v, hv⟩ := (AlgebraicGeometry.sigmaOpenCover V).exists_eq (a yU)
  let j : V i ⟶ ∐ V := Sigma.ι V i
  let D : U.toScheme.Opens := a ⁻¹ᵁ j.opensRange
  have hyD : yU ∈ D := ⟨v, hv⟩
  let k : D.toScheme ⟶ Y := D.ι ≫ U.ι
  have : IsOpenImmersion k := inferInstance
  let W : Y.Opens := k.opensRange
  have hRange : Set.range (D.ι ≫ a) ⊆ Set.range j := by
    rintro x ⟨t, rfl⟩
    rw [Scheme.Hom.comp_apply]
    exact t.property
  let l : D.toScheme ⟶ V i := IsOpenImmersion.lift j (D.ι ≫ a) hRange
  have hl : l ≫ j = D.ι ≫ a := IsOpenImmersion.lift_fac j (D.ι ≫ a) hRange
  let b : W.toScheme ⟶ V i := k.isoOpensRange.inv ≫ l
  have hyW : y ∈ W := by
    refine ⟨⟨yU, hyD⟩, ?_⟩
    exact Scheme.Hom.comp_apply D.ι U.ι ⟨yU, hyD⟩
  refine ⟨W, hyW, i, b, ?_⟩
  have hj : j ≫ Sigma.desc f = f i := Sigma.ι_comp_desc f i
  have hlq : l ≫ f i = k ≫ q := by
    calc
      l ≫ f i = l ≫ (j ≫ Sigma.desc f) := congrArg (fun t => l ≫ t) hj.symm
      _ = (l ≫ j) ≫ Sigma.desc f := (Category.assoc _ _ _).symm
      _ = (D.ι ≫ a) ≫ Sigma.desc f := congrArg (fun t => t ≫ Sigma.desc f) hl
      _ = D.ι ≫ (U.ι ≫ q) := by rw [Category.assoc, ha]
      _ = k ≫ q := (Category.assoc D.ι U.ι q).symm
  calc
    b ≫ f i = k.isoOpensRange.inv ≫ (l ≫ f i) := Category.assoc _ _ _
    _ = k.isoOpensRange.inv ≫ (k ≫ q) := congrArg (fun t => k.isoOpensRange.inv ≫ t) hlq
    _ = (k.isoOpensRange.inv ≫ k) ≫ q := (Category.assoc _ _ _).symm
    _ = W.ι ≫ q := congrArg (fun t => t ≫ q) k.isoOpensRange_inv_comp

end AlgebraicGeometry
