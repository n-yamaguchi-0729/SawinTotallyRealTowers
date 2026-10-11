/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers

/-!
# Fpqc-local coequalizers of schemes

An fpqc cover detects whether a morphism of schemes is a coequalizer, provided
the asserted coequalizer property holds both over every member of the cover and
over every pairwise overlap.  This is
[Stacks Project, Tag 0BMN](https://stacks.math.columbia.edu/tag/0BMN).
-/

noncomputable section

universe u v

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/--
Let `a, b : X ⟶ Y` be morphisms coequalized by `c : Y ⟶ Z`.  If an fpqc
cover `π i : Zᵢ i ⟶ Z` makes the base change of `c` a coequalizer over every
`Zᵢ i` and every pairwise overlap `Zᵢ i ×_Z Zᵢ j`, then `c` is the
coequalizer of `a` and `b`.
-/
@[stacks 0BMN]
theorem isColimit_cofork_of_fpqc_local
    {X Y Z : Scheme.{u}} {a b : X ⟶ Y} {c : Y ⟶ Z}
    (hc : a ≫ c = b ≫ c)
    {ι : Type v} (Zᵢ : ι → Scheme.{u}) (π : (i : ι) → Zᵢ i ⟶ Z)
    (hπ : Presieve.ofArrows Zᵢ π ∈ fpqcPrecoverage Z)
    (hlocal : ∀ i,
      Nonempty
        (IsColimit
          (Cofork.ofπ
            (f := pullback.map (π i) (a ≫ c) (π i) c
              (𝟙 _) a (𝟙 _) (by simp) (by simp))
            (g := pullback.map (π i) (a ≫ c) (π i) c
              (𝟙 _) b (𝟙 _) (by simp) (by simpa using hc))
            (pullback.fst (π i) c) (by
              simp only [pullback.map, pullback.lift_fst]))))
    (hoverlap : ∀ i j,
      let q : pullback (π i) (π j) ⟶ Z :=
        pullback.fst (π i) (π j) ≫ π i
      Nonempty
        (IsColimit
          (Cofork.ofπ
            (f := pullback.map q (a ≫ c) q c
              (𝟙 _) a (𝟙 _) (by simp) (by simp))
            (g := pullback.map q (a ≫ c) q c
              (𝟙 _) b (𝟙 _) (by simp) (by simpa using hc))
            (pullback.fst q c) (by
              simp only [pullback.map, pullback.lift_fst])))) :
    Nonempty (IsColimit (Cofork.ofπ c hc)) := by
  let : EffectiveEpiFamily Zᵢ π := by
    rw [← Sieve.effectiveEpimorphic_family]
    rw [Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
    intro T
    exact
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
        (Precoverage.generate_mem_toGrothendieck hπ)
  have hπY :
      Presieve.ofArrows
          (fun i => pullback (π i) c)
          (fun i => pullback.snd (π i) c) ∈
        fpqcPrecoverage Y := by
    rw [Presieve.ofArrows_pullback]
    exact fpqcPrecoverage.pullbackArrows_mem c hπ
  let : EffectiveEpiFamily
      (fun i => pullback (π i) c)
      (fun i => pullback.snd (π i) c) := by
    rw [← Sieve.effectiveEpimorphic_family]
    rw [Presieve.EffectiveEpimorphic.iff_forall_isSheafFor_yoneda]
    intro T
    exact
      (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable _).isSheafFor _
        (Precoverage.generate_mem_toGrothendieck hπY)
  let hlocalData (i : ι) := (hlocal i).some
  let hoverlapData (i j : ι) := (hoverlap i j).some
  refine ⟨Cofork.IsColimit.mk' _ fun s => ?_⟩
  let fᵢ (i : ι) :
      pullback (π i) (a ≫ c) ⟶ pullback (π i) c :=
    pullback.map (π i) (a ≫ c) (π i) c
      (𝟙 _) a (𝟙 _) (by simp) (by simp)
  let gᵢ (i : ι) :
      pullback (π i) (a ≫ c) ⟶ pullback (π i) c :=
    pullback.map (π i) (a ≫ c) (π i) c
      (𝟙 _) b (𝟙 _) (by simp) (by simpa using hc)
  have hfgᵢ (i : ι) :
      fᵢ i ≫ (pullback.snd (π i) c ≫ s.π) =
        gᵢ i ≫ (pullback.snd (π i) c ≫ s.π) := by
    simp only [fᵢ, gᵢ, pullback.map, ← Category.assoc,
      pullback.lift_snd]
    rw [Category.assoc, Category.assoc, s.condition]
  let eᵢ (i : ι) : Zᵢ i ⟶ s.pt :=
    Cofork.IsColimit.desc (hlocalData i)
      (pullback.snd (π i) c ≫ s.π) (hfgᵢ i)
  have heᵢ (i : ι) :
      pullback.fst (π i) c ≫ eᵢ i =
        pullback.snd (π i) c ≫ s.π := by
    exact Cofork.IsColimit.π_desc' (hlocalData i) _ _
  have heᵢ_compatible :
      ∀ {W : Scheme.{u}} (i j : ι)
        (rᵢ : W ⟶ Zᵢ i) (rⱼ : W ⟶ Zᵢ j),
        rᵢ ≫ π i = rⱼ ≫ π j →
          rᵢ ≫ eᵢ i = rⱼ ≫ eᵢ j := by
    intro W i j rᵢ rⱼ hr
    let q : pullback (π i) (π j) ⟶ Z :=
      pullback.fst (π i) (π j) ≫ π i
    let mᵢ :
        pullback q c ⟶ pullback (π i) c :=
      pullback.map q c (π i) c
        (pullback.fst (π i) (π j)) (𝟙 _) (𝟙 _)
        (by simp [q]) (by simp)
    let mⱼ :
        pullback q c ⟶ pullback (π j) c :=
      pullback.map q c (π j) c
        (pullback.snd (π i) (π j)) (𝟙 _) (𝟙 _)
        (by
          simpa only [q, Category.comp_id, Category.id_comp] using
            (pullback.condition :
              pullback.fst (π i) (π j) ≫ π i =
                pullback.snd (π i) (π j) ≫ π j))
        (by simp)
    have hleft :
        pullback.fst q c ≫
              (pullback.fst (π i) (π j) ≫ eᵢ i) =
            pullback.snd q c ≫ s.π := by
      calc
        pullback.fst q c ≫
              (pullback.fst (π i) (π j) ≫ eᵢ i) =
            mᵢ ≫ (pullback.fst (π i) c ≫ eᵢ i) := by
              simp only [mᵢ, pullback.map, ← Category.assoc,
                pullback.lift_fst]
        _ = mᵢ ≫ (pullback.snd (π i) c ≫ s.π) := by
              rw [heᵢ i]
        _ = pullback.snd q c ≫ s.π := by
              simp only [mᵢ, pullback.map, ← Category.assoc,
                pullback.lift_snd, Category.comp_id]
    have hright :
        pullback.fst q c ≫
              (pullback.snd (π i) (π j) ≫ eᵢ j) =
            pullback.snd q c ≫ s.π := by
      calc
        pullback.fst q c ≫
              (pullback.snd (π i) (π j) ≫ eᵢ j) =
            mⱼ ≫ (pullback.fst (π j) c ≫ eᵢ j) := by
              simp only [mⱼ, pullback.map, ← Category.assoc,
                pullback.lift_fst]
        _ = mⱼ ≫ (pullback.snd (π j) c ≫ s.π) := by
              rw [heᵢ j]
        _ = pullback.snd q c ≫ s.π := by
              simp only [mⱼ, pullback.map, ← Category.assoc,
                pullback.lift_snd, Category.comp_id]
    have hp :
        pullback.fst (π i) (π j) ≫ eᵢ i =
          pullback.snd (π i) (π j) ≫ eᵢ j := by
      apply Cofork.IsColimit.hom_ext (hoverlapData i j)
      exact hleft.trans hright.symm
    let r : W ⟶ pullback (π i) (π j) :=
      pullback.lift rᵢ rⱼ hr
    calc
      rᵢ ≫ eᵢ i =
          r ≫ (pullback.fst (π i) (π j) ≫ eᵢ i) := by
            simp only [r, ← Category.assoc, pullback.lift_fst]
      _ = r ≫ (pullback.snd (π i) (π j) ≫ eᵢ j) := by
            rw [hp]
      _ = rⱼ ≫ eᵢ j := by
            simp only [r, ← Category.assoc, pullback.lift_snd]
  let l : Z ⟶ s.pt :=
    EffectiveEpiFamily.desc Zᵢ π eᵢ heᵢ_compatible
  have hlᵢ (i : ι) : π i ≫ l = eᵢ i :=
    EffectiveEpiFamily.fac Zᵢ π eᵢ heᵢ_compatible i
  have hl : c ≫ l = s.π := by
    apply EffectiveEpiFamily.hom_ext
      (fun i => pullback (π i) c)
      (fun i => pullback.snd (π i) c)
    intro i
    calc
      pullback.snd (π i) c ≫ c ≫ l =
          pullback.fst (π i) c ≫ π i ≫ l := by
            simp only [← Category.assoc, pullback.condition]
      _ = pullback.fst (π i) c ≫ eᵢ i := by
            rw [hlᵢ i]
      _ = pullback.snd (π i) c ≫ s.π := heᵢ i
  refine ⟨l, hl, ?_⟩
  intro m hm
  change Z ⟶ s.pt at m
  change c ≫ m = s.π at hm
  apply EffectiveEpiFamily.hom_ext Zᵢ π
  intro i
  apply Cofork.IsColimit.hom_ext (hlocalData i)
  calc
    pullback.fst (π i) c ≫ π i ≫ m =
        pullback.snd (π i) c ≫ c ≫ m := by
          simp only [← Category.assoc, pullback.condition]
    _ = pullback.snd (π i) c ≫ s.π := by
          rw [hm]
    _ = pullback.fst (π i) c ≫ eᵢ i := (heᵢ i).symm
    _ = pullback.fst (π i) c ≫ π i ≫ l := by
          rw [hlᵢ i]

end AlgebraicGeometry.Scheme
