/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Naganori Yamaguchi (assisted by OpenAI Codex)
-/
import Mathlib.AlgebraicGeometry.Gluing
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Nyll.SchemeTheory.FiniteEtale.Basic

/-!
The range and open-immersion lifting arguments below adapt Christian Merten's
`RelativeGluingData.preimage_toBase_eq_range_ι` and
`RelativeGluingData.isPullback_natTrans_ι_toBase` from Mathlib:
https://github.com/leanprover-community/mathlib4/blob/065356127b1dc0016f66b7283ce0ce2c4055aa55/Mathlib/AlgebraicGeometry/RelativeGluing.lean
The present construction works with actual pairwise overlaps of arbitrary open
covers, without a locally directed structure on the cover index.
-/

noncomputable section
universe u
open CategoryTheory Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.GlueData

/-- Gluing finite étale pieces over their actual pairwise overlaps constructs
a finite étale scheme over the covered base, together with all local pullback squares. -/
theorem exists_finiteEtale_gluedToBase
    (D : Scheme.GlueData.{u}) (S : Scheme.{u})
    (U : D.J → Scheme.{u}) (u : ∀ i, U i ⟶ S)
    [∀ i, IsOpenImmersion (u i)]
    (hu : ∀ s : S, ∃ (i : D.J) (x : U i), u i x = s)
    (y : ∀ i, D.U i ⟶ U i) [∀ i, IsFiniteEtale (y i)]
    (ℓ : ∀ i j, D.V (i, j) ⟶ U j)
    (hV : ∀ i j, IsPullback (D.f i j) (ℓ i j) (y i ≫ u i) (u j))
    (ht : ∀ i j, D.t i j ≫ D.f j i ≫ y j = ℓ i j) :
    ∃ q : D.glued ⟶ S, IsFiniteEtale q ∧
      ∀ i, IsPullback (y i) (D.ι i) (u i) q := by
  have hcompat (a : D.J × D.J) :
      D.diagram.fst a ≫ (y a.1 ≫ u a.1) =
        D.diagram.snd a ≫ (y a.2 ≫ u a.2) := by
    rcases a with ⟨i, j⟩
    change D.f i j ≫ (y i ≫ u i) = (D.t i j ≫ D.f j i) ≫ (y j ≫ u j)
    rw [(hV i j).w, ← ht i j]
    simp only [Category.assoc]
  let q : D.glued ⟶ S :=
    Multicoequalizer.desc D.diagram S (fun i ↦ y i ≫ u i) hcompat
  have hq (i : D.J) : D.ι i ≫ q = y i ≫ u i :=
    Multicoequalizer.π_desc D.diagram S (fun i ↦ y i ≫ u i) hcompat i
  have hrange (i : D.J) : q ⁻¹' Set.range (u i) = Set.range (D.ι i) := by
    ext x
    constructor
    · rintro ⟨ui, hui⟩
      obtain ⟨j, xj, rfl⟩ := D.ι_jointly_surjective x
      have heq : (y j ≫ u j) xj = u i ui := by
        rw [← hq j, Scheme.Hom.comp_apply]
        exact hui.symm
      obtain ⟨z, hz, _⟩ := Scheme.exists_preimage_of_isPullback (hV j i) xj ui heq
      refine ⟨(D.t j i ≫ D.f i j) z, ?_⟩
      rw [← Scheme.Hom.comp_apply, Category.assoc, D.glue_condition,
        Scheme.Hom.comp_apply, hz]
    · rintro ⟨xi, rfl⟩
      refine ⟨y i xi, ?_⟩
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hq i]
  have hPB (i : D.J) : IsPullback (y i) (D.ι i) (u i) q := by
    refine ⟨⟨(hq i).symm⟩, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
    · intro s
      apply IsOpenImmersion.lift (D.ι i) s.snd
      rw [← hrange i]
      rintro x ⟨z, rfl⟩
      refine ⟨s.fst z, ?_⟩
      exact congrArg (fun g : s.pt ⟶ S ↦ g z) s.condition
    · intro s
      apply (cancel_mono (u i)).mp
      rw [Category.assoc, ← hq i, IsOpenImmersion.lift_fac_assoc, s.condition]
    · intro s
      exact IsOpenImmersion.lift_fac _ _ _
    · intro s m _ hm
      apply (cancel_mono (D.ι i)).mp
      rw [hm, IsOpenImmersion.lift_fac]
  let 𝒰 : S.OpenCover :=
    { I₀ := D.J
      X := U
      f := u
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        exact ⟨hu, inferInstance⟩ }
  have hLocal : IsZariskiLocalAtTarget (@IsFiniteEtale : MorphismProperty Scheme.{u}) :=
    ((HasAffineProperty.iff
      (P := (@IsFiniteEtale : MorphismProperty Scheme.{u}))
      (Q := affineAnd RingHom.FiniteEtale)).mp inferInstance).1
  refine ⟨q, IsZariskiLocalAtTarget.of_openCover (P := @IsFiniteEtale) 𝒰 ?_, hPB⟩
  intro i
  change IsFiniteEtale (Limits.pullback.snd q (u i))
  rw [← (hPB i).flip.isoPullback_inv_snd]
  let : MorphismProperty.RespectsIso (@IsFiniteEtale : MorphismProperty Scheme.{u}) :=
    hLocal.toRespects
  exact (MorphismProperty.cancel_left_of_respectsIso (@IsFiniteEtale : MorphismProperty Scheme.{u})
    (hPB i).flip.isoPullback.inv (y i)).mpr inferInstance

end AlgebraicGeometry.Scheme.GlueData
