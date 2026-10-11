/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_AlgebraicGeometry_exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing_of_isNoetherianRing.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/


import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
import Nyll.SchemeTheory.FiniteEtale.isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper
import Nyll.SchemeTheory.Morphisms.ProperHenselianClopenLift

/-!
# Finite etale sections over an arbitrary proper Henselian family

The clopen image of a section on the closed fibre lifts to a clopen subscheme
of the finite etale cover. Its projection is an isomorphism because it is an
isomorphism on the closed fibre. The original FLT section construction is
adapted here to the unrestricted Henselian clopen-lifting theorem, removing
the Noetherian hypothesis on the base.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem etale_of_section {X Y : Scheme.{u}} (π : Y ⟶ X) [Etale π] (s : X ⟶ Y) (hs : s ≫ π =
  𝟙 X) :
    Etale s := by
  have : Etale (s ≫ π) := by rw [hs]; infer_instance
  exact MorphismProperty.of_postcomp (W := @Etale) (W' := @Etale) s π ‹_› this

private theorem isClosedImmersion_of_section {X Y : Scheme.{u}} (π : Y ⟶ X) [IsSeparated π] (s : X
  ⟶ Y)
    (hs : s ≫ π = 𝟙 X) : IsClosedImmersion s := by
  have : IsClosedImmersion (s ≫ π) := by rw [hs]; infer_instance
  exact IsClosedImmersion.of_comp s π

private theorem isOpenImmersion_of_section {X Y : Scheme.{u}} (π : Y ⟶ X) [Etale π] (s : X ⟶ Y)
    (hs : s ≫ π = 𝟙 X) : IsOpenImmersion s := by
  have : Etale s := etale_of_section π s hs
  have : IsSplitMono s := IsSplitMono.mk' ⟨π, hs⟩
  exact IsOpenImmersion.of_flat_of_mono s

private theorem isClosedImmersion_ι_of_isClosed {Y : Scheme.{u}} (U : Y.Opens) (hU : IsClosed (U :
  Set Y)) :
    IsClosedImmersion U.ι :=
  IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hU)

private theorem isIso_pullback_snd_of_preimage_eq
    {Xk X Y : Scheme.{u}} (ι : Xk ⟶ X) (π : Y ⟶ X) (U : Y.Opens) (V₀ : (pullback π ι).Opens)
    (hV₀ : IsIso (V₀.ι ≫ pullback.snd π ι)) (hUV : (pullback.fst π ι) ⁻¹ᵁ U = V₀) :
    IsIso (pullback.snd (U.ι ≫ π) ι) := by
  let e₂ := pullbackRightPullbackFstIso π ι U.ι
  have h1 : pullback.snd (U.ι ≫ π) ι = e₂.inv ≫ pullback.snd U.ι (pullback.fst π ι) ≫ pullback.snd
    π ι := by
    rw [← pullbackRightPullbackFstIso_hom_snd, Iso.inv_hom_id_assoc]
  have h2 : pullback.snd U.ι (pullback.fst π ι) =
      (pullbackSymmetry _ _).hom ≫ pullback.fst (pullback.fst π ι) U.ι := by
    rw [pullbackSymmetry_hom_comp_fst]
  have h3 : pullback.fst (pullback.fst π ι) U.ι =
      (pullbackRestrictIsoRestrict (pullback.fst π ι) U).hom ≫ ((pullback.fst π ι) ⁻¹ᵁ U).ι := by
    rw [pullbackRestrictIsoRestrict_hom_ι]
  have h4 : ((pullback.fst π ι) ⁻¹ᵁ U).ι = ((pullback π ι).isoOfEq hUV).hom ≫ V₀.ι := by
    rw [Scheme.isoOfEq_hom_ι]
  rw [h1, h2, h3, h4]
  simp only [Category.assoc]
  have : IsIso (V₀.ι ≫ pullback.snd π ι) := hV₀
  infer_instance


/-- A section on the actual closed fibre of a finite etale cover of a proper
scheme over any Henselian local ring extends to a section of the cover. -/
theorem exists_section_of_isFinite_of_etale_of_isProper_of_henselianLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {X Y : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (π : Y ⟶ X) [IsFinite π] [AlgebraicGeometry.Etale π]
    (s₀ : pullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ⟶ Y)
    (hs₀ : s₀ ≫ π = pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) :
    ∃ s : X ⟶ Y, s ≫ π = 𝟙 X ∧
      pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) ≫ s = s₀ := by
  have hcond : s₀ ≫ π = 𝟙 _ ≫ (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue
    R)))) := by rw [hs₀, Category.id_comp]
  have ht₀ : pullback.lift s₀ (𝟙 _) hcond ≫ pullback.snd π (pullback.fst f (Spec.map
    (CommRingCat.ofHom (IsLocalRing.residue R)))) = 𝟙 _ := pullback.lift_snd _ _ _
  have ht₀fst : pullback.lift s₀ (𝟙 _) hcond ≫ pullback.fst π (pullback.fst f (Spec.map
    (CommRingCat.ofHom (IsLocalRing.residue R)))) = s₀ := pullback.lift_fst _ _ _
  have hopen : IsOpenImmersion (pullback.lift s₀ (𝟙 _) hcond) := isOpenImmersion_of_section _ _ ht₀
  have hclosed : IsClosedImmersion (pullback.lift s₀ (𝟙 _) hcond) := isClosedImmersion_of_section _
    _ ht₀
  let V₀ : (pullback π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue
    R))))).Opens := (pullback.lift s₀ (𝟙 _) hcond).opensRange
  have hV₀c : IsClosed (V₀ : Set ↥(pullback π (pullback.fst f (Spec.map (CommRingCat.ofHom
    (IsLocalRing.residue R)))))) :=
    (pullback.lift s₀ (𝟙 _) hcond).isClosedEmbedding.isClosed_range
  have hV₀i : IsIso (V₀.ι ≫ pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom
    (IsLocalRing.residue R))))) := by
    have e : (pullback.lift s₀ (𝟙 _) hcond).isoOpensRange.hom ≫ V₀.ι = pullback.lift s₀ (𝟙 _) hcond
      :=
      (pullback.lift s₀ (𝟙 _) hcond).isoOpensRange_hom_ι
    have : V₀.ι ≫ pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue
      R)))) = (pullback.lift s₀ (𝟙 _) hcond).isoOpensRange.inv := by
      rw [← cancel_epi (pullback.lift s₀ (𝟙 _) hcond).isoOpensRange.hom, ← Category.assoc, e, ht₀,
        Iso.hom_inv_id]
    rw [this]
    infer_instance
  let V : (pullback (π ≫ f) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))).Opens :=
    (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) π).inv
    ⁻¹ᵁ V₀
  have hVc : IsClosed (V : Set ↥(pullback (π ≫ f) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue
    R))))) := hV₀c.preimage (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom
    (IsLocalRing.residue R))) π).inv.continuous
  have : IsClosedImmersion (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨Uset, hUclopen, hUVset⟩ :=
    AlgebraicGeometry.exists_isClopen_closedFiber_preimage_eq_of_isProper_of_henselianLocalRing
      (π ≫ f)
      (V : Set ↥(pullback (π ≫ f) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))) ⟨hVc,
        V.2⟩
  let U : Y.Opens := ⟨Uset, hUclopen.isOpen⟩
  have hUc : IsClosed (U : Set Y) := hUclopen.isClosed
  have hUV : (pullback.fst (π ≫ f) (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ⁻¹ᵁ U =
    V := TopologicalSpace.Opens.ext hUVset
  have hUV₀ : (pullback.fst π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue
    R))))) ⁻¹ᵁ U = V₀ := by
    have h : ((pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
      π).inv ≫ pullback.fst π (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue
      R))))) ⁻¹ᵁ U = (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue R))) π).inv ⁻¹ᵁ V₀ := by
      rw [pullbackRightPullbackFstIso_inv_fst]; exact hUV
    rw [Scheme.Hom.comp_preimage] at h
    have h2 := congrArg (fun W => (pullbackRightPullbackFstIso f (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue R))) π).hom ⁻¹ᵁ W) h
    simp only [← Scheme.Hom.comp_preimage, Iso.hom_inv_id] at h2
    simpa only [Iso.hom_inv_id_assoc, Scheme.Hom.id_preimage] using h2
  have : IsClosedImmersion U.ι := isClosedImmersion_ι_of_isClosed U hUc
  have hiso : IsIso (U.ι ≫ π) :=
    AlgebraicGeometry.isIso_of_isIso_pullback_closedFibre_of_isFinite_of_etale_of_isProper f (U.ι ≫
      π)
      (isIso_pullback_snd_of_preimage_eq (pullback.fst f (Spec.map (CommRingCat.ofHom
        (IsLocalRing.residue R)))) π U V₀ hV₀i hUV₀)
  refine ⟨inv (U.ι ≫ π) ≫ U.ι, by rw [Category.assoc, IsIso.inv_hom_id], ?_⟩
  have hcond' : ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≫ inv (U.ι
    ≫ π) ≫ U.ι) ≫ π = 𝟙 _ ≫ (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    := by
    simp only [Category.assoc, Category.id_comp, IsIso.inv_hom_id, Category.comp_id]
  have ht' : pullback.lift ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    ≫ inv (U.ι ≫ π) ≫ U.ι) (𝟙 _) hcond' ≫ pullback.snd π (pullback.fst f (Spec.map
    (CommRingCat.ofHom (IsLocalRing.residue R)))) = 𝟙 _ :=
    pullback.lift_snd _ _ _
  have hr₀ : Set.range (pullback.lift s₀ (𝟙 _) hcond).base ⊆ Set.range V₀.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact subset_of_eq rfl
  have hr' : Set.range (pullback.lift ((pullback.fst f (Spec.map (CommRingCat.ofHom
    (IsLocalRing.residue R)))) ≫ inv (U.ι ≫ π) ≫ U.ι) (𝟙 _) hcond').base ⊆
      Set.range V₀.ι.base := by
    rw [Scheme.Opens.range_ι, ← hUV₀]
    rintro _ ⟨x, rfl⟩
    change ((pullback.lift ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
      ≫ inv (U.ι ≫ π) ≫ U.ι) (𝟙 _) hcond') ≫ pullback.fst π (pullback.fst f (Spec.map
      (CommRingCat.ofHom (IsLocalRing.residue R))))).base x ∈
      (U : Set Y)
    rw [pullback.lift_fst]
    change U.ι.base (((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≫ inv
      (U.ι ≫ π)).base x) ∈ (U : Set Y)
    rw [← Scheme.Opens.range_ι U]
    exact ⟨_, rfl⟩
  have eq1 : IsOpenImmersion.lift V₀.ι _ hr' ≫ V₀.ι ≫ pullback.snd π (pullback.fst f (Spec.map
    (CommRingCat.ofHom (IsLocalRing.residue R)))) = 𝟙 _ := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact ht'
  have eq0 : IsOpenImmersion.lift V₀.ι _ hr₀ ≫ V₀.ι ≫ pullback.snd π (pullback.fst f (Spec.map
    (CommRingCat.ofHom (IsLocalRing.residue R)))) = 𝟙 _ := by
    rw [← Category.assoc, IsOpenImmersion.lift_fac]; exact ht₀
  have hlifts : IsOpenImmersion.lift V₀.ι _ hr' = IsOpenImmersion.lift V₀.ι _ hr₀ := by
    have : Mono (V₀.ι ≫ pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue R))))) := by have := hV₀i; infer_instance
    rw [← cancel_mono (V₀.ι ≫ pullback.snd π (pullback.fst f (Spec.map (CommRingCat.ofHom
      (IsLocalRing.residue R)))))]
    exact eq1.trans eq0.symm
  calc (pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≫ inv (U.ι ≫ π) ≫ U.ι
      = pullback.lift ((pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))) ≫
        inv (U.ι ≫ π) ≫ U.ι) (𝟙 _) hcond' ≫ pullback.fst π (pullback.fst f (Spec.map
        (CommRingCat.ofHom (IsLocalRing.residue R)))) :=
        (pullback.lift_fst _ _ _).symm
    _ = (IsOpenImmersion.lift V₀.ι _ hr' ≫ V₀.ι) ≫ pullback.fst π (pullback.fst f (Spec.map
      (CommRingCat.ofHom (IsLocalRing.residue R)))) := by rw [IsOpenImmersion.lift_fac]
    _ = (IsOpenImmersion.lift V₀.ι _ hr₀ ≫ V₀.ι) ≫ pullback.fst π (pullback.fst f (Spec.map
      (CommRingCat.ofHom (IsLocalRing.residue R)))) := by rw [hlifts]
    _ = s₀ := by rw [IsOpenImmersion.lift_fac, pullback.lift_fst]

end AlgebraicGeometry
