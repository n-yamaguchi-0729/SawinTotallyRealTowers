/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/P2M/Sol/S_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Mathlib.CategoryTheory.Localization.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Nyll.SchemeTheory.Modules.PresheafInternalHom
import Nyll.SchemeTheory.Modules.InternalHomSheaf

/-!
# Tensor compatibility of module sheafification equivalences

For a locally bijective morphism of ring presheaves, the module-presheaf morphisms whose
underlying additive presheaf maps are sheafification equivalences form a monoidal morphism
property. The proof uses the internal-Hom adjunction and the sheafification adjunction.
-/

section ProofImplementation

namespace
  AlgebraicCurves.Foundations.Algebra.Proofs.PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf

universe u

open _root_.CategoryTheory
open _root_.CategoryTheory.MonoidalCategory
open _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory.Limits

noncomputable section

namespace PresheafOfModules
open _root_.PresheafOfModules
namespace IsMonoidalW
open _root_.PresheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Sheaf J RingCat.{u})
  (α : 𝒪 ⋙ forget₂ CommRingCat RingCat ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- The category of module presheaves over the given commutative-ring presheaf. -/
abbrev PMod := PresheafOfModules.{u} (𝒪 ⋙ forget₂ CommRingCat RingCat)

private abbrev W : MorphismProperty (PMod 𝒪) :=
  (J.W (A := AddCommGrpCat.{u})).inverseImage
    (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))

/-- The module-sheafification functor along the locally bijective ring-presheaf morphism. -/
abbrev shf : PMod 𝒪 ⥤ SheafOfModules.{u} R := PresheafOfModules.sheafification α

/-- The functor forgetting the sheaf condition and restricting scalars along the ring-presheaf
  morphism. -/
abbrev inc : SheafOfModules.{u} R ⥤ PMod 𝒪 :=
  SheafOfModules.forget R ⋙ PresheafOfModules.restrictScalars α

/-- The adjunction between module sheafification and the underlying module-presheaf functor. -/
abbrev adj : shf 𝒪 R α ⊣ inc 𝒪 R α := PresheafOfModules.sheafificationAdjunction α

scoped instance : (inc 𝒪 R α).Faithful := (adj 𝒪 R α).fullyFaithfulROfIsIsoCounit.faithful
scoped instance : (inc 𝒪 R α).Full := (adj 𝒪 R α).fullyFaithfulROfIsIsoCounit.full

lemma W_eq : W (J := J) 𝒪 = (MorphismProperty.isomorphisms _).inverseImage (shf 𝒪 R α) :=
  PresheafOfModules.inverseImage_W_toPresheaf_eq_inverseImage_isomorphisms α

lemma isIso_unit_app_of_isSheaf (N : PMod 𝒪) (hN : Presheaf.IsSheaf J N.presheaf) :
    IsIso ((adj 𝒪 R α).unit.app N) := by
  have : IsIso ((PresheafOfModules.toPresheaf _).map ((adj 𝒪 R α).unit.app N)) := by
    rw [PresheafOfModules.toPresheaf_map_sheafificationAdjunction_unit_app]
    exact isIso_toSheafify J hN
  exact isIso_of_reflects_iso _ (PresheafOfModules.toPresheaf _)

lemma isIso_shf_map_unit_whiskerRight (d d' : PMod 𝒪) :
    IsIso ((shf 𝒪 R α).map (((adj 𝒪 R α).unit.app d) ▷ d')) := by
  have h := (Monoidal.Reflective.isIso_tfae (adj 𝒪 R α)).out 1 3
  refine (h.mp ?_) d d'
  intro c d
  apply isIso_unit_app_of_isSheaf
  exact PresheafOfModules.isSheaf_ihomObj _ _ c.isSheaf

include R α in
lemma W_whiskerRight {d₁ d₂ : PMod 𝒪} (g : d₁ ⟶ d₂) (hg : W (J := J) 𝒪 g) (d' : PMod 𝒪) :
    W (J := J) 𝒪 (g ▷ d') := by
  have two3 : (W (J := J) 𝒪).HasTwoOutOfThreeProperty := by
    rw [W_eq 𝒪 R α]; infer_instance
  have hη : ∀ d : PMod 𝒪, W (J := J) 𝒪 ((adj 𝒪 R α).unit.app d ▷ d') := fun d => by
    rw [W_eq 𝒪 R α]
    exact isIso_shf_map_unit_whiskerRight 𝒪 R α d d'
  have hiso : W (J := J) 𝒪 ((inc 𝒪 R α).map ((shf 𝒪 R α).map g) ▷ d') := by
    rw [W_eq 𝒪 R α] at hg ⊢
    simp only [MorphismProperty.inverseImage_iff, MorphismProperty.isomorphisms.iff] at hg ⊢
    have : IsIso ((inc 𝒪 R α).map ((shf 𝒪 R α).map g)) := Functor.map_isIso _ _
    infer_instance
  have e := (adj 𝒪 R α).unit_naturality g
  have hη₁ := hη d₁
  have hη₂ := hη d₂
  dsimp only [Functor.comp_obj, Functor.id_obj] at e hη₁ hη₂ hiso ⊢
  have h' := (W (J := J) 𝒪).comp_mem _ _ hη₁ hiso
  rw [← comp_whiskerRight, e, comp_whiskerRight] at h'
  exact (W (J := J) 𝒪).of_postcomp _ _ hη₂ h'

end PresheafOfModules.IsMonoidalW

end

open PresheafOfModules.IsMonoidalW in
theorem _root_.PresheafOfModules.isMonoidal_inverseImage_W_toPresheaf {C : Type u} [Category.{u} C]
  {J : GrothendieckTopology C}
    (𝒪 : Cᵒᵖ ⥤ CommRingCat.{u}) (R : Sheaf J RingCat.{u})
    (α : 𝒪 ⋙ forget₂ CommRingCat RingCat ⟶ R.obj)
    [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}] :
    ((J.W (A := AddCommGrpCat.{u})).inverseImage
      (PresheafOfModules.toPresheaf (𝒪 ⋙ forget₂ CommRingCat RingCat))).IsMonoidal where
  whiskerRight g hg d' := W_whiskerRight 𝒪 R α g hg d'
  whiskerLeft d g₁ g₂ g hg :=
    ((W (J := J) 𝒪).arrow_mk_iso_iff (Arrow.isoMk' (g ▷ d) (d ◁ g) (β_ g₁ d) (β_ g₂ d)
      (BraidedCategory.braiding_naturality_left g d).symm)).1 (W_whiskerRight 𝒪 R α g hg d)
end
  AlgebraicCurves.Foundations.Algebra.Proofs.PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
end ProofImplementation

attribute [-instance] PresheafOfModules.instMonoidalClosed

namespace PresheafOfModules.InternalHom

attribute [-instance]
  instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies
  instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf
  instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies

end PresheafOfModules.InternalHom
attribute [-simp] PresheafOfModules.InternalHom.presheaf_map_apply
  PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app
  PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app
  PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map
  PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app
  PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val
  PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj
  PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app
  PresheafOfModules.ihomMap_app_val
