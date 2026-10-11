/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesRestrictOpen.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Nyll.SchemeTheory.CategoryTheory.PresheafModulePushforward

/-!
# Restriction of module presheaves and sheaves

Compares restriction to open subschemes with the corresponding pullback constructions.
-/

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Functor

namespace AlgebraicGeometry.Scheme.Modules

open TopologicalSpace

variable {X : Scheme.{u}} (U : X.Opens)

/-- The canonical ring-presheaf map identifying restriction to an open subscheme with sections
  on its image. -/
noncomputable def restrictPresheafRingHom :
    (U : Scheme.{u}).ringCatSheaf.obj ⟶ U.ι.opensFunctor.op ⋙ X.ringCatSheaf.obj := 𝟙 _

/-- Restriction of presheaves of modules to the open subscheme. -/
noncomputable def restrictPresheaf : X.PresheafOfModules ⥤ (U : Scheme.{u}).PresheafOfModules :=
  PresheafOfModules.pushforward.{u} (restrictPresheafRingHom U)

/-- Restriction obtained by precomposing with the open-image functor, before scalar restriction. -/
noncomputable def restrictPresheaf₀ : X.PresheafOfModules ⥤ (U : Scheme.{u}).PresheafOfModules :=
  PresheafOfModules.pushforward₀.{u} U.ι.opensFunctor X.ringCatSheaf.obj

/-- The canonical identification of the two descriptions of presheaf restriction. -/
noncomputable def restrictPresheafIsoRestrictPresheaf₀ : restrictPresheaf U ≅ restrictPresheaf₀
  U := Iso.refl _

lemma restrictPresheaf_obj_obj (P : X.PresheafOfModules) (V : (U : Scheme.{u}).Opensᵒᵖ) :
    (((restrictPresheaf U).obj P).obj V : Type u) = P.obj (Opposite.op (U.ι ''ᵁ V.unop)) := rfl

/-- Restriction to the open subscheme is left adjoint to presheaf pushforward along its
  inclusion. -/
noncomputable def restrictPresheafAdj :
    restrictPresheaf U ⊣ PresheafOfModules.pushforward.{u} U.ι.toRingCatSheafHom.hom := by
  let adjU : U.ι.opensFunctor ⊣ Opens.map U.ι.base := by
    exact U.ι.isOpenEmbedding.isOpenMap.adjunction
  refine PresheafOfModules.pushforwardPushforwardAdj adjU _ _ ?_ ?_
  · ext V x; rfl
  · ext V x
    let W : X.Opens := U.ι ''ᵁ V.unop
    let j₁ := (adjU.counit.app W).op
    let j₂ := (U.ι.opensFunctor.map (adjU.unit.app V.unop)).op
    have hj : j₁ ≫ j₂ = 𝟙 (Opposite.op W) := Subsingleton.elim _ _
    have hmap : X.presheaf.map j₁ ≫ X.presheaf.map j₂ = 𝟙 (X.presheaf.obj (Opposite.op W)) :=
      (X.presheaf.map_comp j₁ j₂).symm.trans
        ((congrArg (fun k : Opposite.op W ⟶ Opposite.op W => X.presheaf.map k) hj).trans
          (X.presheaf.map_id (Opposite.op W)))
    exact congrArg
      (fun k : X.presheaf.obj (Opposite.op W) ⟶ X.presheaf.obj (Opposite.op W) => k.hom x) hmap

section

local instance : (PresheafOfModules.pushforward.{u} U.ι.toRingCatSheafHom.hom).IsRightAdjoint :=
  (restrictPresheafAdj U).isRightAdjoint

/-- The identification of presheaf pullback along an open inclusion with restriction. -/
noncomputable def pullbackPresheafIsoRestrictPresheaf :
    PresheafOfModules.pullback.{u} U.ι.toRingCatSheafHom.hom ≅ restrictPresheaf U :=
  Adjunction.leftAdjointUniq (PresheafOfModules.pullbackPushforwardAdjunction _)
    (restrictPresheafAdj U)

/-- Sheafification followed by pullback to an open subscheme agrees with restriction followed by
  sheafification. -/
noncomputable def sheafificationCompPullbackIso :
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj) ⋙ Modules.pullback U.ι ≅
      restrictPresheaf U ⋙ PresheafOfModules.sheafification (𝟙 (U : Scheme.{u}).ringCatSheaf.obj) :=
  SheafOfModules.sheafificationCompPullback U.ι.toRingCatSheafHom ≪≫
    isoWhiskerRight (pullbackPresheafIsoRestrictPresheaf U) _

end

/-- Restriction of sheaves of modules to an open subscheme using the open-image functor. -/
noncomputable def restrictOpen : X.Modules ⥤ (U : Scheme.{u}).Modules :=
  SheafOfModules.pushforward.{u} (F := U.ι.opensFunctor) ⟨restrictPresheafRingHom U⟩

lemma restrictOpen_obj_val (M : X.Modules) :
    ((restrictOpen U).obj M).val = (restrictPresheaf U).obj M.val := rfl

/-- The canonical identification of open restriction with the scheme restriction functor. -/
noncomputable def restrictOpenIsoRestrictFunctor : restrictOpen U ≅ Modules.restrictFunctor U.ι :=
  SheafOfModules.pushforwardCongr (by
    ext V x
    change x = (U.ι.appIso V.unop).inv x
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl)

/-- The canonical identification of open restriction with scheme pullback. -/
noncomputable def restrictOpenIsoPullback : restrictOpen U ≅ Modules.pullback U.ι :=
  restrictOpenIsoRestrictFunctor U ≪≫ Modules.restrictFunctorIsoPullback U.ι

end AlgebraicGeometry.Scheme.Modules
