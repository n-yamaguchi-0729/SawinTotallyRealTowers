/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_RelativePicardFunctor.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-! Invertible scheme modules and the canonical pullback of the unit module. -/

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry

/-- A sheaf of modules locally isomorphic to the unit module around every point. -/
structure Scheme.Modules.IsInvertible {X : Scheme.{u}} (M : X.Modules) : Prop where
  /-- Every point has an open neighborhood on which the module is trivial. -/
  exists_trivialization : ∀ x : X, ∃ (U : X.Opens), x ∈ U ∧
    Nonempty ((Scheme.Modules.pullback U.ι).obj M ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)

instance Scheme.Hom.opensMapFinal {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

/-- The canonical identification of the pullback of the unit module with the unit module. -/
def Scheme.Modules.pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf := by
  let : (SheafOfModules.pushforward f.toRingCatSheafHom).IsRightAdjoint :=
    (Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  let : (TopologicalSpace.Opens.map f.base).Final := Scheme.Hom.opensMapFinal f
  let makeUnitIso {C D : Type u} [Category.{u} C] [Category.{u} D]
      {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
      {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
      [Functor.IsContinuous F J K]
      (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)
      [(SheafOfModules.pushforward.{u} φ).IsRightAdjoint] [F.Final] :
      (SheafOfModules.pullback φ).obj (SheafOfModules.unit S) ≅ SheafOfModules.unit R :=
    asIso (SheafOfModules.pullbackObjUnitToUnit φ)
  exact makeUnitIso f.toRingCatSheafHom

theorem Scheme.Modules.isInvertible_unit (X : Scheme.{u}) :
    Scheme.Modules.IsInvertible (SheafOfModules.unit X.ringCatSheaf) :=
  ⟨fun _ => ⟨⊤, trivial, ⟨Scheme.Modules.pullbackUnitIso _⟩⟩⟩

theorem Scheme.Modules.IsInvertible.pullback {X Y : Scheme.{u}} (f : X ⟶ Y) {L : Y.Modules}
    (hL : Scheme.Modules.IsInvertible L) :
    Scheme.Modules.IsInvertible ((Scheme.Modules.pullback f).obj L) := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, hyU, ⟨eU⟩⟩ := hL.1 (f.base x)
  refine ⟨f ⁻¹ᵁ U, hyU, ⟨?_⟩⟩
  have hfact : (f ⁻¹ᵁ U).ι ≫ f = (f ∣_ U) ≫ U.ι := (morphismRestrict_ι f U).symm
  exact
    (Scheme.Modules.pullbackComp _ _).app L ≪≫
    (Scheme.Modules.pullbackCongr hfact).app L ≪≫
    ((Scheme.Modules.pullbackComp _ _).app L).symm ≪≫
    (Scheme.Modules.pullback (f ∣_ U)).mapIso eU ≪≫
    Scheme.Modules.pullbackUnitIso (f ∣_ U)

end AlgebraicGeometry
