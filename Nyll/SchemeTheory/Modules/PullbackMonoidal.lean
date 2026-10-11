/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted Anthropic FLT source (pinned comparison revision):
https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_AlgebraicGeometry_ModulesPullbackMonoidal.lean
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Nyll.SchemeTheory.Modules.PresheafInternalHom
import Nyll.SchemeTheory.Modules.SheafificationMonoidal
import Nyll.SchemeTheory.Modules.Monoidal
import Nyll.SchemeTheory.Modules.PresheafPullbackMonoidal

/-!
# Tensor compatibility of module pullback on schemes

Pullback on module presheaves descends through module sheafification to a monoidal functor
on module sheaves. Its tensor and unit comparison isomorphisms identify pullbacks of tensor
products and structure modules with the corresponding tensor products and structure modules.
-/

universe u

open CategoryTheory MonoidalCategory Limits TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance preservesBinaryProducts_opensMap :
    PreservesLimitsOfShape (Discrete WalkingPair) (Opens.map f.base) where
  preservesLimit {K} := ⟨fun {c} hc => ⟨
    { lift := fun s => homOfLE (by
        have hinf : K.obj ⟨.left⟩ ⊓ K.obj ⟨.right⟩ ≤ c.pt := leOfHom (hc.lift
          { pt := K.obj ⟨.left⟩ ⊓ K.obj ⟨.right⟩
            π := Discrete.natTrans (fun j => match j with
              | ⟨.left⟩ => homOfLE inf_le_left
              | ⟨.right⟩ => homOfLE inf_le_right) })
        have h₁ : s.pt ≤ (Opens.map f.base).obj (K.obj ⟨.left⟩) := leOfHom (s.π.app ⟨.left⟩)
        have h₂ : s.pt ≤ (Opens.map f.base).obj (K.obj ⟨.right⟩) := leOfHom (s.π.app ⟨.right⟩)
        exact (le_inf h₁ h₂).trans (leOfHom ((Opens.map f.base).map (homOfLE hinf))))
      fac := fun s j => Subsingleton.elim _ _
      uniq := fun s m _ => Subsingleton.elim _ _ }⟩⟩

instance preservesTerminal_opensMap :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (Opens.map f.base) where
  preservesLimit {K} := ⟨fun {c} hc => ⟨
    { lift := fun s => homOfLE (by
        have htop : (⊤ : Y.Opens) ≤ c.pt := leOfHom (hc.lift
          { pt := ⊤, π := Discrete.natTrans (fun j => j.as.elim) })
        exact le_top.trans (leOfHom ((Opens.map f.base).map (homOfLE htop))))
      fac := fun s j => Subsingleton.elim _ _
      uniq := fun s m _ => Subsingleton.elim _ _ }⟩⟩

instance preservesFiniteProducts_opensMap : PreservesFiniteProducts (Opens.map f.base) :=
  Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal _

/-- The pullback functor on module presheaves underlying the pullback of sheaves of modules. -/
abbrev pullback₀ : Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.PullbackMonoidal.pb (Opens.map f.base) (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

instance pullback₀_monoidal : (pullback₀ f).Monoidal :=
  PresheafOfModules.PullbackMonoidal.pullback_monoidal (Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

local instance : (PresheafOfModules.pushforward.{u}
    (F := Opens.map f.base) f.toRingCatSheafHom.hom).IsRightAdjoint :=
  (PresheafOfModules.PullbackMonoidal.adj (Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c).isRightAdjoint

example : pullback₀ f = PresheafOfModules.pullback f.toRingCatSheafHom.hom := rfl

variable (Y) in
instance sheafify_isLocalization' : (Modules.sheafify Y).IsLocalization
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj) :=
  inferInstanceAs ((SheafOfModules.sheafifyFunctor Y.sheaf.obj
    Y.ringCatSheaf.property).IsLocalization
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj))

instance sheafifyPullback_lifting : Localization.Lifting (Modules.sheafify Y)
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
    (pullback₀ f ⋙ Modules.sheafify X) (Modules.pullback f) :=
  ⟨SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom⟩

instance pullback_monoidal : (Modules.pullback f).Monoidal := by
  have : MorphismProperty.ContainsIdentities (C := Y.PresheafOfModules)
      (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj) :=
    MorphismProperty.ContainsIdentities.inverseImage
      (P := (Opens.grothendieckTopology Y).W (A := AddCommGrpCat.{u}))
      (PresheafOfModules.toPresheaf (Y.sheaf.obj ⋙ forget₂ CommRingCat RingCat))
  letI := SheafOfModules.presheafW_isMonoidal
    (J := Opens.grothendieckTopology Y) Y.sheaf.obj Y.ringCatSheaf.property
  exact Localization.Monoidal.functorMonoidalOfComp (Modules.sheafify Y)
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
    (Modules.pullback f) (pullback₀ f ⋙ Modules.sheafify X)

/-- The comparison identifying pullback of a sheaf tensor product with the tensor product of the
  pullbacks. -/
def pullbackTensorObjIso (L M : Y.Modules) :
    (Modules.pullback f).obj (L ⊗ M) ≅ (Modules.pullback f).obj L ⊗ (Modules.pullback f).obj M :=
  (Functor.Monoidal.μIso (Modules.pullback f) L M).symm

/-- The comparison identifying pullback of the sheaf tensor unit with the tensor unit. -/
def pullbackTensorUnitObjIso : (Modules.pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  (Functor.Monoidal.εIso (Modules.pullback f)).symm

end AlgebraicGeometry.Scheme.Modules

end
