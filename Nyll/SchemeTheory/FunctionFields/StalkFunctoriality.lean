/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Nyll.SchemeTheory.FunctionFields.Functoriality
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!
# Function-field maps and local rings

The canonical map on function fields commutes with every stalk map, not
only with global sections. For an open immersion it therefore identifies
the actual local-ring subrings. This supplies the local equations needed
when restricting a Kummer construction to an open curve.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

omit [IsIntegral X] in
private theorem eqToHom_stalk_eq_stalkCongr'
    {x x' : X} (h : x = x') :
    eqToHom (congrArg (fun z => X.presheaf.stalk z) h) =
      (X.presheaf.stalkCongr (.of_eq h)).hom := by
  subst x'
  simp only [eqToHom_refl, TopCat.Presheaf.stalkCongr_hom,
    TopCat.Presheaf.stalkSpecializes_refl]

/-- Function-field pullback commutes with taking the generic germ of a
section over any nonempty open, with nonempty inverse image. -/
theorem functionFieldMap_comp_germToFunctionField
    (f : Y ⟶ X) (hf : DenseRange f) (U : X.Opens)
    [Nonempty U] [Nonempty (f ⁻¹ᵁ U)] :
    (f.functionFieldMap hf).comp (X.germToFunctionField U).hom =
      (Y.germToFunctionField (f ⁻¹ᵁ U)).hom.comp (f.app U).hom := by
  let h : genericPoint X = f (genericPoint Y) := (f.map_genericPoint_of_denseRange hf).symm
  have hEq : eqToHom (show X.presheaf.stalk (genericPoint X) =
      X.presheaf.stalk (f (genericPoint Y)) by
        rw [f.map_genericPoint_of_denseRange hf]) =
      (X.presheaf.stalkCongr (.of_eq h)).hom :=
    eqToHom_stalk_eq_stalkCongr' h
  unfold functionFieldMap
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  apply congrArg CommRingCat.Hom.hom
  rw [hEq]
  simp only [TopCat.Presheaf.stalkCongr_hom]
  rw [← Category.assoc]
  erw [TopCat.Presheaf.germ_stalkSpecializes]
  exact f.germ_stalkMap U (genericPoint Y)
    (((genericPoint_spec Y).mem_open_set_iff (f ⁻¹ᵁ U).isOpen).mpr
      (by
        obtain ⟨y⟩ := (inferInstance : Nonempty (f ⁻¹ᵁ U))
        exact ⟨y.val, Set.mem_univ y.val, y.property⟩))

/-- The actual map on function fields commutes with the actual map on
local rings at every point. -/
theorem functionFieldMap_algebraMap_stalk
    (f : Y ⟶ X) (hf : DenseRange f) (y : Y) (a : X.presheaf.stalk (f y)) :
    f.functionFieldMap hf (algebraMap (X.presheaf.stalk (f y)) X.functionField a) =
      algebraMap (Y.presheaf.stalk y) Y.functionField (f.stalkMap y a) := by
  obtain ⟨U, hy, aU, haU⟩ := X.presheaf.exists_germ_eq a
  have : Nonempty U := ⟨⟨f y, hy⟩⟩
  have : Nonempty (f ⁻¹ᵁ U) := ⟨⟨y, hy⟩⟩
  rw [← haU, X.algebraMap_germ_eq_germToFunctionField hy aU]
  have hgeneric := congrArg
    (fun q : Γ(X, U) →+* Y.functionField => q aU)
    (f.functionFieldMap_comp_germToFunctionField hf U)
  have hstalk := ConcreteCategory.congr_hom (f.germ_stalkMap U y hy) aU
  change f.stalkMap y (X.presheaf.germ U (f y) hy aU) =
    Y.presheaf.germ (f ⁻¹ᵁ U) y hy (f.app U aU) at hstalk
  rw [hstalk, Y.algebraMap_germ_eq_germToFunctionField hy (f.app U aU)]
  exact hgeneric

/-- An open immersion identifies, inside the identified function fields,
the actual local-ring images at corresponding points. -/
theorem functionFieldMap_mem_stalk_range_iff_of_isOpenImmersion
    (f : Y ⟶ X) [IsOpenImmersion f] (hf : DenseRange f) (y : Y)
    (a : X.functionField) :
    f.functionFieldMap hf a ∈ (algebraMap (Y.presheaf.stalk y) Y.functionField).range ↔
      a ∈ (algebraMap (X.presheaf.stalk (f y)) X.functionField).range := by
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (f.stalkMap y)).2 b
    refine ⟨c, (f.functionFieldMap hf).injective ?_⟩
    rw [f.functionFieldMap_algebraMap_stalk hf y c, hc]
    exact hb
  · rintro ⟨b, hb⟩
    refine ⟨f.stalkMap y b, ?_⟩
    rw [← f.functionFieldMap_algebraMap_stalk hf y b, hb]

end AlgebraicGeometry.Scheme.Hom
