/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Function fields of dominant morphisms

A morphism with dense image between integral schemes sends the generic point
to the generic point.  Its map on local rings therefore gives the canonical
embedding of function fields.
-/

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry

universe u

namespace Scheme.Hom

variable {X Y : Scheme.{u}}

private theorem eqToHom_stalk_eq_stalkCongr
    (Z : Scheme.{u}) {z z' : Z} (h : z = z') :
    eqToHom (congrArg (fun w ↦ Z.presheaf.stalk w) h) =
      (Z.presheaf.stalkCongr (.of_eq h)).hom := by
  subst z'
  simp

/-- A dense morphism between irreducible schemes sends the generic point to
the generic point. -/
theorem map_genericPoint_of_denseRange
    (f : Y ⟶ X) [IrreducibleSpace X] [IrreducibleSpace Y]
    (hf : DenseRange f) :
    f (genericPoint Y) = genericPoint X := by
  apply ((genericPoint_spec X).eq _).symm
  convert (genericPoint_spec Y).image f.continuous using 1
  simpa only [Set.image_univ] using hf.closure_range.symm

/-- The canonical map on function fields induced by a dense morphism of
integral schemes. -/
noncomputable def functionFieldMap
    (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y]
    (hf : DenseRange f) :
    X.functionField →+* Y.functionField :=
  (eqToHom (show
      X.presheaf.stalk (genericPoint X) =
        X.presheaf.stalk (f (genericPoint Y)) by
      rw [map_genericPoint_of_denseRange f hf]) ≫
    f.stalkMap (genericPoint Y)).hom

/-- The function-field map of a dense morphism of integral schemes is
injective. -/
theorem functionFieldMap_injective
    (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y]
    (hf : DenseRange f) :
    Function.Injective (functionFieldMap f hf) :=
  (functionFieldMap f hf).injective

/-- On global sections, the function-field map of a dense morphism is the
map obtained by first pulling back the section and then taking its germ at
the generic point. -/
theorem functionFieldMap_comp_germToFunctionField_top
    (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y]
    (hf : DenseRange f) :
    letI : Nonempty (⊤ : X.Opens) :=
      ⟨⟨Classical.choice (inferInstance : Nonempty X), by simp⟩⟩
    letI : Nonempty (⊤ : Y.Opens) :=
      ⟨⟨Classical.choice (inferInstance : Nonempty Y), by simp⟩⟩
    (functionFieldMap f hf).comp (X.germToFunctionField ⊤).hom =
      (Y.germToFunctionField ⊤).hom.comp f.appTop.hom := by
  let : Nonempty (⊤ : X.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty X), by simp⟩⟩
  let : Nonempty (⊤ : Y.Opens) :=
    ⟨⟨Classical.choice (inferInstance : Nonempty Y), by simp⟩⟩
  let h : genericPoint X = f (genericPoint Y) :=
    (map_genericPoint_of_denseRange f hf).symm
  have hEq : eqToHom (show
      X.presheaf.stalk (genericPoint X) =
        X.presheaf.stalk (f (genericPoint Y)) by
      rw [map_genericPoint_of_denseRange f hf]) =
      (X.presheaf.stalkCongr (.of_eq h)).hom := by
    convert eqToHom_stalk_eq_stalkCongr X h
  unfold functionFieldMap
  rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
  apply congrArg CommRingCat.Hom.hom
  rw [hEq]
  simp only [TopCat.Presheaf.stalkCongr_hom]
  rw [← Category.assoc]
  erw [TopCat.Presheaf.germ_stalkSpecializes]
  exact f.germ_stalkMap ⊤ (genericPoint Y) (by simp)

/-- The algebra structure on the target function field induced by a dense
morphism of integral schemes. -/
@[reducible] noncomputable def functionFieldAlgebraOfDenseRange
    (f : Y ⟶ X) [IsIntegral X] [IsIntegral Y]
    (hf : DenseRange f) :
    Algebra X.functionField Y.functionField :=
  (functionFieldMap f hf).toAlgebra

end Scheme.Hom

end AlgebraicGeometry
