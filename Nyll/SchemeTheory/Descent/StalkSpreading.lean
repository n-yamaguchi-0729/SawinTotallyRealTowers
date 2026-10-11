/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.Topology.Sheaves.Stalks

/-!+# Spreading a stalk morphism with finitely presented target

The actual stalk is the colimit of the rings of sections over its open
neighborhoods. Applying `Spec` gives an affine inverse system. A morphism
from this limit into a locally finitely presented relative target descends
to one stage; composition with the neighborhood's affinization gives an
actual morphism on that neighborhood.

No injectivity of a germ map, Noetherianity, reducedness, or normality is
required. This is the local morphism supplier needed for Stacks 0BQF.
-/

noncomputable section

universe u

open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A morphism from an actual scheme stalk spreads over an affine base
when its target is locally of finite presentation. -/
theorem Scheme.exists_open_extension_fromSpecStalk_of_isAffine
    {X Y : Scheme.{u}} [IsAffine X] (f : Y ⟶ X)
    [LocallyOfFinitePresentation f] (x : X)
    (a : Spec (X.presheaf.stalk x) ⟶ Y)
    (ha : a ≫ f = X.fromSpecStalk x) :
    ∃ (U : X.Opens) (hxU : x ∈ U) (b : U.toScheme ⟶ Y),
      U.fromSpecStalkOfMem x hxU ≫ b = a ∧ b ≫ f = U.ι := by
  let F : (OpenNhds x)ᵒᵖ ⥤ CommRingCat.{u} :=
    (OpenNhds.inclusion x).op ⋙ X.presheaf
  let D : (OpenNhds x)ᵒᵖᵒᵖ ⥤ Scheme.{u} := F.op ⋙ Scheme.Spec
  let c : Cone D := Scheme.Spec.mapCone (colimit.cocone F).op
  have hc : IsLimit c :=
    isLimitOfPreserves Scheme.Spec (colimit.isColimit F).op
  let t : D ⟶ (Functor.const (OpenNhds x)ᵒᵖᵒᵖ).obj X :=
    { app := fun i =>
        Spec.map (X.presheaf.map (homOfLE (show i.unop.unop.1 ≤ ⊤ from le_top)).op) ≫
          X.isoSpec.inv
      naturality := by
        intro i j h
        change Spec.map (X.presheaf.map ((OpenNhds.inclusion x).map h.unop.unop).op) ≫
            (Spec.map (X.presheaf.map (homOfLE le_top).op) ≫ X.isoSpec.inv) =
          (Spec.map (X.presheaf.map (homOfLE le_top).op) ≫ X.isoSpec.inv) ≫ 𝟙 X
        rw [Category.comp_id, ← Category.assoc, ← Spec.map_comp, ← X.presheaf.map_comp]
        rfl }
  have hcompat : c.π ≫ t = (Functor.const (OpenNhds x)ᵒᵖᵒᵖ).map (a ≫ f) := by
    apply NatTrans.ext
    funext i
    change Spec.map (X.presheaf.germ i.unop.unop.1 x i.unop.unop.2) ≫
        (Spec.map (X.presheaf.map (homOfLE le_top).op) ≫ X.isoSpec.inv) = a ≫ f
    rw [← Category.assoc, ← Spec.map_comp, TopCat.Presheaf.germ_res,
      ← Scheme.fromSpecStalk_toSpecΓ, Category.assoc,
      Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]
    exact ha.symm
  have : ∀ {i j : (OpenNhds x)ᵒᵖᵒᵖ} (h : i ⟶ j), IsAffineHom (D.map h) :=
    fun h => inferInstanceAs (IsAffineHom (Spec.map (F.map h.unop)))
  have : ∀ i : (OpenNhds x)ᵒᵖᵒᵖ, CompactSpace (D.obj i) :=
    fun i => inferInstanceAs (CompactSpace (Spec (F.obj i.unop)))
  have : ∀ i : (OpenNhds x)ᵒᵖᵒᵖ, QuasiSeparatedSpace (D.obj i) :=
    fun i => inferInstanceAs (QuasiSeparatedSpace (Spec (F.obj i.unop)))
  obtain ⟨i, b, hb, hbf⟩ :=
    Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D t f c hc a hcompat
  let U : X.Opens := i.unop.unop.1
  have hxU : x ∈ U := i.unop.unop.2
  let b' : Spec Γ(X, U) ⟶ Y := b
  have hb' : Spec.map (X.presheaf.germ U x hxU) ≫ b' = a := hb
  have hbf' : b' ≫ f =
      Spec.map (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op) ≫
        X.isoSpec.inv := hbf
  refine ⟨U, hxU, U.toSpecΓ ≫ b', ?_, ?_⟩
  · rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_toSpecΓ]
    exact hb'
  · rw [Category.assoc, hbf']
    change U.toSpecΓ ≫ (Spec.map (X.presheaf.map (homOfLE le_top).op) ≫
      X.isoSpec.inv) = U.ι
    rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top,
      Category.assoc, Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

end AlgebraicGeometry
