/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Surjective global restriction and finite products

Global restriction through the actual inverse-image adjunction is
surjective for a finite product whenever it is surjective for each factor.
The proof uses actual sheaf product projections, preservation of finite
products by inverse image, and preservation of products by sheaf sections.
Lifts of the projected target section assemble by the product universal
property; unit naturality identifies their restriction with the target.

The Lean proof is original.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace SchemeTheory

variable {X Y : TopCat.{u}}

/-- Surjectivity of the actual global restriction map is stable under
finite products of sheaves of types. -/
theorem sheafPullback_globalSections_surjective_pi (f : X ⟶ Y)
    {I : Type u} [Finite I]
    (G : I → CategoryTheory.Sheaf (Opens.grothendieckTopology Y) (Type u))
    (hG : ∀ i : I, Function.Surjective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app (G i)).hom.app
        (op (⊤ : Opens Y)))) :
    Function.Surjective
      (((TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f).unit.app (∏ᶜ G)).hom.app
        (op (⊤ : Opens Y))) := by
  classical
  let JX : GrothendieckTopology (Opens X) := Opens.grothendieckTopology X
  let JY : GrothendieckTopology (Opens Y) := Opens.grothendieckTopology Y
  let L : CategoryTheory.Sheaf JY (Type u) ⥤ CategoryTheory.Sheaf JX (Type u) :=
    (Opens.map f).sheafPullback (Type u) JY JX
  let R : CategoryTheory.Sheaf JX (Type u) ⥤ CategoryTheory.Sheaf JY (Type u) :=
    TopCat.Sheaf.pushforward (Type u) f
  let adj : L ⊣ R := TopCat.Sheaf.pullbackPushforwardAdjunction (Type u) f
  let ΓX : CategoryTheory.Sheaf JX (Type u) ⥤ Type u :=
    (sheafSections JX (Type u)).obj (op (⊤ : Opens X))
  let ΓY : CategoryTheory.Sheaf JY (Type u) ⥤ Type u :=
    (sheafSections JY (Type u)).obj (op (⊤ : Opens Y))
  let P : CategoryTheory.Sheaf JY (Type u) := ∏ᶜ G
  let η (H : CategoryTheory.Sheaf JY (Type u)) : ΓY.obj H ⟶ ΓX.obj (L.obj H) :=
    (adj.unit.app H).hom.app (op (⊤ : Opens Y))
  have hReflects : ReflectsLimits (CategoryTheory.forget (Type u)) :=
    reflectsLimits_of_reflectsIsomorphisms
  have hLan : PreservesFiniteLimits
      ((Opens.map f).op.lan : ((Opens Y)ᵒᵖ ⥤ Type u) ⥤ (Opens X)ᵒᵖ ⥤ Type u) :=
    lan_preservesFiniteLimits_of_flat (E := Type u) (Opens.map f)
  have hL : PreservesFiniteLimits L :=
    Functor.sheafPullbackConstruction.preservesFiniteLimits (Opens.map f) (Type u) JY JX
  have hΓY : PreservesLimit (Discrete.functor G) ΓY :=
    preservesLimit_of_natIso (Discrete.functor G)
      (sheafSectionsNatIsoEvaluation JY (Type u) (X := (⊤ : Opens Y))).symm
  have hΓX : PreservesLimit (Discrete.functor G ⋙ L) ΓX :=
    preservesLimit_of_natIso (Discrete.functor G ⋙ L)
      (sheafSectionsNatIsoEvaluation JX (Type u) (X := (⊤ : Opens X))).symm
  have hLΓ : PreservesLimit (Discrete.functor G) (L ⋙ ΓX) := comp_preservesLimit L ΓX
  let πY (i : I) : ΓY.obj P ⟶ ΓY.obj (G i) := ΓY.map (Pi.π G i)
  let πX (i : I) : ΓX.obj (L.obj P) ⟶ ΓX.obj (L.obj (G i)) :=
    ΓX.map (L.map (Pi.π G i))
  have hPY : IsLimit (Fan.mk (ΓY.obj P) πY) :=
    isLimitOfHasProductOfPreservesLimit ΓY G
  have hPX : IsLimit (Fan.mk (ΓX.obj (L.obj P)) πX) :=
    isLimitOfHasProductOfPreservesLimit (L ⋙ ΓX) G
  change Function.Surjective (η P)
  intro t
  have hη (i : I) : Function.Surjective (η (G i)) := hG i
  choose s hs using fun i : I => hη i (πX i t)
  let points (i : I) : PUnit.{u+1} ⟶ ΓY.obj (G i) := TypeCat.ofHom (fun _ => s i)
  let lift : PUnit.{u+1} ⟶ ΓY.obj P := Fan.IsLimit.lift hPY points
  let w : ΓY.obj P := lift PUnit.unit
  have hw (i : I) : πY i w = s i :=
    congrArg (fun k : PUnit.{u+1} ⟶ ΓY.obj (G i) => k PUnit.unit)
      (Fan.IsLimit.fac hPY points i)
  refine ⟨w, ?_⟩
  let k₁ : PUnit.{u+1} ⟶ ΓX.obj (L.obj P) := TypeCat.ofHom (fun _ => η P w)
  let k₂ : PUnit.{u+1} ⟶ ΓX.obj (L.obj P) := TypeCat.ofHom (fun _ => t)
  have hk : k₁ = k₂ := by
    apply Fan.IsLimit.hom_ext hPX k₁ k₂
    intro i
    ext z
    change πX i (η P w) = πX i t
    have hn : πY i ≫ η (G i) = η P ≫ πX i :=
      congrArg (fun k : P ⟶ R.obj (L.obj (G i)) => k.hom.app (op (⊤ : Opens Y)))
        (adj.unit.naturality (Pi.π G i))
    have hnw : η (G i) (πY i w) = πX i (η P w) :=
      congrArg (fun k : ΓY.obj P ⟶ ΓX.obj (L.obj (G i)) => k w) hn
    exact hnw.symm.trans ((congrArg (η (G i)) (hw i)).trans (hs i))
  exact congrArg (fun k : PUnit.{u+1} ⟶ ΓX.obj (L.obj P) => k PUnit.unit) hk

end SchemeTheory
